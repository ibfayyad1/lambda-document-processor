import json
import boto3
import logging
import os
import tempfile
import base64
import io
import time
import zipfile
import xml.etree.ElementTree as ET
import re
import uuid
import traceback
import fitz  # PyMuPDF for PDF processing
from typing import Dict, Any, List, Optional, Tuple, Set
from pathlib import Path
from decimal import Decimal
from datetime import datetime, timedelta
from dataclasses import dataclass
from collections import defaultdict
import hashlib

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# AWS Configuration
AWS_REGION = os.environ.get('AWS_REGION', 'us-east-1')
S3_BUCKET = os.environ.get('S3_BUCKET')
DYNAMODB_TEXT_TABLE = os.environ.get('EXTRACTED_TEXT_TABLE', 'extracted_text')
DYNAMODB_IMAGES_TABLE = os.environ.get('IMAGES_TABLE', 'images')
MAX_FILE_SIZE = int(os.environ.get('MAX_FILE_SIZE', '104857600'))  # 100MB

# Image AI Processing Configuration
IMAGE_PROCESSOR_LAMBDA_ARN = os.environ.get('IMAGE_PROCESSOR_LAMBDA_ARN')
IMAGE_PROCESSING_QUEUE_URL = os.environ.get('IMAGE_BATCH_QUEUE_URL')
USE_ASYNC_PROCESSING = os.environ.get('USE_ASYNC_PROCESSING', 'true').lower() == 'true'

# AWS Clients
s3_client = boto3.client('s3')
dynamodb = boto3.resource('dynamodb')
lambda_client = boto3.client('lambda')
sqs_client = boto3.client('sqs')
events_client = boto3.client('events')

@dataclass
class ImageInstance:
    """Enhanced image instance with complete positioning and metadata"""
    xref: int
    bbox: Tuple[float, float, float, float]  # x0, y0, x1, y1
    page_number: int
    instance_id: str
    image_hash: str
    width: float
    height: float
    area: float
    position_in_text: int = 0
    text_before: str = ""
    text_after: str = ""
    is_duplicate: bool = False
    original_instance_id: str = None
    extraction_order: int = 0

@dataclass
class TextBlock:
    """Enhanced text block with positioning"""
    text: str
    bbox: Tuple[float, float, float, float]
    font_size: float
    font_name: str
    flags: int
    page_number: int
    block_order: int
    is_heading: bool = False
    heading_level: int = 0

# Initialize DynamoDB tables with better error handling
def initialize_dynamodb_tables():
    """Initialize DynamoDB tables with proper error handling and logging"""
    global text_table, images_table
    
    logger.info(f"Initializing DynamoDB tables...")
    logger.info(f"Region: {AWS_REGION}")
    logger.info(f"Text table name: {DYNAMODB_TEXT_TABLE}")
    logger.info(f"Images table name: {DYNAMODB_IMAGES_TABLE}")
    
    try:
        # Initialize text table
        if DYNAMODB_TEXT_TABLE:
            text_table = dynamodb.Table(DYNAMODB_TEXT_TABLE)
            # Test table access
            text_table.load()
            logger.info(f"Successfully initialized text table: {DYNAMODB_TEXT_TABLE}")
        else:
            logger.error("DYNAMODB_TEXT_TABLE environment variable not set!")
            text_table = None
            
    except Exception as e:
        logger.error(f"Failed to initialize text table: {e}")
        text_table = None
    
    try:
        # Initialize images table
        if DYNAMODB_IMAGES_TABLE:
            images_table = dynamodb.Table(DYNAMODB_IMAGES_TABLE)
            # Test table access
            images_table.load()
            logger.info(f"Successfully initialized images table: {DYNAMODB_IMAGES_TABLE}")
        else:
            logger.error("DYNAMODB_IMAGES_TABLE environment variable not set!")
            images_table = None
            
    except Exception as e:
        logger.error(f"Failed to initialize images table: {e}")
        images_table = None
    
    # Log final status
    if text_table and images_table:
        logger.info("DynamoDB tables initialized successfully")
    elif text_table:
        logger.warning("Only text table initialized - images will be processed but metadata won't be stored")
    elif images_table:
        logger.warning("Only images table initialized - text storage will use fallback methods")
    else:
        logger.error("No DynamoDB tables initialized - using fallback storage methods only")

# Initialize tables
initialize_dynamodb_tables()

def generate_unique_document_id(original_filename: str = None) -> str:
    """Generate truly unique document ID with timestamp and UUID"""
    timestamp = datetime.utcnow()
    microseconds = timestamp.microsecond
    random_suffix = str(uuid.uuid4())[:8]
    
    date_part = timestamp.strftime('%Y%m%d')
    time_part = timestamp.strftime('%H%M%S')
    
    if original_filename:
        base_name = Path(original_filename).stem
        clean_name = re.sub(r'[^\w\-_]', '_', base_name)[:15]
        document_id = f"{clean_name}_{date_part}_{time_part}_{microseconds}_{random_suffix}"
    else:
        document_id = f"doc_{date_part}_{time_part}_{microseconds}_{random_suffix}"
    
    logger.info(f"Generated unique document ID: {document_id}")
    return document_id

class EnhancedDocumentProcessor:
    """Enhanced processor with advanced PDF and DOCX processing with AI integration"""
    
    def __init__(self, document_id: str):
        self.document_id = document_id
        self.placeholders = {}
        self.processed_images = []
        self.image_counter = 1
        self.processing_timestamp = datetime.utcnow().isoformat()
        
        # Advanced PDF tracking
        self.image_instances: List[ImageInstance] = []
        self.text_blocks: List[TextBlock] = []
        self.image_hash_map: Dict[str, str] = {}  # hash -> first_instance_id
        self.duplicate_map: Dict[str, List[str]] = {}  # original_id -> [duplicate_ids]
        self.spatial_index: Dict[int, List] = {}  # page -> sorted elements
        
        # DOCX namespaces
        self.namespaces = {
            'w': 'http://schemas.openxmlformats.org/wordprocessingml/2006/main',
            'pic': 'http://schemas.openxmlformats.org/drawingml/2006/picture',
            'a': 'http://schemas.openxmlformats.org/drawingml/2006/main',
            'r': 'http://schemas.openxmlformats.org/officeDocument/2006/relationships',
            'wp': 'http://schemas.openxmlformats.org/drawingml/2006/wordprocessingDrawing'
        }
        
        # Processing statistics
        self.stats = {
            'total_images_detected': 0,
            'unique_images': 0,
            'duplicate_images': 0,
            'images_extracted': 0,
            'images_uploaded': 0,
            'positioning_accuracy': 0.0,
            'text_blocks_processed': 0,
            'pages_processed': 0,
            'processing_time': 0.0
        }
        
    def process_document(self, file_path: str) -> Dict[str, Any]:
        """Main processing method with formatting preservation and AI trigger - Supports PDF and DOCX"""
        start_time = time.time()
        
        try:
            logger.info(f"Starting enhanced processing for {self.document_id}")
            
            # Validate file
            if not os.path.exists(file_path):
                raise Exception(f"File not found: {file_path}")
            
            file_size = os.path.getsize(file_path)
            if file_size > MAX_FILE_SIZE:
                raise Exception(f"File too large: {file_size} bytes")
            
            # Process based on file type
            file_extension = Path(file_path).suffix.lower()
            
            if file_extension == '.pdf':
                result = self.process_pdf_with_advanced_detection(file_path)
                extraction_method = 'advanced_pdf_with_spatial_positioning'
            elif file_extension == '.docx':
                result = self._process_docx_with_formatting(file_path)
                extraction_method = 'enhanced_docx_with_formatting'
            else:
                raise Exception(f"Unsupported file type: {file_extension}")
            
            processing_time = time.time() - start_time
            
            # Validate extracted text
            if not result.get('formatted_text') or len(result['formatted_text'].strip()) == 0:
                logger.error("No text was extracted from the document!")
                raise Exception("Text extraction failed - no content found")
            
            logger.info(f"Text extracted successfully: {len(result['formatted_text'])} characters")
            
            # Store results with error handling
            try:
                # Save text files to S3 as primary storage method
                text_files_saved = self._save_text_files_to_s3(result['formatted_text'])
                if text_files_saved:
                    logger.info("Text files successfully saved to S3")
                else:
                    logger.error("Failed to save text files to S3")
                    
                # Optional: Also save to DynamoDB if needed
                if text_table:
                    try:
                        self._store_formatted_text(result['formatted_text'])
                        logger.info("Text also saved to DynamoDB as backup")
                    except Exception as db_error:
                        logger.warning(f"DynamoDB backup failed: {db_error}")
                        
            except Exception as storage_error:
                logger.error(f"Text file storage failed: {storage_error}")
                # Save to local file as last resort
                self._save_text_to_file(result['formatted_text'])

            # TRIGGER IMAGE AI PROCESSING
            ai_trigger_result = self._trigger_image_ai_processing(
                result['formatted_text'], 
                len(self.processed_images)
            )
            
            processing_time = time.time() - start_time
            
            logger.info(f"Enhanced processing complete in {processing_time:.2f}s")
            logger.info(f"Images processed: {len(self.processed_images)}")
            logger.info(f"AI processing trigger: {ai_trigger_result}")
            
            # Create S3 file paths for response
            timestamp_prefix = datetime.utcnow().strftime('%Y/%m/%d')
            base_path = f"document_extractions/{timestamp_prefix}/{self.document_id}"
            
            file_locations = {
                'formatted_text': f"s3://{S3_BUCKET}/{base_path}/formatted_text.md",
                'plain_text': f"s3://{S3_BUCKET}/{base_path}/plain_text.txt",
                'metadata': f"s3://{S3_BUCKET}/{base_path}/metadata.json",
                'summary': f"s3://{S3_BUCKET}/{base_path}/extraction_summary.txt"
            }

            return {
                'success': True,
                'document_id': self.document_id,
                'processing_timestamp': self.processing_timestamp,
                'extracted_text': result['formatted_text'],
                'plain_text': result.get('plain_text', ''),
                'images_count': len(self.processed_images),
                'placeholders': self.placeholders,
                'processing_time': processing_time,
                'extraction_method': extraction_method,
                'pages_processed': result.get('pages_processed', 1),
                'images_detected': result.get('total_image_references', 0),
                'unique_image_files': result.get('unique_image_files', 0),
                'duplicate_image_instances': result.get('duplicate_image_instances', 0),
                'images_extracted': result.get('images_extracted', 0),
                'images_uploaded': result.get('images_uploaded', 0),
                'positioning_accuracy': result.get('positioning_accuracy', 0.0),
                'text_blocks_processed': result.get('text_blocks_processed', 0),
                'tables_detected': result.get('tables_count', 0),
                'headings_detected': result.get('headings_count', 0),
                'formatting_preserved': True,
                'files_saved_to_s3': True,
                'output_files': file_locations,
                's3_base_path': f"s3://{S3_BUCKET}/{base_path}/",
                'ai_processing': ai_trigger_result,
                'processing_stats': result.get('processing_stats', self.stats),
                'error_count': 0,
                'warning_count': 0,
                'errors': [],
                'warnings': []
            }
            
        except Exception as e:
            processing_time = time.time() - start_time
            logger.error(f"Enhanced processing failed: {e}")
            
            return {
                'success': False,
                'document_id': self.document_id,
                'processing_timestamp': self.processing_timestamp,
                'extracted_text': "",
                'plain_text': "",
                'images_count': 0,
                'placeholders': {},
                'processing_time': processing_time,
                'extraction_method': 'failed',
                'pages_processed': 0,
                'images_detected': 0,
                'images_extracted': 0,
                'images_uploaded': 0,
                'formatting_preserved': False,
                'ai_processing': {'triggered': False, 'reason': 'processing_failed'},
                'error_count': 1,
                'warning_count': 0,
                'errors': [str(e)],
                'warnings': [],
                'traceback': traceback.format_exc()
            }
    
    def process_pdf_with_advanced_detection(self, file_path: str) -> Dict[str, Any]:
        """Main PDF processing method with advanced image detection and positioning"""
        start_time = time.time()
        
        try:
            logger.info(f"Starting advanced PDF processing for {self.document_id}")
            
            # Open PDF with advanced options
            pdf_doc = fitz.open(file_path)
            logger.info(f"PDF opened: {len(pdf_doc)} pages")
            
            # Phase 1: Comprehensive Analysis
            self._perform_comprehensive_analysis(pdf_doc)
            
            # Phase 2: Advanced Image Detection
            self._detect_all_images_advanced(pdf_doc)
            
            # Phase 3: Text Extraction with Positioning
            self._extract_text_with_positioning(pdf_doc)
            
            # Phase 4: Spatial Integration
            self._integrate_images_and_text_spatially(pdf_doc)
            
            # Phase 5: Generate Final Document
            formatted_text = self._generate_final_document()
            
            # Phase 6: Process and Upload Images
            self._process_and_upload_all_images(pdf_doc)
            
            # Phase 7: Finalize Text with Image Links
            final_text = self._finalize_text_with_images(formatted_text)
            
            pdf_doc.close()
            
            processing_time = time.time() - start_time
            self.stats['processing_time'] = processing_time
            
            logger.info(f"Advanced PDF processing complete:")
            logger.info(f"  - Processing time: {processing_time:.2f}s")
            logger.info(f"  - Total images detected: {self.stats['total_images_detected']}")
            logger.info(f"  - Unique images: {self.stats['unique_images']}")
            logger.info(f"  - Duplicate instances: {self.stats['duplicate_images']}")
            logger.info(f"  - Images uploaded: {self.stats['images_uploaded']}")
            logger.info(f"  - Text blocks processed: {self.stats['text_blocks_processed']}")
            
            # Generate plain text
            plain_text = self._strip_formatting_markers(final_text)
            
            return {
                'formatted_text': final_text,
                'plain_text': plain_text,
                'method': 'advanced_pdf_with_spatial_positioning',
                'pages_processed': self.stats['pages_processed'],
                'total_image_references': self.stats['total_images_detected'],
                'unique_image_files': self.stats['unique_images'],
                'duplicate_image_instances': self.stats['duplicate_images'],
                'images_extracted': self.stats['images_extracted'],
                'images_uploaded': self.stats['images_uploaded'],
                'text_blocks_processed': self.stats['text_blocks_processed'],
                'positioning_accuracy': self.stats['positioning_accuracy'],
                'processing_stats': self.stats,
                'tables_count': 0,
                'headings_count': len([tb for tb in self.text_blocks if tb.is_heading])
            }
            
        except Exception as e:
            processing_time = time.time() - start_time
            logger.error(f"Advanced PDF processing failed: {e}")
            logger.error(traceback.format_exc())
            
            return self._fallback_pdf_extraction(file_path)
    
    def _perform_comprehensive_analysis(self, pdf_doc: fitz.Document) -> None:
        """Phase 1: Perform comprehensive document analysis"""
        logger.info("Phase 1: Comprehensive document analysis")
        
        self.stats['pages_processed'] = len(pdf_doc)
        
        # Analyze document structure
        for page_num in range(len(pdf_doc)):
            page = pdf_doc.load_page(page_num)
            
            # Get page dimensions for spatial calculations
            page_rect = page.rect
            logger.info(f"Page {page_num + 1} dimensions: {page_rect.width} x {page_rect.height}")
            
            # Initialize spatial index for this page
            self.spatial_index[page_num] = []
    
    def _detect_all_images_advanced(self, pdf_doc: fitz.Document) -> None:
        """Phase 2: Advanced image detection that finds ALL images including duplicates"""
        logger.info("Phase 2: Advanced image detection and analysis")
        
        extraction_order = 0
        
        for page_num in range(len(pdf_doc)):
            page = pdf_doc.load_page(page_num)
            
            logger.info(f"Analyzing images on page {page_num + 1}")
            
            # Method 1: Get basic image list
            basic_image_list = page.get_images()
            logger.info(f"  - Basic image detection found: {len(basic_image_list)} images")
            
            # Method 2: Advanced image detection using page drawings
            drawings = page.get_drawings()
            logger.info(f"  - Drawing analysis found: {len(drawings)} vector elements")
            
            # Method 3: Text extraction with image markers
            text_dict = page.get_text("dict")
            embedded_images = self._find_embedded_images_in_text_dict(text_dict, page_num)
            logger.info(f"  - Text analysis found: {len(embedded_images)} embedded images")
            
            # Method 4: Advanced spatial analysis
            spatial_images = self._detect_images_spatially(page, page_num)
            logger.info(f"  - Spatial analysis found: {len(spatial_images)} positioned images")
            
            # Process basic image list with advanced analysis
            for img_index, img_data in enumerate(basic_image_list):
                try:
                    xref = img_data[0]
                    
                    # Get image properties
                    base_image = pdf_doc.extract_image(xref)
                    if not base_image:
                        logger.warning(f"Could not extract base image for xref {xref}")
                        continue
                    
                    # Calculate image hash for duplicate detection
                    image_bytes = base_image["image"]
                    image_hash = hashlib.md5(image_bytes).hexdigest()
                    
                    # Find all instances of this image on the current page
                    instances = self._find_all_image_instances_on_page(
                        page, xref, image_hash, page_num, extraction_order
                    )
                    
                    # Add to our comprehensive list
                    for instance in instances:
                        self.image_instances.append(instance)
                        extraction_order += 1
                        
                        logger.info(f"  - Detected image instance {instance.instance_id} at {instance.bbox}")
                    
                except Exception as e:
                    logger.error(f"Error processing image {img_index} on page {page_num + 1}: {e}")
                    continue
            
            # Process spatial images that might have been missed
            for spatial_img in spatial_images:
                if not any(self._rectangles_overlap(spatial_img['bbox'], inst.bbox) 
                          for inst in self.image_instances if inst.page_number == page_num + 1):
                    # This is a new image not detected by basic method
                    try:
                        instance = self._create_spatial_image_instance(
                            spatial_img, page_num, extraction_order
                        )
                        if instance:
                            self.image_instances.append(instance)
                            extraction_order += 1
                            logger.info(f"  - Added spatial image {instance.instance_id}")
                    except Exception as e:
                        logger.error(f"Error processing spatial image: {e}")
        
        # Post-process: Identify duplicates across all pages
        self._identify_duplicates_advanced()
        
        # Update statistics
        self.stats['total_images_detected'] = len(self.image_instances)
        self.stats['unique_images'] = len(set(inst.image_hash for inst in self.image_instances))
        self.stats['duplicate_images'] = self.stats['total_images_detected'] - self.stats['unique_images']
        
        logger.info(f"Advanced image detection complete:")
        logger.info(f"  - Total instances: {self.stats['total_images_detected']}")
        logger.info(f"  - Unique images: {self.stats['unique_images']}")
        logger.info(f"  - Duplicates: {self.stats['duplicate_images']}")
    
    def _find_all_image_instances_on_page(self, page: fitz.Page, xref: int, 
                                        image_hash: str, page_num: int, 
                                        base_extraction_order: int) -> List[ImageInstance]:
        """Find all instances of a specific image on a page (including duplicates)"""
        instances = []
        
        try:
            # Get all image rectangles for this xref
            image_rects = []
            
            # Try to get image rectangles
            try:
                if hasattr(page, 'get_image_rects'):
                    rects = page.get_image_rects(xref)
                    image_rects.extend(rects)
                else:
                    # Fallback: estimate positions
                    image_rects = self._estimate_image_positions(page, xref)
            except Exception as e:
                logger.warning(f"Could not get image rectangles: {e}")
                image_rects = self._estimate_image_positions(page, xref)
            
            # If no rects found, create default position
            if not image_rects:
                page_rect = page.rect
                default_rect = fitz.Rect(
                    page_rect.width * 0.1,
                    page_rect.height * 0.1,
                    page_rect.width * 0.5,
                    page_rect.height * 0.3
                )
                image_rects = [default_rect]
                logger.info(f"Using estimated position for image xref {xref}")
            
            # Create instances for each rectangle
            for rect_index, rect in enumerate(image_rects):
                instance_id = f"img_{page_num + 1}_{xref}_{rect_index}_{int(time.time() * 1000000) + rect_index}"
                
                instance = ImageInstance(
                    xref=xref,
                    bbox=(rect.x0, rect.y0, rect.x1, rect.y1),
                    page_number=page_num + 1,
                    instance_id=instance_id,
                    image_hash=image_hash,
                    width=rect.width,
                    height=rect.height,
                    area=rect.width * rect.height,
                    extraction_order=base_extraction_order + rect_index
                )
                
                instances.append(instance)
                logger.info(f"Created instance {instance_id} at {instance.bbox}")
        
        except Exception as e:
            logger.error(f"Error finding image instances for xref {xref}: {e}")
            
            # Create fallback instance
            page_rect = page.rect
            fallback_rect = (
                page_rect.width * 0.1,
                page_rect.height * 0.1,
                page_rect.width * 0.5,
                page_rect.height * 0.3
            )
            
            instance_id = f"img_{page_num + 1}_{xref}_fallback_{int(time.time() * 1000000)}"
            
            instance = ImageInstance(
                xref=xref,
                bbox=fallback_rect,
                page_number=page_num + 1,
                instance_id=instance_id,
                image_hash=image_hash,
                width=fallback_rect[2] - fallback_rect[0],
                height=fallback_rect[3] - fallback_rect[1],
                area=(fallback_rect[2] - fallback_rect[0]) * (fallback_rect[3] - fallback_rect[1]),
                extraction_order=base_extraction_order
            )
            
            instances.append(instance)
        
        return instances
    
    def _estimate_image_positions(self, page: fitz.Page, xref: int) -> List[fitz.Rect]:
        """Estimate image positions when direct position detection fails"""
        positions = []
        
        try:
            # Get text blocks to help estimate positions
            text_blocks = page.get_text("dict")["blocks"]
            page_rect = page.rect
            
            # Strategy: Place images between text blocks or in empty areas
            text_areas = []
            for block in text_blocks:
                if "bbox" in block:
                    text_areas.append(fitz.Rect(block["bbox"]))
            
            # If we have text, try to place images in gaps
            if text_areas:
                # Sort text areas by position
                text_areas.sort(key=lambda r: (r.y0, r.x0))
                
                # Find gaps between text areas
                for i in range(len(text_areas)):
                    if i == 0:
                        # Before first text block
                        if text_areas[0].y0 > page_rect.height * 0.1:
                            img_rect = fitz.Rect(
                                page_rect.x0 + 20,
                                page_rect.y0 + 20,
                                page_rect.x1 - 20,
                                text_areas[0].y0 - 10
                            )
                            if img_rect.width > 50 and img_rect.height > 50:
                                positions.append(img_rect)
                    
                    if i < len(text_areas) - 1:
                        # Between text blocks
                        current_block = text_areas[i]
                        next_block = text_areas[i + 1]
                        
                        gap_height = next_block.y0 - current_block.y1
                        if gap_height > 60:  # Enough space for an image
                            img_rect = fitz.Rect(
                                page_rect.x0 + 20,
                                current_block.y1 + 10,
                                page_rect.x1 - 20,
                                current_block.y1 + min(gap_height - 10, 200)
                            )
                            positions.append(img_rect)
            
            # If no good positions found, use default grid
            if not positions:
                positions.append(fitz.Rect(
                    page_rect.width * 0.1,
                    page_rect.height * 0.2,
                    page_rect.width * 0.9,
                    page_rect.height * 0.5
                ))
        
        except Exception as e:
            logger.error(f"Error estimating image positions: {e}")
            
            # Ultimate fallback
            page_rect = page.rect
            positions.append(fitz.Rect(
                page_rect.width * 0.1,
                page_rect.height * 0.1,
                page_rect.width * 0.5,
                page_rect.height * 0.3
            ))
        
        return positions
    
    def _find_embedded_images_in_text_dict(self, text_dict: Dict, page_num: int) -> List[Dict]:
        """Find images embedded in text structure"""
        embedded_images = []
        
        try:
            for block in text_dict.get("blocks", []):
                if "lines" in block:
                    for line in block["lines"]:
                        for span in line["spans"]:
                            # Look for image markers or special characters
                            text = span.get("text", "")
                            if any(char in text for char in ["□", "▢", "⬜", "◊"]):
                                # Potential image placeholder
                                bbox = span.get("bbox")
                                if bbox:
                                    embedded_images.append({
                                        'bbox': bbox,
                                        'type': 'placeholder',
                                        'page': page_num,
                                        'text': text
                                    })
        
        except Exception as e:
            logger.error(f"Error finding embedded images: {e}")
        
        return embedded_images
    
    def _detect_images_spatially(self, page: fitz.Page, page_num: int) -> List[Dict]:
        """Detect images using spatial analysis of page elements"""
        spatial_images = []
        
        try:
            # Get all drawings and analyze for image-like patterns
            drawings = page.get_drawings()
            
            for drawing in drawings:
                # Analyze drawing properties
                rect = drawing.get("rect")
                if rect and rect.width > 20 and rect.height > 20:
                    # This could be an image boundary
                    spatial_images.append({
                        'bbox': (rect.x0, rect.y0, rect.x1, rect.y1),
                        'type': 'spatial_drawing',
                        'page': page_num,
                        'width': rect.width,
                        'height': rect.height,
                        'area': rect.width * rect.height
                    })
        
        except Exception as e:
            logger.error(f"Error in spatial image detection: {e}")
        
        return spatial_images
    
    def _create_spatial_image_instance(self, spatial_img: Dict, page_num: int, 
                                     extraction_order: int) -> Optional[ImageInstance]:
        """Create an image instance from spatial detection"""
        try:
            bbox = spatial_img['bbox']
            instance_id = f"spatial_{page_num + 1}_{extraction_order}_{int(time.time() * 1000000)}"
            
            # Create a synthetic hash for spatial images
            spatial_hash = hashlib.md5(
                f"{bbox}_{spatial_img['type']}_{page_num}".encode()
            ).hexdigest()
            
            instance = ImageInstance(
                xref=-1,  # No xref for spatial images
                bbox=bbox,
                page_number=page_num + 1,
                instance_id=instance_id,
                image_hash=spatial_hash,
                width=spatial_img['width'],
                height=spatial_img['height'],
                area=spatial_img['area'],
                extraction_order=extraction_order
            )
            
            return instance
        
        except Exception as e:
            logger.error(f"Error creating spatial image instance: {e}")
            return None
    
    def _rectangles_overlap(self, rect1: Tuple[float, float, float, float], 
                           rect2: Tuple[float, float, float, float]) -> bool:
        """Check if two rectangles overlap"""
        return not (rect1[2] < rect2[0] or rect2[2] < rect1[0] or 
                   rect1[3] < rect2[1] or rect2[3] < rect1[1])
    
    def _identify_duplicates_advanced(self) -> None:
        """Advanced duplicate identification across all pages"""
        logger.info("Identifying duplicate images across document")
        
        # Group by hash
        hash_groups = defaultdict(list)
        for instance in self.image_instances:
            hash_groups[instance.image_hash].append(instance)
        
        # Process each hash group
        for image_hash, instances in hash_groups.items():
            if len(instances) > 1:
                # Sort by extraction order to determine original
                instances.sort(key=lambda x: x.extraction_order)
                original = instances[0]
                
                # Mark duplicates
                for duplicate in instances[1:]:
                    duplicate.is_duplicate = True
                    duplicate.original_instance_id = original.instance_id
                
                # Track duplicates
                self.duplicate_map[original.instance_id] = [d.instance_id for d in instances[1:]]
                
                logger.info(f"Hash {image_hash[:8]}: 1 original + {len(instances) - 1} duplicates")
        
        # Update hash map
        for instance in self.image_instances:
            if not instance.is_duplicate:
                self.image_hash_map[instance.image_hash] = instance.instance_id
    
    def _extract_text_with_positioning(self, pdf_doc: fitz.Document) -> None:
        """Phase 3: Extract text with detailed positioning information"""
        logger.info("Phase 3: Text extraction with positioning")
        
        block_order = 0
        
        for page_num in range(len(pdf_doc)):
            page = pdf_doc.load_page(page_num)
            
            # Get text with detailed formatting
            text_dict = page.get_text("dict")
            
            for block in text_dict.get("blocks", []):
                if "lines" not in block:
                    continue
                
                block_text_parts = []
                block_bbox = block.get("bbox")
                
                if not block_bbox:
                    continue
                
                # Process lines in block
                for line in block["lines"]:
                    line_text_parts = []
                    
                    for span in line["spans"]:
                        text = span.get("text", "").strip()
                        if text:
                            font_size = span.get("size", 12)
                            flags = span.get("flags", 0)
                            
                            # Apply formatting
                            if flags & 16:  # Bold
                                text = f"**{text}**"
                            if flags & 2:   # Italic
                                text = f"*{text}*"
                            
                            line_text_parts.append(text)
                    
                    if line_text_parts:
                        block_text_parts.append(" ".join(line_text_parts))
                
                if block_text_parts:
                    block_text = "\n".join(block_text_parts)
                    
                    # Determine if this is a heading
                    avg_font_size = self._calculate_average_font_size_in_block(block)
                    is_heading = avg_font_size > 14
                    heading_level = min(6, max(1, int((avg_font_size - 12) / 2) + 1)) if is_heading else 0
                    
                    text_block = TextBlock(
                        text=block_text,
                        bbox=block_bbox,
                        font_size=avg_font_size,
                        font_name="",
                        flags=0,
                        page_number=page_num + 1,
                        block_order=block_order,
                        is_heading=is_heading,
                        heading_level=heading_level
                    )
                    
                    self.text_blocks.append(text_block)
                    block_order += 1
        
        self.stats['text_blocks_processed'] = len(self.text_blocks)
        logger.info(f"Extracted {len(self.text_blocks)} text blocks")
    
    def _calculate_average_font_size_in_block(self, block: Dict) -> float:
        """Calculate average font size in a text block"""
        sizes = []
        
        for line in block.get("lines", []):
            for span in line.get("spans", []):
                size = span.get("size")
                if size:
                    sizes.append(size)
        
        return sum(sizes) / len(sizes) if sizes else 12.0
    
    def _integrate_images_and_text_spatially(self, pdf_doc: fitz.Document) -> None:
        """Phase 4: Spatially integrate images and text for proper positioning"""
        logger.info("Phase 4: Spatial integration of images and text")
        
        # Group elements by page
        page_elements = defaultdict(list)
        
        # Add text blocks
        for text_block in self.text_blocks:
            page_elements[text_block.page_number].append({
                'type': 'text',
                'element': text_block,
                'bbox': text_block.bbox,
                'y_center': (text_block.bbox[1] + text_block.bbox[3]) / 2
            })
        
        # Add image instances
        for image_instance in self.image_instances:
            page_elements[image_instance.page_number].append({
                'type': 'image',
                'element': image_instance,
                'bbox': image_instance.bbox,
                'y_center': (image_instance.bbox[1] + image_instance.bbox[3]) / 2
            })
        
        # Sort elements by position on each page
        for page_num, elements in page_elements.items():
            # Sort by Y position (top to bottom), then X position (left to right)
            elements.sort(key=lambda e: (e['y_center'], e['bbox'][0]))
            self.spatial_index[page_num] = elements
            
            # Calculate position in text flow for images
            for i, element in enumerate(elements):
                if element['type'] == 'image':
                    image_instance = element['element']
                    
                    # Find surrounding text
                    text_before = ""
                    text_after = ""
                    
                    # Get text before
                    for j in range(i - 1, -1, -1):
                        if elements[j]['type'] == 'text':
                            text_before = elements[j]['element'].text[-100:]
                            break
                    
                    # Get text after
                    for j in range(i + 1, len(elements)):
                        if elements[j]['type'] == 'text':
                            text_after = elements[j]['element'].text[:100]
                            break
                    
                    image_instance.text_before = text_before
                    image_instance.text_after = text_after
                    image_instance.position_in_text = i
            
            logger.info(f"Page {page_num}: Integrated {len(elements)} elements")
        
        # Calculate positioning accuracy
        positioned_correctly = sum(1 for inst in self.image_instances 
                                 if inst.text_before or inst.text_after)
        total_images = len(self.image_instances)
        
        if total_images > 0:
            self.stats['positioning_accuracy'] = positioned_correctly / total_images
        
        logger.info(f"Positioning accuracy: {self.stats['positioning_accuracy']:.2%}")
    
    def _generate_final_document(self) -> str:
        """Phase 5: Generate final document with properly positioned placeholders"""
        logger.info("Phase 5: Generating final document")
        
        document_parts = []
        
        for page_num in sorted(self.spatial_index.keys()):
            elements = self.spatial_index[page_num]
            
            if not elements:
                continue
            
            page_parts = [f"## Page {page_num}\n"]
            
            for element in elements:
                if element['type'] == 'text':
                    text_block = element['element']
                    
                    # Apply heading formatting
                    if text_block.is_heading:
                        heading_prefix = "#" * (text_block.heading_level + 2)
                        formatted_text = f"{heading_prefix} {text_block.text}\n"
                    else:
                        formatted_text = f"{text_block.text}\n"
                    
                    page_parts.append(formatted_text)
                
                elif element['type'] == 'image':
                    image_instance = element['element']
                    
                    # Create placeholder marker
                    placeholder_marker = f"__IMAGE_PLACEHOLDER_{image_instance.instance_id}__"
                    
                    # Add context information
                    context_info = []
                    if image_instance.text_before:
                        context_info.append(f"After: ...{image_instance.text_before[-50:]}")
                    if image_instance.text_after:
                        context_info.append(f"Before: ...{image_instance.text_after[:50]}")
                    
                    context_text = " | ".join(context_info) if context_info else "Standalone image"
                    
                    # Format image placeholder
                    image_text = f"\n{placeholder_marker}\n*[Page {page_num}, Position {image_instance.position_in_text}]*\n"
                    if image_instance.is_duplicate:
                        image_text += f"*[Duplicate of {image_instance.original_instance_id}]*\n"
                    image_text += f"*[Context: {context_text}]*\n\n"
                    
                    page_parts.append(image_text)
            
            document_parts.append("\n".join(page_parts))
        
        return "\n\n".join(document_parts)
    
    def _process_and_upload_all_images(self, pdf_doc: fitz.Document) -> None:
        """Phase 6: Process and upload all detected images"""
        logger.info("Phase 6: Processing and uploading images")
        
        uploaded_count = 0
        processed_count = 0
        
        for image_instance in self.image_instances:
            try:
                processed_count += 1
                
                # Skip spatial images without xref for now
                if image_instance.xref < 0:
                    logger.info(f"Skipping spatial image {image_instance.instance_id} (no xref)")
                    continue
                
                # Extract image data
                try:
                    base_image = pdf_doc.extract_image(image_instance.xref)
                    if not base_image:
                        logger.warning(f"Could not extract image data for {image_instance.instance_id}")
                        continue
                    
                    image_bytes = base_image["image"]
                    image_ext = base_image["ext"]
                    
                except Exception as e:
                    logger.error(f"Failed to extract image data for {image_instance.instance_id}: {e}")
                    continue
                
                # Skip tiny images
                if len(image_bytes) < 100:
                    logger.warning(f"Image {image_instance.instance_id} too small ({len(image_bytes)} bytes)")
                    continue
                
                # For duplicates, reference the original upload
                if image_instance.is_duplicate:
                    original_id = image_instance.original_instance_id
                    original_s3_key = self.placeholders.get(f"IMG_{original_id}")
                    
                    if original_s3_key:
                        # Create reference to original
                        self.placeholders[f"IMG_{image_instance.instance_id}"] = original_s3_key
                        
                        # Store metadata for duplicate
                        duplicate_info = {
                            'placeholder': f"IMG_{image_instance.instance_id}",
                            's3_key': original_s3_key,
                            's3_filename': f"IMG_{image_instance.instance_id}.{image_ext}",
                            'original_filename': f"page_{image_instance.page_number}_img_{image_instance.xref}.{image_ext}",
                            'image_number': self.image_counter,
                            'instance_id': image_instance.instance_id,
                            'is_duplicate': True,
                            'original_instance_id': original_id,
                            'page_number': image_instance.page_number,
                            'bbox': image_instance.bbox,
                            'size_bytes': len(image_bytes),
                            'uploaded': False,
                            'upload_timestamp': datetime.utcnow().isoformat(),
                            'source_type': 'pdf_advanced'
                        }
                        
                        self.processed_images.append(duplicate_info)
                        self.image_counter += 1
                        
                        logger.info(f"Referenced duplicate {image_instance.instance_id} → {original_s3_key}")
                        continue
                
                # Upload new/original image
                placeholder_name = f"IMG_{image_instance.instance_id}"
                s3_key = self._upload_pdf_image_to_s3_advanced(
                    image_bytes, placeholder_name, image_instance, image_ext
                )
                
                if s3_key:
                    # Store image info
                    image_info = {
                        'placeholder': placeholder_name,
                        's3_key': s3_key,
                        's3_filename': f"{placeholder_name}.{image_ext}",
                        'original_filename': f"page_{image_instance.page_number}_img_{image_instance.xref}.{image_ext}",
                        'image_number': self.image_counter,
                        'instance_id': image_instance.instance_id,
                        'is_duplicate': False,
                        'page_number': image_instance.page_number,
                        'bbox': image_instance.bbox,
                        'width': image_instance.width,
                        'height': image_instance.height,
                        'area': image_instance.area,
                        'image_hash': image_instance.image_hash,
                        'size_bytes': len(image_bytes),
                        'uploaded': True,
                        'upload_timestamp': datetime.utcnow().isoformat(),
                        'source_type': 'pdf_advanced'
                    }
                    
                    self.processed_images.append(image_info)
                    self.placeholders[placeholder_name] = s3_key
                    
                    # Store in DynamoDB (if available)
                    self._store_image_metadata_advanced(image_info)
                    
                    uploaded_count += 1
                    self.image_counter += 1
                    
                    logger.info(f"Uploaded {placeholder_name}: {len(image_bytes)} bytes → {s3_key}")
                else:
                    logger.error(f"Failed to upload {image_instance.instance_id}")
            
            except Exception as e:
                logger.error(f"Error processing image {image_instance.instance_id}: {e}")
                continue
        
        self.stats['images_extracted'] = processed_count
        self.stats['images_uploaded'] = uploaded_count
        
        logger.info(f"Image processing complete: {processed_count} processed, {uploaded_count} uploaded")
    
    def _upload_pdf_image_to_s3_advanced(self, image_bytes: bytes, placeholder_name: str,
                                       image_instance: ImageInstance, image_ext: str) -> Optional[str]:
        """Advanced S3 upload with comprehensive metadata"""
        if not S3_BUCKET:
            logger.error("S3_BUCKET not configured")
            return None
        
        try:
            timestamp_prefix = datetime.utcnow().strftime('%Y/%m/%d/%H')
            s3_key = f"extracted_images_advanced/{timestamp_prefix}/{self.document_id}/{placeholder_name}.{image_ext}"
            
            s3_client.put_object(
                Bucket=S3_BUCKET,
                Key=s3_key,
                Body=image_bytes,
                ContentType=f'image/{image_ext}',
                Metadata={
                    'document_id': self.document_id,
                    'placeholder_name': placeholder_name,
                    'instance_id': image_instance.instance_id,
                    'source_type': 'pdf_advanced',
                    'page_number': str(image_instance.page_number),
                    'xref': str(image_instance.xref),
                    'bbox': f"{image_instance.bbox[0]},{image_instance.bbox[1]},{image_instance.bbox[2]},{image_instance.bbox[3]}",
                    'width': str(image_instance.width),
                    'height': str(image_instance.height),
                    'area': str(image_instance.area),
                    'image_hash': image_instance.image_hash,
                    'is_duplicate': str(image_instance.is_duplicate),
                    'extraction_order': str(image_instance.extraction_order),
                    'upload_timestamp': datetime.utcnow().isoformat(),
                    'processing_timestamp': self.processing_timestamp
                }
            )
            
            logger.info(f"Advanced S3 Upload: {placeholder_name} → s3://{S3_BUCKET}/{s3_key}")
            return s3_key
            
        except Exception as e:
            logger.error(f"Advanced S3 upload failed for {placeholder_name}: {e}")
            return None
    
    def _store_image_metadata_advanced(self, image_info: Dict[str, Any]) -> None:
        """Store advanced image metadata"""
        if not images_table:
            logger.warning("Images table not available")
            return
        
        try:
            ttl = datetime.utcnow() + timedelta(days=30)
            image_id = f"{self.document_id}_{image_info['instance_id']}_{int(time.time() * 1000)}"
            
            item = {
                'document_id': self.document_id,
                'image_id': image_id,
                'image_number': image_info['image_number'],
                'instance_id': image_info['instance_id'],
                'placeholder': image_info['placeholder'],
                's3_bucket': S3_BUCKET,
                's3_key': image_info['s3_key'],
                's3_filename': image_info['s3_filename'],
                'original_filename': image_info['original_filename'],
                'size_bytes': image_info['size_bytes'],
                'page_number': image_info['page_number'],
                'bbox': image_info.get('bbox', (0, 0, 0, 0)),
                'width': image_info.get('width', 0),
                'height': image_info.get('height', 0),
                'area': image_info.get('area', 0),
                'image_hash': image_info.get('image_hash', ''),
                'is_duplicate': image_info.get('is_duplicate', False),
                'source_type': 'pdf_advanced',
                'extraction_method': 'advanced_pdf_with_spatial_positioning',
                'processing_timestamp': self.processing_timestamp,
                'upload_timestamp': image_info['upload_timestamp'],
                'ai_processed': False,
                'ttl': int(ttl.timestamp())
            }
            
            images_table.put_item(Item=item)
            logger.info(f"DynamoDB: Stored advanced metadata for {image_info['placeholder']}")
            
        except Exception as e:
            logger.error(f"DynamoDB storage failed for {image_info['placeholder']}: {e}")
    
    def _finalize_text_with_images(self, formatted_text: str) -> str:
        """Phase 7: Finalize text by replacing placeholders with proper image references"""
        logger.info("Phase 7: Finalizing text with image references")
        
        current_text = formatted_text
        
        for image_instance in self.image_instances:
            placeholder_marker = f"__IMAGE_PLACEHOLDER_{image_instance.instance_id}__"
            
            if placeholder_marker in current_text:
                placeholder_name = f"IMG_{image_instance.instance_id}"
                s3_key = self.placeholders.get(placeholder_name)
                
                if s3_key:
                    # Create rich image reference
                    image_ref = f"\n![{placeholder_name}](s3://{S3_BUCKET}/{s3_key})\n"
                    
                    # Add metadata
                    metadata_parts = [
                        f"*Advanced PDF Image {image_instance.instance_id}: Page {image_instance.page_number}*",
                        f"*Size: {int(image_instance.width)} × {int(image_instance.height)} pixels*",
                        f"*Position: {image_instance.bbox[0]:.1f}, {image_instance.bbox[1]:.1f}*"
                    ]
                    
                    if image_instance.is_duplicate:
                        metadata_parts.append(f"*Duplicate of {image_instance.original_instance_id}*")
                    
                    if image_instance.text_before or image_instance.text_after:
                        context = []
                        if image_instance.text_before:
                            context.append(f"after '{image_instance.text_before[-20:]}...'")
                        if image_instance.text_after:
                            context.append(f"before '...{image_instance.text_after[:20]}'")
                        metadata_parts.append(f"*Context: {' and '.join(context)}*")
                    
                    full_image_ref = image_ref + "\n".join(metadata_parts) + "\n"
                    
                    current_text = current_text.replace(placeholder_marker, full_image_ref)
                    logger.info(f"Finalized image reference for {image_instance.instance_id}")
                else:
                    # Remove placeholder if no S3 key
                    current_text = current_text.replace(placeholder_marker, 
                        f"\n*[Image {image_instance.instance_id} - Upload failed]*\n")
        
        # Clean up any remaining placeholders
        current_text = re.sub(r'__IMAGE_PLACEHOLDER_[^_]+__', 
                            '\n*[Image processing failed]*\n', current_text)
        
        # Clean up extra whitespace
        current_text = re.sub(r'\n\s*\n\s*\n', '\n\n', current_text)
        
        return current_text.strip()
    
    def _process_docx_with_formatting(self, file_path: str) -> Dict[str, Any]:
        """Process DOCX files with formatting preservation"""
        logger.info("Processing DOCX with formatting preservation")
        
        try:
            text_parts = []
            images_count = 0
            
            with zipfile.ZipFile(file_path, 'r') as docx_zip:
                # Extract document.xml
                document_xml = docx_zip.read('word/document.xml')
                root = ET.fromstring(document_xml)
                
                # Process paragraphs
                for para in root.findall('.//w:p', self.namespaces):
                    para_text = self._extract_paragraph_text(para)
                    if para_text.strip():
                        text_parts.append(para_text)
                
                # Process images
                images_count = self._process_docx_images(docx_zip, root)
            
            formatted_text = '\n\n'.join(text_parts)
            plain_text = self._strip_formatting_markers(formatted_text)
            
            return {
                'formatted_text': formatted_text,
                'plain_text': plain_text,
                'method': 'enhanced_docx_with_formatting',
                'pages_processed': 1,
                'total_image_references': images_count,
                'unique_image_files': images_count,
                'duplicate_image_instances': 0,
                'images_extracted': images_count,
                'images_uploaded': len(self.processed_images),
                'text_blocks_processed': len(text_parts),
                'positioning_accuracy': 1.0,
                'processing_stats': self.stats,
                'tables_count': 0,
                'headings_count': 0
            }
            
        except Exception as e:
            logger.error(f"DOCX processing failed: {e}")
            return self._fallback_docx_extraction(file_path)
    
    def _extract_paragraph_text(self, para_element) -> str:
        """Extract formatted text from a paragraph element"""
        para_parts = []
        
        for run in para_element.findall('.//w:r', self.namespaces):
            run_text = ""
            
            # Get text content
            for t in run.findall('.//w:t', self.namespaces):
                if t.text:
                    run_text += t.text
            
            if run_text:
                # Check formatting
                run_props = run.find('.//w:rPr', self.namespaces)
                if run_props is not None:
                    # Bold
                    if run_props.find('.//w:b', self.namespaces) is not None:
                        run_text = f"**{run_text}**"
                    # Italic
                    if run_props.find('.//w:i', self.namespaces) is not None:
                        run_text = f"*{run_text}*"
                    # Underline
                    if run_props.find('.//w:u', self.namespaces) is not None:
                        run_text = f"<u>{run_text}</u>"
                
                para_parts.append(run_text)
        
        return "".join(para_parts)
    
    def _process_docx_images(self, docx_zip: zipfile.ZipFile, root) -> int:
        """Process images in DOCX file"""
        images_processed = 0
        
        try:
            # Find image relationships
            rels_xml = docx_zip.read('word/_rels/document.xml.rels')
            rels_root = ET.fromstring(rels_xml)
            
            image_rels = {}
            for rel in rels_root.findall('Relationship'):
                if rel.get('Type') and 'image' in rel.get('Type'):
                    image_rels[rel.get('Id')] = rel.get('Target')
            
            # Find images in document
            for drawing in root.findall('.//w:drawing', self.namespaces):
                try:
                    # Find image reference
                    blip = drawing.find('.//a:blip', self.namespaces)
                    if blip is not None:
                        r_embed = blip.get('{http://schemas.openxmlformats.org/officeDocument/2006/relationships}embed')
                        
                        if r_embed in image_rels:
                            image_path = f"word/{image_rels[r_embed]}"
                            
                            try:
                                image_data = docx_zip.read(image_path)
                                image_ext = Path(image_path).suffix[1:]  # Remove dot
                                
                                instance_id = f"docx_img_{self.image_counter}_{int(time.time() * 1000)}"
                                placeholder_name = f"IMG_{instance_id}"
                                
                                # Upload to S3
                                s3_key = self._upload_docx_image_to_s3(
                                    image_data, placeholder_name, image_ext
                                )
                                
                                if s3_key:
                                    # Store image info
                                    image_info = {
                                        'placeholder': placeholder_name,
                                        's3_key': s3_key,
                                        's3_filename': f"{placeholder_name}.{image_ext}",
                                        'original_filename': f"docx_image_{self.image_counter}.{image_ext}",
                                        'image_number': self.image_counter,
                                        'instance_id': instance_id,
                                        'is_duplicate': False,
                                        'size_bytes': len(image_data),
                                        'uploaded': True,
                                        'upload_timestamp': datetime.utcnow().isoformat(),
                                        'source_type': 'docx'
                                    }
                                    
                                    self.processed_images.append(image_info)
                                    self.placeholders[placeholder_name] = s3_key
                                    
                                    # Store metadata
                                    if images_table:
                                        self._store_docx_image_metadata(image_info)
                                    
                                    images_processed += 1
                                    self.image_counter += 1
                                    
                                    logger.info(f"Processed DOCX image: {placeholder_name}")
                            
                            except KeyError:
                                logger.warning(f"Image file not found in DOCX: {image_path}")
                            except Exception as e:
                                logger.error(f"Error processing DOCX image: {e}")
                
                except Exception as e:
                    logger.error(f"Error processing drawing element: {e}")
                    continue
        
        except Exception as e:
            logger.error(f"Error processing DOCX images: {e}")
        
        return images_processed
    
    def _upload_docx_image_to_s3(self, image_data: bytes, placeholder_name: str, 
                               image_ext: str) -> Optional[str]:
        """Upload DOCX image to S3"""
        if not S3_BUCKET:
            logger.error("S3_BUCKET not configured")
            return None
        
        try:
            timestamp_prefix = datetime.utcnow().strftime('%Y/%m/%d/%H')
            s3_key = f"extracted_images_docx/{timestamp_prefix}/{self.document_id}/{placeholder_name}.{image_ext}"
            
            s3_client.put_object(
                Bucket=S3_BUCKET,
                Key=s3_key,
                Body=image_data,
                ContentType=f'image/{image_ext}',
                Metadata={
                    'document_id': self.document_id,
                    'placeholder_name': placeholder_name,
                    'source_type': 'docx',
                    'upload_timestamp': datetime.utcnow().isoformat(),
                    'processing_timestamp': self.processing_timestamp
                }
            )
            
            logger.info(f"DOCX S3 Upload: {placeholder_name} → s3://{S3_BUCKET}/{s3_key}")
            return s3_key
            
        except Exception as e:
            logger.error(f"DOCX S3 upload failed for {placeholder_name}: {e}")
            return None
    
    def _store_docx_image_metadata(self, image_info: Dict[str, Any]) -> None:
        """Store DOCX image metadata"""
        try:
            ttl = datetime.utcnow() + timedelta(days=30)
            image_id = f"{self.document_id}_{image_info['instance_id']}"
            
            item = {
                'document_id': self.document_id,
                'image_id': image_id,
                'image_number': image_info['image_number'],
                'instance_id': image_info['instance_id'],
                'placeholder': image_info['placeholder'],
                's3_bucket': S3_BUCKET,
                's3_key': image_info['s3_key'],
                's3_filename': image_info['s3_filename'],
                'original_filename': image_info['original_filename'],
                'size_bytes': image_info['size_bytes'],
                'source_type': 'docx',
                'extraction_method': 'enhanced_docx_with_formatting',
                'processing_timestamp': self.processing_timestamp,
                'upload_timestamp': image_info['upload_timestamp'],
                'ai_processed': False,
                'ttl': int(ttl.timestamp())
            }
            
            images_table.put_item(Item=item)
            logger.info(f"DynamoDB: Stored DOCX metadata for {image_info['placeholder']}")
            
        except Exception as e:
            logger.error(f"DynamoDB storage failed for {image_info['placeholder']}: {e}")
    
    def _fallback_docx_extraction(self, file_path: str) -> Dict[str, Any]:
        """Fallback DOCX extraction"""
        logger.info("Using fallback DOCX extraction")
        
        try:
            with zipfile.ZipFile(file_path, 'r') as docx_zip:
                document_xml = docx_zip.read('word/document.xml')
                root = ET.fromstring(document_xml)
                
                text_parts = []
                for para in root.findall('.//w:p', self.namespaces):
                    para_text = ""
                    for t in para.findall('.//w:t', self.namespaces):
                        if t.text:
                            para_text += t.text
                    
                    if para_text.strip():
                        text_parts.append(para_text)
                
                formatted_text = '\n\n'.join(text_parts)
                
                return {
                    'formatted_text': formatted_text,
                    'plain_text': formatted_text,
                    'method': 'fallback_docx_extraction',
                    'pages_processed': 1,
                    'total_image_references': 0,
                    'unique_image_files': 0,
                    'duplicate_image_instances': 0,
                    'images_extracted': 0,
                    'images_uploaded': 0,
                    'text_blocks_processed': len(text_parts),
                    'positioning_accuracy': 0.0,
                    'processing_stats': {'fallback': True},
                    'tables_count': 0,
                    'headings_count': 0
                }
        
        except Exception as e:
            logger.error(f"Fallback DOCX extraction failed: {e}")
            return {
                'formatted_text': "DOCX extraction failed completely",
                'plain_text': "DOCX extraction failed completely",
                'method': 'failed_extraction',
                'pages_processed': 0,
                'total_image_references': 0,
                'unique_image_files': 0,
                'duplicate_image_instances': 0,
                'images_extracted': 0,
                'images_uploaded': 0,
                'text_blocks_processed': 0,
                'positioning_accuracy': 0.0,
                'processing_stats': {'failed': True},
                'tables_count': 0,
                'headings_count': 0
            }
    
    def _fallback_pdf_extraction(self, file_path: str) -> Dict[str, Any]:
        """Enhanced fallback extraction"""
        logger.info("Using enhanced fallback PDF extraction")
        
        try:
            pdf_doc = fitz.open(file_path)
            text_parts = []
            
            for page_num in range(len(pdf_doc)):
                page = pdf_doc.load_page(page_num)
                page_text = page.get_text()
                
                if page_text.strip():
                    text_parts.append(f"## Page {page_num + 1}\n\n{page_text}")
            
            pdf_doc.close()
            
            formatted_text = '\n\n'.join(text_parts)
            
            return {
                'formatted_text': formatted_text,
                'plain_text': formatted_text,
                'method': 'fallback_pdf_extraction_enhanced',
                'pages_processed': len(text_parts),
                'total_image_references': 0,
                'unique_image_files': 0,
                'duplicate_image_instances': 0,
                'images_extracted': 0,
                'images_uploaded': 0,
                'text_blocks_processed': 0,
                'positioning_accuracy': 0.0,
                'processing_stats': {'fallback': True},
                'tables_count': 0,
                'headings_count': 0
            }
        
        except Exception as e:
            logger.error(f"Enhanced fallback failed: {e}")
            return {
                'formatted_text': "PDF extraction failed completely",
                'plain_text': "PDF extraction failed completely",
                'method': 'failed_extraction',
                'pages_processed': 0,
                'total_image_references': 0,
                'unique_image_files': 0,
                'duplicate_image_instances': 0,
                'images_extracted': 0,
                'images_uploaded': 0,
                'text_blocks_processed': 0,
                'positioning_accuracy': 0.0,
                'processing_stats': {'failed': True},
                'tables_count': 0,
                'headings_count': 0
            }
    
    def _trigger_image_ai_processing(self, extracted_text: str, images_count: int) -> Dict[str, Any]:
        """Trigger AI processing of extracted images"""
        
        if images_count == 0:
            logger.info("No images to process with AI")
            return {'triggered': False, 'reason': 'no_images'}
        
        try:
            logger.info(f"Triggering AI processing for {images_count} images in document {self.document_id}")
            
            if USE_ASYNC_PROCESSING:
                return self._trigger_via_sqs(images_count)
            else:
                return self._trigger_via_lambda_invoke(images_count)
                
        except Exception as e:
            logger.error(f"Failed to trigger image AI processing: {e}")
            return {
                'triggered': False,
                'error': str(e),
                'method': 'failed'
            }

    def _trigger_via_sqs(self, images_count: int) -> Dict[str, Any]:
        """Trigger image processing via SQS queue (asynchronous, recommended)"""
        
        if not IMAGE_PROCESSING_QUEUE_URL:
            logger.warning("IMAGE_PROCESSING_QUEUE_URL not configured")
            return {'triggered': False, 'reason': 'sqs_not_configured'}
        
        try:
            # Send message to SQS queue
            message_body = {
                'document_id': self.document_id,
                'images_count': images_count,
                'trigger_source': 'document_extractor',
                'processing_timestamp': self.processing_timestamp,
                'trigger_timestamp': datetime.utcnow().isoformat()
            }
            
            response = sqs_client.send_message(
                QueueUrl=IMAGE_PROCESSING_QUEUE_URL,
                MessageBody=json.dumps(message_body),
                MessageAttributes={
                    'DocumentId': {
                        'StringValue': self.document_id,
                        'DataType': 'String'
                    },
                    'ImagesCount': {
                        'StringValue': str(images_count),
                        'DataType': 'Number'
                    },
                    'TriggerSource': {
                        'StringValue': 'document_extractor',
                        'DataType': 'String'
                    }
                }
            )
            
            logger.info(f"Sent image processing request to SQS: {response['MessageId']}")
            
            return {
                'triggered': True,
                'method': 'sqs',
                'message_id': response['MessageId'],
                'queue_url': IMAGE_PROCESSING_QUEUE_URL,
                'images_count': images_count
            }
            
        except Exception as e:
            logger.error(f"SQS trigger failed: {e}")
            return {'triggered': False, 'error': str(e), 'method': 'sqs'}

    def _trigger_via_lambda_invoke(self, images_count: int) -> Dict[str, Any]:
        """Trigger image processing via direct Lambda invocation (synchronous)"""
        
        if not IMAGE_PROCESSOR_LAMBDA_ARN:
            logger.warning("IMAGE_PROCESSOR_LAMBDA_ARN not configured")
            return {'triggered': False, 'reason': 'lambda_arn_not_configured'}
        
        try:
            # Prepare payload for image processor Lambda
            payload = {
                'document_id': self.document_id,
                'images_count': images_count,
                'trigger_source': 'document_extractor',
                'processing_timestamp': self.processing_timestamp
            }
            
            # Invoke image processor Lambda asynchronously
            response = lambda_client.invoke(
                FunctionName=IMAGE_PROCESSOR_LAMBDA_ARN,
                InvocationType='Event',
                Payload=json.dumps(payload)
            )
            
            logger.info(f"Triggered image processor Lambda: {response['StatusCode']}")
            
            return {
                'triggered': True,
                'method': 'lambda_invoke',
                'status_code': response['StatusCode'],
                'lambda_arn': IMAGE_PROCESSOR_LAMBDA_ARN,
                'images_count': images_count
            }
            
        except Exception as e:
            logger.error(f"Lambda invoke trigger failed: {e}")
            return {'triggered': False, 'error': str(e), 'method': 'lambda_invoke'}
    
    def _save_text_files_to_s3(self, formatted_text: str) -> bool:
        """Primary method: Save extracted text as files in S3"""
        
        if not S3_BUCKET:
            logger.error("S3_BUCKET not configured for text file storage")
            return False
        
        try:
            # Create organized folder structure
            timestamp_prefix = datetime.utcnow().strftime('%Y/%m/%d')
            base_path = f"document_extractions/{timestamp_prefix}/{self.document_id}"
            
            plain_text = self._strip_formatting_markers(formatted_text)
            
            # Prepare file metadata
            file_metadata = {
                'document_id': self.document_id,
                'extraction_method': 'enhanced_document_processor_with_advanced_pdf',
                'processing_timestamp': self.processing_timestamp,
                'character_count': str(len(formatted_text)),
                'plain_character_count': str(len(plain_text)),
                'images_processed': str(len(self.processed_images)),
                'extraction_timestamp': datetime.utcnow().isoformat()
            }
            
            # 1. Save formatted text (with markdown formatting)
            formatted_s3_key = f"{base_path}/formatted_text.md"
            s3_client.put_object(
                Bucket=S3_BUCKET,
                Key=formatted_s3_key,
                Body=formatted_text.encode('utf-8'),
                ContentType='text/markdown; charset=utf-8',
                Metadata=file_metadata
            )
            logger.info(f"Saved formatted text: s3://{S3_BUCKET}/{formatted_s3_key}")
            
            # 2. Save plain text (clean version)
            plain_s3_key = f"{base_path}/plain_text.txt"
            s3_client.put_object(
                Bucket=S3_BUCKET,
                Key=plain_s3_key,
                Body=plain_text.encode('utf-8'),
                ContentType='text/plain; charset=utf-8',
                Metadata=file_metadata
            )
            logger.info(f"Saved plain text: s3://{S3_BUCKET}/{plain_s3_key}")
            
            # 3. Save extraction metadata as JSON
            extraction_metadata = {
                'document_id': self.document_id,
                'processing_timestamp': self.processing_timestamp,
                'extraction_timestamp': datetime.utcnow().isoformat(),
                'extraction_method': 'enhanced_document_processor_with_advanced_pdf',
                'formatting_preserved': True,
                'character_count': len(formatted_text),
                'plain_character_count': len(plain_text),
                'images_detected': len(self.processed_images),
                'placeholders': self.placeholders,
                'processing_stats': self.stats,
                'file_locations': {
                    'formatted_text': f"s3://{S3_BUCKET}/{formatted_s3_key}",
                    'plain_text': f"s3://{S3_BUCKET}/{plain_s3_key}",
                    'metadata': f"s3://{S3_BUCKET}/{base_path}/metadata.json"
                },
                'images': [
                    {
                        'placeholder': img['placeholder'],
                        's3_location': f"s3://{S3_BUCKET}/{img['s3_key']}",
                        'original_filename': img.get('original_filename', 'unknown'),
                        'size_bytes': img['size_bytes'],
                        'source_type': img.get('source_type', 'unknown')
                    }
                    for img in self.processed_images
                ]
            }
            
            metadata_s3_key = f"{base_path}/metadata.json"
            s3_client.put_object(
                Bucket=S3_BUCKET,
                Key=metadata_s3_key,
                Body=json.dumps(extraction_metadata, indent=2).encode('utf-8'),
                ContentType='application/json; charset=utf-8',
                Metadata=file_metadata
            )
            logger.info(f"Saved metadata: s3://{S3_BUCKET}/{metadata_s3_key}")
            
            return True
            
        except Exception as e:
            logger.error(f"Failed to save text files to S3: {e}")
            return False
    
    def _store_formatted_text(self, formatted_text: str) -> bool:
        """Store formatted text in DynamoDB with robust error handling"""
        
        logger.info(f"Attempting to store text for document {self.document_id}")
        logger.info(f"Text length: {len(formatted_text)} characters")
        
        # Check if DynamoDB table is available
        if not text_table:
            logger.error("DynamoDB text table not initialized!")
            logger.error(f"DYNAMODB_TEXT_TABLE environment variable: {DYNAMODB_TEXT_TABLE}")
            
            # Fallback: Save to local file for debugging
            self._save_text_to_file(formatted_text)
            return False
        
        try:
            ttl = datetime.utcnow() + timedelta(days=30)
            
            # Generate plain text version for searchability
            plain_text = self._strip_formatting_markers(formatted_text)
            
            # Prepare DynamoDB item
            item = {
                'document_id': self.document_id,
                'extracted_text': formatted_text,
                'plain_text': plain_text,
                'extraction_timestamp': datetime.utcnow().isoformat(),
                'processing_timestamp': self.processing_timestamp,
                'character_count': len(formatted_text),
                'plain_character_count': len(plain_text),
                'extraction_method': 'enhanced_document_processor_with_advanced_pdf',
                'formatting_preserved': True,
                'pages_processed': self.stats.get('pages_processed', 1),
                'images_processed': len(self.processed_images),
                'placeholders': self.placeholders,
                'processing_stats': self.stats,
                'ttl': int(ttl.timestamp())
            }
            
            logger.info(f"Attempting DynamoDB put_item for document {self.document_id}")
            
            # Store in DynamoDB
            response = text_table.put_item(Item=item)
            
            logger.info(f"DynamoDB: Successfully stored formatted text for document {self.document_id}")
            
            # Also save backup to file for verification
            self._save_text_to_file(formatted_text)
            
            return True
            
        except Exception as e:
            logger.error(f"DynamoDB text storage failed: {e}")
            logger.error(f"Exception type: {type(e).__name__}")
            logger.error(f"Exception details: {str(e)}")
            
            # Save to file as fallback
            self._save_text_to_file(formatted_text)
            
            # Re-raise to ensure caller knows about the failure
            raise e
    
    def _save_text_to_file(self, formatted_text: str) -> None:
        """Fallback: Save text to local file for debugging"""
        
        try:
            # Save formatted text
            formatted_file_path = f"/tmp/{self.document_id}_formatted.txt"
            with open(formatted_file_path, 'w', encoding='utf-8') as f:
                f.write(formatted_text)
            logger.info(f"Backup: Saved formatted text to {formatted_file_path}")
            
            # Save plain text
            plain_text = self._strip_formatting_markers(formatted_text)
            plain_file_path = f"/tmp/{self.document_id}_plain.txt"
            with open(plain_file_path, 'w', encoding='utf-8') as f:
                f.write(plain_text)
            logger.info(f"Backup: Saved plain text to {plain_file_path}")
            
        except Exception as e:
            logger.error(f"Failed to save backup text files: {e}")

    def _strip_formatting_markers(self, formatted_text: str) -> str:
        """Generate plain text version by removing formatting markers"""
        
        plain_text = formatted_text
        
        # Remove markdown formatting
        plain_text = re.sub(r'\*\*(.*?)\*\*', r'\1', plain_text)  # Bold
        plain_text = re.sub(r'\*(.*?)\*', r'\1', plain_text)      # Italic
        plain_text = re.sub(r'<u>(.*?)</u>', r'\1', plain_text)   # Underline
        plain_text = re.sub(r'^#+\s*', '', plain_text, flags=re.MULTILINE)  # Headers
        plain_text = re.sub(r'^\s*-\s*', '', plain_text, flags=re.MULTILINE)  # Lists
        plain_text = re.sub(r'\*\*TABLE START\*\*\n', '', plain_text)  # Table markers
        plain_text = re.sub(r'\*\*TABLE END\*\*\n', '', plain_text)
        plain_text = re.sub(r'\|.*?\|', '', plain_text, flags=re.MULTILINE)  # Table content
        plain_text = re.sub(r'^-+\|.*$', '', plain_text, flags=re.MULTILINE)  # Table separators
        plain_text = re.sub(r'!\[.*?\]\(.*?\)', '[Image]', plain_text)  # Image links
        plain_text = re.sub(r'\[.*?\]', '', plain_text)  # Remove remaining brackets
        
        # Clean up extra whitespace
        plain_text = re.sub(r'\n\s*\n\s*\n', '\n\n', plain_text)
        
        return plain_text.strip()

def lambda_handler(event: Dict[str, Any], context) -> Dict[str, Any]:
    """AWS Lambda handler with integrated image AI processing trigger - Supports advanced PDF and DOCX"""
    
    request_id = getattr(context, 'aws_request_id', str(uuid.uuid4()))
    
    try:
        logger.info(f"Enhanced Document processor with advanced PDF support started - Request ID: {request_id}")
        
        # Handle health check
        if event.get('action') == 'health_check':
            return {
                'statusCode': 200,
                'body': json.dumps({
                    'status': 'healthy',
                    'service': 'enhanced-document-processor-with-advanced-pdf-support',
                    'timestamp': datetime.utcnow().isoformat(),
                    'request_id': request_id,
                    'supported_formats': ['PDF', 'DOCX'],
                    'features': [
                        'Advanced PDF processing with spatial image detection',
                        'Complete duplicate image detection and handling',
                        'Precise image positioning in text flow',
                        'Enhanced DOCX processing with formatting preservation',
                        'Automatic AI image processing trigger',
                        'S3 file storage for extracted text and images',
                        'DynamoDB metadata storage',
                        'Event-driven architecture support',
                        'SQS and Lambda invoke integration',
                        'Comprehensive processing statistics',
                        'Advanced error handling and fallback mechanisms'
                    ],
                    'ai_integration': {
                        'sqs_configured': bool(IMAGE_PROCESSING_QUEUE_URL),
                        'lambda_arn_configured': bool(IMAGE_PROCESSOR_LAMBDA_ARN),
                        'async_processing': USE_ASYNC_PROCESSING
                    },
                    'pdf_capabilities': {
                        'spatial_image_detection': True,
                        'duplicate_detection': True,
                        'positioning_accuracy': True,
                        'multi_instance_support': True,
                        'advanced_text_integration': True
                    }
                }),
                'headers': {
                    'Content-Type': 'application/json',
                    'X-Request-ID': request_id
                }
            }
        
        # Handle SQS batch processing
        if 'Records' in event and event['Records']:
            results = []
            
            for record in event['Records']:
                try:
                    message_body = json.loads(record['body'])
                    file_info = message_body['file_info']
                    s3_key = file_info['key']
                    original_filename = Path(s3_key).name
                    
                    # Validate file type
                    file_extension = Path(original_filename).suffix.lower()
                    if file_extension not in ['.pdf', '.docx']:
                        logger.warning(f"Unsupported file type: {file_extension}")
                        continue
                    
                    document_id = generate_unique_document_id(original_filename)
                    logger.info(f"Processing {original_filename} as document {document_id}")
                    
                    # Download file
                    local_path = f"/tmp/{document_id}_{original_filename}"
                    s3_client.download_file(S3_BUCKET, s3_key, local_path)
                    
                    # Process with enhanced processor
                    processor = EnhancedDocumentProcessor(document_id)
                    result = processor.process_document(local_path)
                    
                    results.append(result)
                    
                    # Cleanup
                    try:
                        os.unlink(local_path)
                    except Exception:
                        pass
                
                except Exception as e:
                    logger.error(f"Failed to process SQS record: {e}")
                    results.append({
                        'success': False,
                        'error': str(e),
                        'traceback': traceback.format_exc()
                    })
            
            successful = len([r for r in results if r.get('success', False)])
            
            return {
                'statusCode': 200 if successful > 0 else 400,
                'body': json.dumps({
                    'success': successful > 0,
                    'processed_count': successful,
                    'failed_count': len(results) - successful,
                    'total_count': len(results),
                    'results': results,
                    'request_id': request_id
                }),
                'headers': {
                    'Content-Type': 'application/json',
                    'X-Request-ID': request_id
                }
            }
        
        # Handle direct invocation
        else:
            s3_key = event.get('s3_key') or event.get('key')
            s3_bucket = event.get('s3_bucket') or S3_BUCKET
            original_filename = event.get('original_filename')
            
            if not s3_bucket or not s3_key:
                return {
                    'statusCode': 400,
                    'body': json.dumps({
                        'success': False,
                        'error': 'missing_parameters',
                        'message': 'Required parameters: s3_bucket, s3_key',
                        'request_id': request_id
                    }),
                    'headers': {
                        'Content-Type': 'application/json',
                        'X-Request-ID': request_id
                    }
                }
            
            if not original_filename:
                original_filename = Path(s3_key).name
            
            # Validate file type
            file_extension = Path(original_filename).suffix.lower()
            if file_extension not in ['.pdf', '.docx']:
                return {
                    'statusCode': 400,
                    'body': json.dumps({
                        'success': False,
                        'error': 'unsupported_file_type',
                        'message': f'Unsupported file type: {file_extension}. Supported types: .pdf, .docx',
                        'request_id': request_id
                    }),
                    'headers': {
                        'Content-Type': 'application/json',
                        'X-Request-ID': request_id
                    }
                }
            
            document_id = generate_unique_document_id(original_filename)
            logger.info(f"Processing {original_filename} as document {document_id}")
            
            # Download file
            local_path = f"/tmp/{document_id}_{original_filename}"
            s3_client.download_file(s3_bucket, s3_key, local_path)
            
            # Process with enhanced processor
            processor = EnhancedDocumentProcessor(document_id)
            result = processor.process_document(local_path)
            
            # Cleanup
            try:
                os.unlink(local_path)
            except Exception:
                pass
            
            return {
                'statusCode': 200 if result['success'] else 500,
                'body': json.dumps(result),
                'headers': {
                    'Content-Type': 'application/json',
                    'X-Request-ID': request_id
                }
            }
    
    except Exception as e:
        logger.error(f"Lambda handler error: {e}")
        return {
            'statusCode': 500,
            'body': json.dumps({
                'success': False,
                'error': 'lambda_handler_error',
                'message': str(e),
                'request_id': request_id,
                'traceback': traceback.format_exc()
            }),
            'headers': {
                'Content-Type': 'application/json',
                'X-Request-ID': request_id
            }
        }
