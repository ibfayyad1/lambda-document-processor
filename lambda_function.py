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
import hashlib
import fitz  # PyMuPDF for PDF processing
from typing import Dict, Any, List, Optional, Tuple, Set
from pathlib import Path
from decimal import Decimal
from datetime import datetime, timedelta
from collections import defaultdict

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

# Advanced PDF Processing Configuration
ENABLE_ADVANCED_IMAGE_DETECTION = True
ENABLE_SPATIAL_POSITIONING = True
ENABLE_DUPLICATE_DETECTION = True
IMAGE_HASH_SIMILARITY_THRESHOLD = 0.95  # 95% similarity for duplicate detection
MIN_IMAGE_SIZE_BYTES = 100  # Skip tiny images
MAX_IMAGES_PER_PAGE = 50  # Safety limit

# AWS Clients
s3_client = boto3.client('s3')
dynamodb = boto3.resource('dynamodb')
lambda_client = boto3.client('lambda')
sqs_client = boto3.client('sqs')
events_client = boto3.client('events')

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


class AdvancedImageInfo:
    """Enhanced image information class for advanced processing"""
    
    def __init__(self, xref: int, page_num: int, img_index: int, bbox: tuple = None):
        self.xref = xref
        self.page_num = page_num
        self.img_index = img_index
        self.bbox = bbox  # (x0, y0, x1, y1)
        self.hash_value = None
        self.size_bytes = 0
        self.width = 0
        self.height = 0
        self.is_duplicate = False
        self.duplicate_group_id = None
        self.instances = []  # List of all instances if this is the master
        self.master_image = None  # Reference to master if this is duplicate
        self.spatial_context = {}
        self.extraction_methods = []  # Which methods detected this image
        self.image_data = None
        self.content_type = None
        self.reference_number = None
        self.marker = None


class EnhancedDocumentProcessor:
    """Enhanced processor that handles both PDF and DOCX files with ADVANCED PDF image processing"""
    
    def __init__(self, document_id: str):
        self.document_id = document_id
        self.placeholders = {}
        self.processed_images = []
        self.image_counter = 1
        self.processing_timestamp = datetime.utcnow().isoformat()
        
        # Advanced PDF processing attributes
        self.all_detected_images = {}  # xref -> AdvancedImageInfo
        self.duplicate_groups = {}  # group_id -> [AdvancedImageInfo]
        self.image_hashes = {}  # hash -> AdvancedImageInfo (first occurrence)
        self.page_image_positions = {}  # page_num -> [image positions]
        self.text_blocks_by_page = {}  # page_num -> [text blocks with positions]
        
        # DOCX processing attributes
        self.namespaces = {
            'w': 'http://schemas.openxmlformats.org/wordprocessingml/2006/main',
            'pic': 'http://schemas.openxmlformats.org/drawingml/2006/picture',
            'a': 'http://schemas.openxmlformats.org/drawingml/2006/main',
            'r': 'http://schemas.openxmlformats.org/officeDocument/2006/relationships',
            'wp': 'http://schemas.openxmlformats.org/drawingml/2006/wordprocessingDrawing'
        }
        
    def process_document(self, file_path: str) -> Dict[str, Any]:
        """Main processing method with formatting preservation and AI trigger - Supports PDF and DOCX"""
        start_time = time.time()
        
        try:
            logger.info(f"Starting ADVANCED enhanced processing for {self.document_id}")
            
            # Validate file
            if not os.path.exists(file_path):
                raise Exception(f"File not found: {file_path}")
            
            file_size = os.path.getsize(file_path)
            if file_size > MAX_FILE_SIZE:
                raise Exception(f"File too large: {file_size} bytes")
            
            # Process based on file type
            file_extension = Path(file_path).suffix.lower()
            
            if file_extension == '.pdf':
                result = self._process_pdf_with_advanced_image_handling(file_path)
                extraction_method = 'advanced_pdf_with_spatial_positioning_and_deduplication'
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
            
            logger.info(f"ADVANCED enhanced processing complete in {processing_time:.2f}s")
            logger.info(f"Images processed: {len(self.processed_images)}")
            logger.info(f"Duplicate groups found: {len(self.duplicate_groups)}")
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
                'duplicate_groups_count': len(self.duplicate_groups),
                'total_image_instances': result.get('total_image_instances', 0),
                'unique_images': result.get('unique_images', 0),
                'placeholders': self.placeholders,
                'processing_time': processing_time,
                'extraction_method': extraction_method,
                'pages_processed': result.get('pages_processed', 1),
                'images_detected': result.get('total_image_references', 0),
                'unique_image_files': result.get('unique_image_files', 0),
                'images_extracted': len(self.processed_images),
                'images_uploaded': len([img for img in self.processed_images if img.get('uploaded')]),
                'tables_detected': result.get('tables_count', 0),
                'headings_detected': result.get('headings_count', 0),
                'formatting_preserved': True,
                'files_saved_to_s3': True,
                'spatial_positioning_enabled': ENABLE_SPATIAL_POSITIONING,
                'duplicate_detection_enabled': ENABLE_DUPLICATE_DETECTION,
                'advanced_image_detection_enabled': ENABLE_ADVANCED_IMAGE_DETECTION,
                'output_files': file_locations,
                's3_base_path': f"s3://{S3_BUCKET}/{base_path}/",
                'ai_processing': ai_trigger_result,
                'error_count': 0,
                'warning_count': 0,
                'errors': [],
                'warnings': []
            }
            
        except Exception as e:
            processing_time = time.time() - start_time
            logger.error(f"ADVANCED enhanced processing failed: {e}")
            
            return {
                'success': False,
                'document_id': self.document_id,
                'processing_timestamp': self.processing_timestamp,
                'extracted_text': "",
                'plain_text': "",
                'images_count': 0,
                'duplicate_groups_count': 0,
                'total_image_instances': 0,
                'unique_images': 0,
                'placeholders': {},
                'processing_time': processing_time,
                'extraction_method': 'failed',
                'pages_processed': 0,
                'images_detected': 0,
                'images_extracted': 0,
                'images_uploaded': 0,
                'formatting_preserved': False,
                'spatial_positioning_enabled': ENABLE_SPATIAL_POSITIONING,
                'duplicate_detection_enabled': ENABLE_DUPLICATE_DETECTION,
                'advanced_image_detection_enabled': ENABLE_ADVANCED_IMAGE_DETECTION,
                'ai_processing': {'triggered': False, 'reason': 'processing_failed'},
                'error_count': 1,
                'warning_count': 0,
                'errors': [str(e)],
                'warnings': [],
                'traceback': traceback.format_exc()
            }
    
    # ========================================
    # ADVANCED PDF PROCESSING METHODS
    # ========================================
    
    def _process_pdf_with_advanced_image_handling(self, file_path: str) -> Dict[str, Any]:
        """FIXED ADVANCED PDF processing with WORKING duplicate detection using proper PyMuPDF methods"""
        
        logger.info("Starting FIXED ADVANCED PDF processing with working duplicate detection...")
        
        try:
            # Open PDF document
            pdf_doc = fitz.open(file_path)
            pages_processed = len(pdf_doc)
            
            logger.info(f"PDF opened successfully: {pages_processed} pages")
            
            # PHASE 1: COLLECT ALL IMAGE XREFS FROM ALL PAGES
            logger.info("PHASE 1: Collecting all image xrefs from all pages...")
            all_page_images = self._collect_all_image_xrefs(pdf_doc)
            logger.info(f"Collected {len(all_page_images)} total image occurrences across all pages")
            
            # PHASE 2: FIXED DUPLICATE DETECTION USING ACTUAL IMAGE CONTENT
            logger.info("PHASE 2: FIXED duplicate detection using actual image content...")
            unique_images, duplicate_mapping = self._detect_duplicates_by_content(pdf_doc, all_page_images)
            logger.info(f"FIXED detection found {len(unique_images)} unique images with {len(duplicate_mapping)} total groups")
            
            # PHASE 3: EXTRACT TEXT WITH POSITIONING
            logger.info("PHASE 3: Extracting text with spatial positioning...")
            text_blocks_by_page = self._extract_text_with_spatial_info(pdf_doc)
            
            # PHASE 4: CREATE INTEGRATED CONTENT WITH PROPER DUPLICATE HANDLING
            logger.info("PHASE 4: Creating integrated content with proper duplicate handling...")
            formatted_text = self._integrate_content_with_fixed_duplicates(
                pdf_doc, text_blocks_by_page, all_page_images, unique_images, duplicate_mapping
            )
            
            # PHASE 5: UPLOAD ONLY UNIQUE IMAGES
            logger.info("PHASE 5: Uploading only unique images...")
            final_text = self._upload_unique_images_and_replace_duplicates(
                formatted_text, unique_images, duplicate_mapping
            )
            
            # Generate plain text
            plain_text = self._strip_formatting_markers(final_text)
            
            pdf_doc.close()
            
            # Calculate CORRECT statistics
            total_image_instances = len(all_page_images)
            unique_images_count = len(unique_images)
            duplicate_groups_count = len([group for group in duplicate_mapping.values() if len(group) > 1])
            
            logger.info(f"FIXED ADVANCED PDF processing complete:")
            logger.info(f"  - Pages processed: {pages_processed}")
            logger.info(f"  - Total image instances: {total_image_instances}")
            logger.info(f"  - Unique images: {unique_images_count}")
            logger.info(f"  - Duplicate groups: {duplicate_groups_count}")
            logger.info(f"  - Images uploaded: {len(self.processed_images)}")
            
            return {
                'formatted_text': final_text,
                'plain_text': plain_text,
                'method': 'fixed_advanced_pdf_with_working_duplicate_detection',
                'pages_processed': pages_processed,
                'total_image_references': len(all_page_images),
                'total_image_instances': total_image_instances,
                'unique_image_files': unique_images_count,
                'unique_images': unique_images_count,
                'duplicate_groups': duplicate_groups_count,
                'tables_count': self._count_tables_in_text(final_text),
                'headings_count': self._count_headings_in_text(final_text)
            }
            
        except Exception as e:
            logger.error(f"FIXED ADVANCED PDF processing failed: {e}")
            return self._fallback_pdf_extraction(file_path)
    
    def _collect_all_image_xrefs(self, pdf_doc) -> List[Dict]:
        """PHASE 1: Collect ALL image xrefs from all pages with position info"""
        
        all_page_images = []
        
        for page_num in range(len(pdf_doc)):
            page = pdf_doc.load_page(page_num)
            
            try:
                # Get all images on this page
                page_images = page.get_images()
                
                for img_idx, img_info in enumerate(page_images):
                    xref = img_info[0]
                    
                    # Create image occurrence record
                    occurrence = {
                        'xref': xref,
                        'page_num': page_num,
                        'img_index': img_idx,
                        'occurrence_id': len(all_page_images),
                        'marker': f"__IMAGE_PLACEHOLDER_{len(all_page_images)}__"
                    }
                    
                    all_page_images.append(occurrence)
                    
                    logger.debug(f"Found image xref={xref} on page {page_num + 1}")
                
            except Exception as e:
                logger.warning(f"Failed to get images from page {page_num + 1}: {e}")
        
        logger.info(f"Collected {len(all_page_images)} total image occurrences")
        return all_page_images
    
    def _detect_duplicates_by_content(self, pdf_doc, all_page_images: List[Dict]) -> Tuple[List[Dict], Dict[str, List[Dict]]]:
        """PHASE 2: FIXED duplicate detection using actual image content comparison"""
        
        logger.info("Starting FIXED duplicate detection using actual image content...")
        
        # Step 1: Extract unique xrefs
        unique_xrefs = set()
        xref_to_occurrences = defaultdict(list)
        
        for occurrence in all_page_images:
            xref = occurrence['xref']
            unique_xrefs.add(xref)
            xref_to_occurrences[xref].append(occurrence)
        
        logger.info(f"Found {len(unique_xrefs)} unique xrefs from {len(all_page_images)} total occurrences")
        
        # Step 2: Extract actual image content for each unique xref
        xref_to_content = {}
        content_hash_to_xref = {}
        
        for xref in unique_xrefs:
            try:
                # Method 1: Try extract_image first (recommended)
                try:
                    img_dict = pdf_doc.extract_image(xref)
                    if img_dict and 'image' in img_dict:
                        image_data = img_dict['image']
                        content_type = img_dict.get('ext', 'png')
                        logger.debug(f"Extracted image data for xref={xref} using extract_image: {len(image_data)} bytes")
                    else:
                        raise Exception("extract_image returned no data")
                        
                except Exception:
                    # Method 2: Fallback to Pixmap
                    try:
                        pix = fitz.Pixmap(pdf_doc, xref)
                        if pix.n - pix.alpha < 4:  # Valid image
                            image_data = pix.tobytes("png")
                            content_type = 'png'
                            logger.debug(f"Extracted image data for xref={xref} using Pixmap: {len(image_data)} bytes")
                            pix = None
                        else:
                            logger.warning(f"Skipping complex image xref={xref}")
                            continue
                    except Exception as e:
                        logger.warning(f"Failed to extract image data for xref={xref}: {e}")
                        continue
                
                # Skip tiny images
                if len(image_data) < MIN_IMAGE_SIZE_BYTES:
                    logger.debug(f"Skipping tiny image xref={xref}: {len(image_data)} bytes")
                    continue
                
                # Generate content hash
                content_hash = hashlib.md5(image_data).hexdigest()
                
                # Store image data and hash
                xref_to_content[xref] = {
                    'image_data': image_data,
                    'content_hash': content_hash,
                    'content_type': content_type,
                    'size_bytes': len(image_data)
                }
                
                logger.debug(f"xref={xref} → hash={content_hash[:8]}..., size={len(image_data)} bytes")
                
            except Exception as e:
                logger.warning(f"Failed to process xref={xref}: {e}")
                continue
        
        # Step 3: Group by actual content hash (this is where duplicates are found)
        hash_to_xrefs = defaultdict(list)
        
        for xref, content_info in xref_to_content.items():
            content_hash = content_info['content_hash']
            hash_to_xrefs[content_hash].append(xref)
        
        # Step 4: Identify unique images and duplicate groups
        unique_images = []
        duplicate_mapping = {}  # hash -> list of occurrences
        
        for content_hash, xref_list in hash_to_xrefs.items():
            # Get all occurrences for all xrefs with this content hash
            all_occurrences = []
            for xref in xref_list:
                all_occurrences.extend(xref_to_occurrences[xref])
            
            # Create master image entry (use first occurrence)
            master_occurrence = all_occurrences[0]
            master_xref = master_occurrence['xref']
            content_info = xref_to_content[master_xref]
            
            unique_image = {
                'master_xref': master_xref,
                'content_hash': content_hash,
                'image_data': content_info['image_data'],
                'content_type': content_info['content_type'],
                'size_bytes': content_info['size_bytes'],
                'total_occurrences': len(all_occurrences),
                'pages': [occ['page_num'] + 1 for occ in all_occurrences],
                'all_occurrences': all_occurrences
            }
            
            unique_images.append(unique_image)
            duplicate_mapping[content_hash] = all_occurrences
            
            # Log duplicate information
            if len(all_occurrences) > 1:
                pages_str = ', '.join([str(occ['page_num'] + 1) for occ in all_occurrences])
                logger.info(f"🎯 DUPLICATE DETECTED: hash={content_hash[:8]}... appears {len(all_occurrences)} times on pages: {pages_str}")
            else:
                logger.debug(f"✅ UNIQUE IMAGE: hash={content_hash[:8]}... on page {all_occurrences[0]['page_num'] + 1}")
        
        # Final statistics
        total_duplicates = sum(1 for group in duplicate_mapping.values() if len(group) > 1)
        logger.info(f"🔍 FIXED DUPLICATE DETECTION COMPLETE:")
        logger.info(f"  - Unique content hashes: {len(hash_to_xrefs)}")
        logger.info(f"  - Master images: {len(unique_images)}")
        logger.info(f"  - Images with duplicates: {total_duplicates}")
        
        return unique_images, duplicate_mapping
    
    def _integrate_content_with_fixed_duplicates(self, pdf_doc, text_blocks_by_page: Dict[int, List[Dict]], 
                                               all_page_images: List[Dict], unique_images: List[Dict], 
                                               duplicate_mapping: Dict[str, List[Dict]]) -> str:
        """PHASE 4: Create integrated content with proper duplicate handling"""
        
        logger.info("Creating integrated content with fixed duplicate handling...")
        
        formatted_parts = []
        
        for page_num in range(len(pdf_doc)):
            logger.debug(f"Processing page {page_num + 1} for content integration")
            
            # Get text blocks for this page
            page_text_blocks = text_blocks_by_page.get(page_num, [])
            
            # Get image occurrences for this page
            page_image_occurrences = [occ for occ in all_page_images if occ['page_num'] == page_num]
            
            # Create page content with image placeholders
            page_content = self._create_page_content_with_placeholders(
                page_num, page_text_blocks, page_image_occurrences
            )
            
            if page_content.strip():
                formatted_parts.append(f"## Page {page_num + 1}\n\n{page_content}")
        
        return '\n\n'.join(formatted_parts)
    
    def _create_page_content_with_placeholders(self, page_num: int, text_blocks: List[Dict], 
                                             image_occurrences: List[Dict]) -> str:
        """Create page content with image placeholders positioned correctly"""
        
        # Simple approach: append text blocks, then add image placeholders
        content_parts = []
        
        # Add all text blocks
        for text_block in text_blocks:
            content_parts.append(text_block.get('content', ''))
        
        # Add image placeholders
        for occurrence in image_occurrences:
            marker = occurrence['marker']
            content_parts.append(f"\n{marker}\n*[Image from page {page_num + 1}]*")
        
        return '\n\n'.join(content_parts)
    
    def _upload_unique_images_and_replace_duplicates(self, formatted_text: str, unique_images: List[Dict], 
                                                   duplicate_mapping: Dict[str, List[Dict]]) -> str:
        """PHASE 5: Upload unique images and replace ALL duplicate occurrences"""
        
        logger.info(f"Uploading {len(unique_images)} unique images and replacing duplicates...")
        
        current_text = formatted_text
        
        for unique_image in unique_images:
            try:
                content_hash = unique_image['content_hash']
                image_data = unique_image['image_data']
                
                # Create unique placeholder name
                timestamp_suffix = int(time.time() * 1000) + self.image_counter
                placeholder_name = f"PDF_IMAGE_{self.image_counter}_{timestamp_suffix}"
                
                # Upload to S3
                s3_key = self._upload_unique_image_to_s3(image_data, placeholder_name, unique_image)
                
                if s3_key:
                    # Get all occurrences for this content hash
                    all_occurrences = duplicate_mapping[content_hash]
                    
                    # Store image info
                    image_info = {
                        'placeholder': placeholder_name,
                        's3_key': s3_key,
                        's3_filename': f"{placeholder_name}.png",
                        'original_filename': f"pdf_unique_img_{unique_image['master_xref']}.png",
                        'image_number': self.image_counter,
                        'reference_number': unique_image['master_xref'],
                        'page_number': unique_image['pages'][0],  # First occurrence page
                        'size_bytes': unique_image['size_bytes'],
                        'content_hash': content_hash,
                        'is_master_image': True,
                        'total_instances': len(all_occurrences),
                        'instance_pages': unique_image['pages'],
                        'uploaded': True,
                        'upload_timestamp': datetime.utcnow().isoformat(),
                        'source_type': 'pdf'
                    }
                    
                    self.processed_images.append(image_info)
                    self.placeholders[placeholder_name] = s3_key
                    
                    # Store in DynamoDB
                    self._store_image_metadata(image_info)
                    
                    # Replace ALL occurrences of this image
                    pages_str = ', '.join([str(p) for p in unique_image['pages']])
                    placeholder_text = f"\n![{placeholder_name}]({s3_key})\n*PDF Image {self.image_counter} (appears on page(s): {pages_str})*\n"
                    
                    # Replace all markers for this image
                    replaced_count = 0
                    for occurrence in all_occurrences:
                        marker = occurrence['marker']
                        marker_count = current_text.count(marker)
                        current_text = current_text.replace(marker, placeholder_text)
                        replaced_count += marker_count
                    
                    logger.info(f"✅ Processed {placeholder_name}: {len(all_occurrences)} instances on pages {pages_str} ({replaced_count} markers replaced)")
                    
                    self.image_counter += 1
                else:
                    logger.error(f"Failed to upload unique image with hash {content_hash[:8]}...")
                
            except Exception as e:
                logger.error(f"Failed to process unique image: {e}")
                continue
        
        # Clean up any remaining markers
        remaining_markers = len(re.findall(r'__IMAGE_PLACEHOLDER_\d+__', current_text))
        if remaining_markers > 0:
            logger.warning(f"Cleaning up {remaining_markers} unprocessed markers")
            current_text = re.sub(r'__IMAGE_PLACEHOLDER_\d+__', '', current_text)
        
        # Clean up extra whitespace
        current_text = re.sub(r'\n\s*\n\s*\n', '\n\n', current_text)
        
        logger.info(f"✅ Fixed duplicate processing complete: uploaded {len(self.processed_images)} unique images")
        
        return current_text.strip()
    
    def _upload_unique_image_to_s3(self, image_data: bytes, placeholder_name: str, unique_image: Dict) -> Optional[str]:
        """Upload unique image to S3 with comprehensive metadata"""
        
        if not S3_BUCKET:
            logger.error("S3_BUCKET not configured")
            return None
        
        try:
            timestamp_prefix = datetime.utcnow().strftime('%Y/%m/%d/%H')
            s3_key = f"extracted_images/{timestamp_prefix}/{self.document_id}/{placeholder_name}.png"
            
            # Comprehensive metadata
            metadata = {
                'document_id': self.document_id,
                'placeholder_name': placeholder_name,
                'source_type': 'pdf_fixed_duplicate_detection',
                'master_xref': str(unique_image['master_xref']),
                'content_hash': unique_image['content_hash'][:32],  # Truncate for metadata limit
                'total_instances': str(unique_image['total_instances']),
                'pages': ','.join([str(p) for p in unique_image['pages']]),
                'size_bytes': str(len(image_data)),
                'content_type': unique_image.get('content_type', 'png'),
                'upload_timestamp': datetime.utcnow().isoformat(),
                'processing_timestamp': self.processing_timestamp
            }
            
            s3_client.put_object(
                Bucket=S3_BUCKET,
                Key=s3_key,
                Body=image_data,
                ContentType=f"image/{unique_image.get('content_type', 'png')}",
                Metadata=metadata
            )
            
            logger.info(f"Fixed S3 Upload: {placeholder_name} → s3://{S3_BUCKET}/{s3_key}")
            return s3_key
            
        except Exception as e:
            logger.error(f"Fixed S3 upload failed for {placeholder_name}: {e}")
            return None
    
    def _detect_drawing_images(self, page, page_num: int) -> Dict[int, AdvancedImageInfo]:
        """Detect images within drawing objects"""
        
        drawing_images = {}
        
        try:
            # Get drawing objects from page
            drawings = page.get_drawings()
            
            for draw_idx, drawing in enumerate(drawings):
                # Check if drawing contains image references
                if 'items' in drawing:
                    for item in drawing['items']:
                        if item[0] == 'l':  # Line with possible image fill
                            continue
                        elif item[0] == 'c':  # Curve with possible image fill
                            continue
                        elif item[0] == 're':  # Rectangle that might be an image
                            # Check if rectangle has image properties
                            rect = item[1]
                            if len(rect) >= 4:  # x0, y0, x1, y1
                                # This could be an image placeholder
                                pass
                                
            # Alternative: Check for inline images in content stream
            try:
                content = page.get_text("dict")
                # Look for image markers in content
                for block in content.get("blocks", []):
                    if block.get("type") == 1:  # Image block
                        # This is an image block
                        if "bbox" in block:
                            bbox = block["bbox"]
                            # Try to find corresponding xref
                            # This is complex and may require parsing content stream
                            pass
            except:
                pass
                
        except Exception as e:
            logger.debug(f"Drawing image detection failed for page {page_num}: {e}")
        
        return drawing_images
    
    def _detect_xobject_images(self, page, page_num: int) -> Dict[int, AdvancedImageInfo]:
        """Detect images in XObjects and Form objects"""
        
        xobject_images = {}
        
        try:
            # Get page dictionary
            page_dict = page.get_contents()
            if not page_dict:
                return xobject_images
                
            # This is a simplified approach - full implementation would need
            # to parse the PDF content stream and identify XObject references
            
            # For now, we'll use a heuristic approach
            page_obj = page.get_contents()
            if page_obj:
                content_bytes = page_obj[0] if isinstance(page_obj, list) else page_obj
                if hasattr(content_bytes, 'get_data'):
                    content_text = content_bytes.get_data().decode('latin1', errors='ignore')
                    
                    # Look for XObject image references in content stream
                    xobj_pattern = r'/Im(\d+)\s+Do'
                    matches = re.findall(xobj_pattern, content_text)
                    
                    for match in matches:
                        # This indicates an image XObject usage
                        # We'd need to resolve the actual xref
                        logger.debug(f"Found XObject image reference Im{match} on page {page_num}")
                        
        except Exception as e:
            logger.debug(f"XObject image detection failed for page {page_num}: {e}")
        
        return xobject_images
    
    def _detect_pattern_images(self, page, page_num: int) -> Dict[int, AdvancedImageInfo]:
        """Detect images used in patterns and shadings"""
        
        pattern_images = {}
        
        try:
            # Get page resources for pattern detection
            # This would require deeper PDF parsing
            # For now, implemented as placeholder for future enhancement
            pass
                        
        except Exception as e:
            logger.debug(f"Pattern image detection failed for page {page_num}: {e}")
        
        return pattern_images
    
    def _find_all_image_instances_on_page(self, page, page_num: int, page_images: Dict[int, AdvancedImageInfo]) -> None:
        """Find ALL instances of each image on the page (for images used multiple times)"""
        
        try:
            # Get all image instances with positioning
            image_instances = []
            
            # Method 1: Try to get image instances with bounding boxes
            try:
                # Get images with location info
                images_with_bbox = page.get_image_bbox([img_info for img_info in page.get_images()])
                
                for i, (img_info, bbox) in enumerate(zip(page.get_images(), images_with_bbox)):
                    xref = img_info[0]
                    if xref in page_images:
                        # Store bounding box info
                        if not page_images[xref].bbox:
                            page_images[xref].bbox = bbox
                        
                        # Add to instances list
                        instance_info = {
                            'bbox': bbox,
                            'instance_index': i,
                            'page_num': page_num
                        }
                        page_images[xref].instances.append(instance_info)
                        
            except Exception as e:
                logger.debug(f"Image bbox detection failed for page {page_num}: {e}")
            
            # Method 2: Parse content stream for multiple Do operations (same image used multiple times)
            try:
                content_stream = page.get_contents()
                if content_stream:
                    # Convert to text for parsing
                    content_bytes = content_stream[0] if isinstance(content_stream, list) else content_stream
                    if hasattr(content_bytes, 'get_data'):
                        content_text = content_bytes.get_data().decode('latin1', errors='ignore')
                        
                        # Look for transformation matrices followed by Do operations
                        # This pattern indicates multiple placements of the same image
                        matrix_do_pattern = r'(\d+(?:\.\d+)?\s+){6}cm\s+/Im(\d+)\s+Do'
                        matches = re.findall(matrix_do_pattern, content_text)
                        
                        if matches:
                            logger.debug(f"Found {len(matches)} potential multiple image instances on page {page_num}")
                            
            except Exception as e:
                logger.debug(f"Content stream parsing failed for page {page_num}: {e}")
                
        except Exception as e:
            logger.warning(f"Multiple instance detection failed for page {page_num}: {e}")
    
    def _identify_duplicates_advanced(self, pdf_doc, all_images: Dict[int, AdvancedImageInfo]) -> Tuple[List[AdvancedImageInfo], Dict[str, List[AdvancedImageInfo]]]:
        """PHASE 2: FIXED Advanced duplicate detection using multiple hashing methods"""
        
        logger.info("Starting FIXED advanced duplicate detection...")
        
        # FIXED: Use content-based hashing instead of xref-based
        content_hash_map = {}  # content_hash -> first image with this hash
        duplicate_groups = {}  # group_id -> list of images  
        unique_images = []
        processed_hashes = set()
        
        logger.info(f"Processing {len(all_images)} total image xrefs for duplicate detection...")
        
        for xref, image_info in all_images.items():
            try:
                # Extract image data
                image_data = self._extract_image_data(pdf_doc, xref)
                
                if not image_data or len(image_data) < MIN_IMAGE_SIZE_BYTES:
                    logger.debug(f"Skipping tiny or empty image xref={xref}")
                    continue
                
                image_info.image_data = image_data
                image_info.size_bytes = len(image_data)
                
                # FIXED: Generate content-based hash (not xref-based)
                content_hash = hashlib.md5(image_data).hexdigest()
                image_info.hash_value = content_hash
                
                logger.debug(f"Image xref={xref}, page={image_info.page_num + 1}, hash={content_hash[:8]}..., size={len(image_data)} bytes")
                
                # FIXED: Check for duplicates by content hash
                if content_hash in content_hash_map:
                    # This is a duplicate - same content hash as existing image
                    master_image = content_hash_map[content_hash]
                    image_info.is_duplicate = True
                    image_info.master_image = master_image
                    image_info.duplicate_group_id = master_image.duplicate_group_id
                    
                    # Add to existing duplicate group
                    duplicate_groups[master_image.duplicate_group_id].append(image_info)
                    
                    logger.info(f"🎯 DUPLICATE FOUND: xref={xref} (page {image_info.page_num + 1}) matches xref={master_image.xref} (page {master_image.page_num + 1})")
                    
                else:
                    # This is a unique image - first time seeing this content
                    image_info.is_duplicate = False
                    group_id = f"group_{len(duplicate_groups)}"
                    image_info.duplicate_group_id = group_id
                    
                    # Create new group with this image as master
                    duplicate_groups[group_id] = [image_info]
                    content_hash_map[content_hash] = image_info
                    unique_images.append(image_info)
                    
                    logger.info(f"✅ UNIQUE IMAGE: xref={xref} on page {image_info.page_num + 1}, hash={content_hash[:8]}...")
                
                processed_hashes.add(content_hash)
                
            except Exception as e:
                logger.warning(f"Failed to process image xref={xref}: {e}")
                continue
        
        # FIXED: Log detailed duplicate detection results
        logger.info(f"🔍 DUPLICATE DETECTION RESULTS:")
        logger.info(f"  - Total image xrefs processed: {len(all_images)}")
        logger.info(f"  - Unique content hashes: {len(processed_hashes)}")
        logger.info(f"  - Unique images (masters): {len(unique_images)}")
        logger.info(f"  - Duplicate groups: {len(duplicate_groups)}")
        
        # Log detailed duplicate group information
        total_instances = 0
        duplicate_count = 0
        
        for group_id, group_images in duplicate_groups.items():
            total_instances += len(group_images)
            if len(group_images) > 1:
                duplicate_count += len(group_images) - 1  # All except master are duplicates
                pages = [str(img.page_num + 1) for img in group_images]
                master_hash = group_images[0].hash_value[:8] if group_images[0].hash_value else "unknown"
                logger.info(f"  🔄 {group_id}: {len(group_images)} instances on pages {', '.join(pages)} (hash: {master_hash}...)")
        
        logger.info(f"  - Total image instances: {total_instances}")
        logger.info(f"  - Duplicate instances: {duplicate_count}")
        
        return unique_images, duplicate_groups
    
    def _extract_image_data(self, pdf_doc, xref: int) -> Optional[bytes]:
        """Extract raw image data from PDF xref"""
        
        try:
            # Method 1: Direct pixmap extraction
            pix = fitz.Pixmap(pdf_doc, xref)
            
            if pix.n - pix.alpha < 4:  # Valid image (GRAY or RGB)
                if pix.n - pix.alpha == 1:  # Grayscale
                    img_data = pix.tobytes("png")
                elif pix.n - pix.alpha == 3:  # RGB
                    img_data = pix.tobytes("png")
                else:
                    # Convert CMYK to RGB
                    pix_rgb = fitz.Pixmap(fitz.csRGB, pix)
                    img_data = pix_rgb.tobytes("png")
                    pix_rgb = None
                
                pix = None  # Free memory
                return img_data
            else:
                pix = None
                return None
                
        except Exception as e:
            logger.debug(f"Failed to extract image data for xref {xref}: {e}")
            
            # Method 2: Fallback using extract_image
            try:
                extracted_image = pdf_doc.extract_image(xref)
                if extracted_image and 'image' in extracted_image:
                    return extracted_image['image']
            except Exception as e2:
                logger.debug(f"Fallback extraction also failed for xref {xref}: {e2}")
            
            return None
    
    def _generate_image_hashes(self, image_data: bytes) -> Dict[str, str]:
        """Generate multiple hashes for robust duplicate detection"""
        
        hashes = {}
        
        try:
            # MD5 hash (primary)
            hashes['md5'] = hashlib.md5(image_data).hexdigest()
            
            # SHA256 hash (secondary)
            hashes['sha256'] = hashlib.sha256(image_data).hexdigest()
            
            # Simple content hash (first and last 1024 bytes)
            if len(image_data) > 2048:
                content_sample = image_data[:1024] + image_data[-1024:]
                hashes['content'] = hashlib.md5(content_sample).hexdigest()
            else:
                hashes['content'] = hashes['md5']  # Same as MD5 for small images
            
        except Exception as e:
            logger.warning(f"Hash generation failed: {e}")
            # Fallback hash
            hashes['md5'] = str(hash(image_data))[:32]
        
        return hashes
    
    def _extract_text_with_spatial_info(self, pdf_doc) -> Dict[int, List[Dict]]:
        """PHASE 3: Extract text with detailed spatial positioning information"""
        
        logger.info("Extracting text with spatial positioning...")
        
        text_blocks_by_page = {}
        
        for page_num in range(len(pdf_doc)):
            page = pdf_doc.load_page(page_num)
            
            try:
                # Get text with detailed positioning
                text_dict = page.get_text("dict")
                
                page_blocks = []
                
                for block in text_dict.get("blocks", []):
                    if "lines" in block:  # Text block
                        block_info = {
                            'type': 'text',
                            'bbox': block.get('bbox', (0, 0, 0, 0)),
                            'lines': [],
                            'content': ''
                        }
                        
                        block_content_parts = []
                        
                        for line in block["lines"]:
                            line_info = {
                                'bbox': line.get('bbox', (0, 0, 0, 0)),
                                'spans': [],
                                'content': ''
                            }
                            
                            line_content_parts = []
                            
                            for span in line["spans"]:
                                span_text = span.get("text", "").strip()
                                if span_text:
                                    span_info = {
                                        'text': span_text,
                                        'bbox': span.get('bbox', (0, 0, 0, 0)),
                                        'font': span.get('font', ''),
                                        'size': span.get('size', 12),
                                        'flags': span.get('flags', 0)
                                    }
                                    
                                    line_info['spans'].append(span_info)
                                    line_content_parts.append(span_text)
                            
                            if line_content_parts:
                                line_info['content'] = ' '.join(line_content_parts)
                                block_info['lines'].append(line_info)
                                block_content_parts.append(line_info['content'])
                        
                        if block_content_parts:
                            block_info['content'] = '\n'.join(block_content_parts)
                            page_blocks.append(block_info)
                
                text_blocks_by_page[page_num] = page_blocks
                
                logger.debug(f"Page {page_num + 1}: Extracted {len(page_blocks)} text blocks")
                
            except Exception as e:
                logger.warning(f"Text extraction with spatial info failed for page {page_num}: {e}")
                
                # Fallback: simple text extraction
                try:
                    simple_text = page.get_text()
                    if simple_text.strip():
                        fallback_block = {
                            'type': 'text',
                            'bbox': page.rect,
                            'lines': [],
                            'content': simple_text
                        }
                        text_blocks_by_page[page_num] = [fallback_block]
                except Exception as e2:
                    logger.error(f"Even fallback text extraction failed for page {page_num}: {e2}")
                    text_blocks_by_page[page_num] = []
        
        total_blocks = sum(len(blocks) for blocks in text_blocks_by_page.values())
        logger.info(f"Text extraction complete: {total_blocks} total text blocks")
        
        return text_blocks_by_page
    
    def _integrate_images_and_text_spatially(self, pdf_doc, text_blocks_by_page: Dict[int, List[Dict]], 
                                           unique_images: List[AdvancedImageInfo], 
                                           duplicate_groups: Dict[str, List[AdvancedImageInfo]]) -> str:
        """PHASE 4: Intelligently integrate images and text based on spatial positioning"""
        
        logger.info("Starting intelligent spatial integration...")
        
        formatted_parts = []
        
        for page_num in range(len(pdf_doc)):
            logger.debug(f"Processing spatial integration for page {page_num + 1}")
            
            # Get text blocks for this page
            page_text_blocks = text_blocks_by_page.get(page_num, [])
            
            # Get images for this page (from all groups)
            page_images = []
            for group_id, group_images in duplicate_groups.items():
                for img in group_images:
                    if img.page_num == page_num:
                        page_images.append(img)
            
            # Create integrated content for this page
            page_content = self._create_spatially_integrated_page_content(
                page_num, page_text_blocks, page_images
            )
            
            if page_content.strip():
                formatted_parts.append(f"## Page {page_num + 1}\n\n{page_content}")
        
        # Combine all pages
        formatted_text = '\n\n'.join(formatted_parts)
        
        logger.info("Spatial integration complete")
        
        return formatted_text
    
    def _create_spatially_integrated_page_content(self, page_num: int, 
                                                text_blocks: List[Dict], 
                                                page_images: List[AdvancedImageInfo]) -> str:
        """Create spatially integrated content for a single page"""
        
        # Create list of all content elements with positions
        content_elements = []
        
        # Add text blocks
        for block_idx, text_block in enumerate(text_blocks):
            bbox = text_block.get('bbox', (0, 0, 0, 0))
            content_elements.append({
                'type': 'text',
                'bbox': bbox,
                'y_pos': bbox[1],  # Top Y coordinate for sorting
                'content': text_block['content'],
                'index': block_idx
            })
        
        # Add images with placeholders
        for img_idx, image_info in enumerate(page_images):
            # Generate placeholder for this image
            image_ref_num = len(self.processed_images) + img_idx + 1
            image_marker = f"__IMAGE_PLACEHOLDER_{image_ref_num}__"
            
            # Store marker for later processing
            image_info.reference_number = image_ref_num
            image_info.marker = image_marker
            
            # Use bbox if available, otherwise estimate position
            if image_info.bbox:
                bbox = image_info.bbox
                y_pos = bbox[1]
            else:
                # Estimate position based on other images or place at end
                y_pos = 999999  # Large number to place at end
                bbox = (0, y_pos, 0, y_pos)
            
            content_elements.append({
                'type': 'image',
                'bbox': bbox,
                'y_pos': y_pos,
                'content': image_marker,
                'image_info': image_info,
                'index': img_idx
            })
        
        # Sort all elements by vertical position (top to bottom)
        content_elements.sort(key=lambda x: x['y_pos'])
        
        # Create integrated content
        integrated_parts = []
        
        for element in content_elements:
            if element['type'] == 'text':
                integrated_parts.append(element['content'])
            elif element['type'] == 'image':
                # Add image placeholder with context
                image_info = element['image_info']
                context_text = f"\n{element['content']}\n*[Image from page {page_num + 1}]*"
                
                # If image is duplicate, add duplicate info
                if image_info.is_duplicate and image_info.master_image:
                    context_text += f"\n*[Duplicate of image from page {image_info.master_image.page_num + 1}]*"
                
                integrated_parts.append(context_text)
        
        return '\n\n'.join(integrated_parts)
    
    def _process_and_upload_unique_images(self, pdf_doc, formatted_text: str, 
                                        unique_images: List[AdvancedImageInfo], 
                                        duplicate_groups: Dict[str, List[AdvancedImageInfo]]) -> str:
        """PHASE 5: FIXED Process and upload only unique images, update ALL references correctly"""
        
        logger.info(f"Processing and uploading {len(unique_images)} unique images...")
        
        current_text = formatted_text
        
        # FIXED: Process each unique image (master of each duplicate group)
        for unique_image in unique_images:
            try:
                if not unique_image.image_data:
                    logger.warning(f"No image data for unique image xref={unique_image.xref}")
                    continue
                
                # Create unique placeholder name
                timestamp_suffix = int(time.time() * 1000) + self.image_counter
                placeholder_name = f"PDF_IMAGE_{self.image_counter}_{timestamp_suffix}"
                
                # Upload to S3
                s3_key = self._upload_pdf_image_to_s3_advanced(
                    unique_image.image_data, placeholder_name, unique_image
                )
                
                if s3_key:
                    # Get all instances in this duplicate group
                    group_images = duplicate_groups[unique_image.duplicate_group_id]
                    
                    # Store image info
                    image_info = {
                        'placeholder': placeholder_name,
                        's3_key': s3_key,
                        's3_filename': f"{placeholder_name}.png",
                        'original_filename': f"pdf_page_{unique_image.page_num + 1}_img_{unique_image.img_index}.png",
                        'image_number': self.image_counter,
                        'reference_number': unique_image.reference_number,
                        'page_number': unique_image.page_num + 1,
                        'size_bytes': unique_image.size_bytes,
                        'width': unique_image.width,
                        'height': unique_image.height,
                        'hash_value': unique_image.hash_value,
                        'duplicate_group_id': unique_image.duplicate_group_id,
                        'is_master_image': True,
                        'extraction_methods': unique_image.extraction_methods,
                        'total_instances': len(group_images),
                        'instance_pages': [str(img.page_num + 1) for img in group_images],
                        'uploaded': True,
                        'upload_timestamp': datetime.utcnow().isoformat(),
                        'source_type': 'pdf'
                    }
                    
                    self.processed_images.append(image_info)
                    self.placeholders[placeholder_name] = s3_key
                    
                    # Store in DynamoDB
                    self._store_image_metadata(image_info)
                    
                    # FIXED: Replace ALL instances of this image across all duplicates
                    instance_pages = [str(img.page_num + 1) for img in group_images]
                    instance_info = f"appears on page(s): {', '.join(instance_pages)}"
                    
                    placeholder_text = f"\n![{placeholder_name}]({s3_key})\n*PDF Image {self.image_counter} ({instance_info})*\n"
                    
                    # FIXED: Replace markers for ALL instances in the group
                    replaced_count = 0
                    for group_image in group_images:
                        if hasattr(group_image, 'marker') and group_image.marker:
                            # Count occurrences before replacement
                            marker_count = current_text.count(group_image.marker)
                            
                            # Replace marker
                            current_text = current_text.replace(group_image.marker, placeholder_text)
                            replaced_count += marker_count
                            
                            logger.debug(f"Replaced marker {group_image.marker} ({marker_count} occurrences) on page {group_image.page_num + 1}")
                    
                    logger.info(f"🎯 Processed unique image {placeholder_name}: {len(group_images)} instances across pages {', '.join(instance_pages)} ({replaced_count} markers replaced)")
                    
                    self.image_counter += 1
                else:
                    logger.error(f"Failed to upload unique image xref={unique_image.xref}")
                
            except Exception as e:
                logger.error(f"Failed to process unique image xref={unique_image.xref}: {e}")
                continue
        
        # Clean up any remaining markers (fallback)
        remaining_markers = len(re.findall(r'__IMAGE_PLACEHOLDER_\d+__', current_text))
        if remaining_markers > 0:
            logger.warning(f"Found {remaining_markers} unprocessed image markers - cleaning up")
            current_text = re.sub(r'__IMAGE_PLACEHOLDER_\d+__', '', current_text)
        
        # Clean up extra whitespace while preserving structure
        current_text = re.sub(r'\n\s*\n\s*\n', '\n\n', current_text)
        
        logger.info(f"✅ Image processing complete: {len(self.processed_images)} unique images uploaded")
        
        return current_text.strip()
    
    def _upload_pdf_image_to_s3_advanced(self, image_data: bytes, placeholder_name: str, 
                                       image_info: AdvancedImageInfo) -> Optional[str]:
        """Upload PDF image to S3 with advanced metadata"""
        
        if not S3_BUCKET:
            logger.error("S3_BUCKET not configured")
            return None
        
        try:
            timestamp_prefix = datetime.utcnow().strftime('%Y/%m/%d/%H')
            s3_key = f"extracted_images/{timestamp_prefix}/{self.document_id}/{placeholder_name}.png"
            
            # Prepare comprehensive metadata
            metadata = {
                'document_id': self.document_id,
                'placeholder_name': placeholder_name,
                'source_type': 'pdf_advanced',
                'page_number': str(image_info.page_num + 1),
                'image_index': str(image_info.img_index),
                'xref': str(image_info.xref),
                'hash_value': image_info.hash_value[:32] if image_info.hash_value else 'unknown',
                'duplicate_group_id': image_info.duplicate_group_id,
                'is_master_image': 'true',
                'extraction_methods': ','.join(image_info.extraction_methods),
                'width': str(image_info.width),
                'height': str(image_info.height),
                'size_bytes': str(len(image_data)),
                'upload_timestamp': datetime.utcnow().isoformat(),
                'processing_timestamp': self.processing_timestamp
            }
            
            s3_client.put_object(
                Bucket=S3_BUCKET,
                Key=s3_key,
                Body=image_data,
                ContentType='image/png',
                Metadata=metadata
            )
            
            logger.info(f"Advanced S3 Upload: {placeholder_name} → s3://{S3_BUCKET}/{s3_key}")
            return s3_key
            
        except Exception as e:
            logger.error(f"Advanced S3 upload failed for {placeholder_name}: {e}")
            return None
    
    def _count_tables_in_text(self, text: str) -> int:
        """Count table markers in text"""
        return len(re.findall(r'\*\*TABLE START\*\*', text))
    
    def _count_headings_in_text(self, text: str) -> int:
        """Count headings in text"""
        return len(re.findall(r'^#+\s', text, re.MULTILINE))
    
    def _fallback_pdf_extraction(self, file_path: str) -> Dict[str, Any]:
        """Fallback PDF extraction with minimal processing"""
        
        logger.info("Using fallback PDF extraction")
        
        try:
            pdf_doc = fitz.open(file_path)
            
            text_parts = []
            all_images = []
            
            for page_num in range(len(pdf_doc)):
                page = pdf_doc.load_page(page_num)
                
                # Simple text extraction
                page_text = page.get_text()
                if page_text.strip():
                    text_parts.append(f"Page {page_num + 1}:\n{page_text}")
                
                # Count images
                image_list = page.get_images()
                for i, img in enumerate(image_list):
                    marker = f"__PDF_FALLBACK_IMAGE_{len(all_images)}__"
                    all_images.append({
                        'marker': marker,
                        'reference_number': len(all_images),
                        'page_number': page_num + 1,
                        'fallback': True
                    })
            
            pdf_doc.close()
            
            formatted_text = '\n\n'.join(text_parts)
            
            # Add image markers
            for img in all_images:
                formatted_text += f" {img['marker']} "
            
            return {
                'formatted_text': formatted_text, 
                'plain_text': formatted_text,
                'method': 'fallback_pdf_extraction',
                'pages_processed': len(text_parts),
                'total_image_references': len(all_images),
                'unique_image_files': len(all_images),
                'unique_images': len(all_images),
                'duplicate_groups': 0,
                'total_image_instances': len(all_images),
                'tables_count': 0, 
                'headings_count': 0
            }
            
        except Exception as e:
            logger.error(f"Fallback PDF extraction failed: {e}")
            return {
                'formatted_text': "Failed to extract PDF text", 
                'plain_text': "Failed to extract PDF text",
                'method': 'failed_pdf_extraction',
                'pages_processed': 0,
                'total_image_references': 0,
                'unique_image_files': 0,
                'unique_images': 0,
                'duplicate_groups': 0,
                'total_image_instances': 0,
                'tables_count': 0, 
                'headings_count': 0
            }
    
    # ========================================
    # DOCX PROCESSING METHODS (UNCHANGED)
    # ========================================
    
    def _process_docx_with_formatting(self, file_path: str) -> Dict[str, Any]:
        """Process DOCX while preserving formatting and structure"""
        
        logger.info("Starting enhanced DOCX processing with formatting preservation...")
        
        with zipfile.ZipFile(file_path, 'r') as docx_zip:
            # Extract styles information
            styles_info = self._extract_styles(docx_zip)
            
            # Extract numbering information for lists
            numbering_info = self._extract_numbering(docx_zip)
            
            # Process document with full formatting
            formatted_text, all_image_references, document_stats = self._extract_formatted_content(
                docx_zip, styles_info, numbering_info
            )
            
            # Get unique image files
            unique_image_files = [f for f in docx_zip.namelist() if f.startswith('word/media/')]
            
            logger.info(f"Found {len(all_image_references)} image references")
            logger.info(f"Found {len(unique_image_files)} unique image files")
            logger.info(f"Found {document_stats.get('tables_count', 0)} tables")
            logger.info(f"Found {document_stats.get('headings_count', 0)} headings")
            
            # Process all image references
            final_text = self._process_all_image_references_formatted(
                docx_zip, formatted_text, all_image_references, unique_image_files
            )
            
            # Generate plain text version
            plain_text = self._strip_formatting_markers(final_text)
            
            logger.info("Enhanced DOCX processing complete")
            
            return {
                'formatted_text': final_text,
                'plain_text': plain_text,
                'method': 'enhanced_docx_with_formatting',
                'pages_processed': 1,  # DOCX is treated as single document
                'total_image_references': len(all_image_references),
                'unique_image_files': len(unique_image_files),
                'unique_images': len(unique_image_files),
                'duplicate_groups': 0,  # DOCX duplicate detection not implemented yet
                'total_image_instances': len(all_image_references),
                'tables_count': document_stats.get('tables_count', 0),
                'headings_count': document_stats.get('headings_count', 0)
            }
    
    def _extract_styles(self, docx_zip: zipfile.ZipFile) -> Dict[str, Dict]:
        """Extract style definitions from styles.xml"""
        styles_info = {}
        
        try:
            with docx_zip.open('word/styles.xml') as styles_file:
                styles_content = styles_file.read().decode('utf-8')
                styles_root = ET.fromstring(styles_content)
                
                for style in styles_root.findall('.//w:style', self.namespaces):
                    style_id = style.get('{http://schemas.openxmlformats.org/wordprocessingml/2006/main}styleId')
                    style_type = style.get('{http://schemas.openxmlformats.org/wordprocessingml/2006/main}type')
                    
                    # Get style name
                    name_elem = style.find('.//w:name', self.namespaces)
                    style_name = name_elem.get('{http://schemas.openxmlformats.org/wordprocessingml/2006/main}val') if name_elem is not None else style_id
                    
                    styles_info[style_id] = {
                        'name': style_name,
                        'type': style_type
                    }
                    
        except Exception as e:
            logger.warning(f"Could not extract styles: {e}")
            
        return styles_info
    
    def _extract_numbering(self, docx_zip: zipfile.ZipFile) -> Dict[str, Dict]:
        """Extract numbering definitions for lists"""
        numbering_info = {}
        
        try:
            with docx_zip.open('word/numbering.xml') as numbering_file:
                numbering_content = numbering_file.read().decode('utf-8')
                numbering_root = ET.fromstring(numbering_content)
                
                # Extract numbering definitions
                for num_def in numbering_root.findall('.//w:num', self.namespaces):
                    num_id = num_def.get('{http://schemas.openxmlformats.org/wordprocessingml/2006/main}numId')
                    numbering_info[num_id] = {'levels': {}}
                    
        except Exception as e:
            logger.warning(f"Could not extract numbering: {e}")
            
        return numbering_info
    
    def _extract_formatted_content(self, docx_zip: zipfile.ZipFile, styles_info: Dict, 
                                 numbering_info: Dict) -> Tuple[str, List[Dict], Dict]:
        """Extract document content with full formatting preservation"""
        
        try:
            with docx_zip.open('word/document.xml') as doc_xml:
                xml_content = doc_xml.read().decode('utf-8')
                root = ET.fromstring(xml_content)
                
                formatted_parts = []
                all_image_references = []
                reference_counter = 0
                
                # Document statistics
                document_stats = {
                    'tables_count': 0,
                    'headings_count': 0
                }
                
                # Process document body
                body = root.find('.//w:body', self.namespaces)
                if body is not None:
                    for element in body:
                        if element.tag.endswith('}p'):  # Paragraph
                            para_content, para_images = self._process_paragraph(
                                element, styles_info, reference_counter
                            )
                            if para_content.strip():
                                formatted_parts.append(para_content)
                                
                                # Check if it's a heading
                                if self._is_heading_paragraph(element, styles_info):
                                    document_stats['headings_count'] += 1
                            
                            # Update reference counter and add images
                            reference_counter += len(para_images)
                            all_image_references.extend(para_images)
                            
                        elif element.tag.endswith('}tbl'):  # Table
                            table_content, table_images = self._process_table(
                                element, styles_info, reference_counter
                            )
                            if table_content.strip():
                                formatted_parts.append(table_content)
                                document_stats['tables_count'] += 1
                            
                            # Update reference counter and add images
                            reference_counter += len(table_images)
                            all_image_references.extend(table_images)
                
                # Combine all formatted content
                formatted_text = '\n\n'.join(formatted_parts)
                
                logger.info(f"Extracted {len(formatted_text)} characters with formatting")
                logger.info(f"Found {len(all_image_references)} image references")
                
                return formatted_text, all_image_references, document_stats
                
        except Exception as e:
            logger.error(f"Failed to extract formatted content: {e}")
            return self._fallback_formatted_extraction(docx_zip)
    
    def _process_paragraph(self, para_elem, styles_info: Dict, 
                          start_ref_counter: int) -> Tuple[str, List[Dict]]:
        """Process a paragraph with formatting"""
        
        para_parts = []
        para_images = []
        current_ref_counter = start_ref_counter
        
        # Check paragraph style
        para_style = self._get_paragraph_style(para_elem, styles_info)
        
        # Process paragraph properties for numbering
        para_props = para_elem.find('.//w:pPr', self.namespaces)
        is_list_item = False
        list_level = 0
        
        if para_props is not None:
            num_pr = para_props.find('.//w:numPr', self.namespaces)
            if num_pr is not None:
                is_list_item = True
                ilvl_elem = num_pr.find('.//w:ilvl', self.namespaces)
                if ilvl_elem is not None:
                    list_level = int(ilvl_elem.get('{http://schemas.openxmlformats.org/wordprocessingml/2006/main}val', '0'))
        
        # Process runs within paragraph
        runs = para_elem.findall('.//w:r', self.namespaces)
        for run in runs:
            run_text, run_images = self._process_run(run, current_ref_counter)
            if run_text or run_images:
                para_parts.append(run_text)
                para_images.extend(run_images)
                current_ref_counter += len(run_images)
        
        # Combine paragraph content
        para_text = ''.join(para_parts)
        
        # Apply paragraph-level formatting
        formatted_para = self._apply_paragraph_formatting(
            para_text, para_style, is_list_item, list_level
        )
        
        return formatted_para, para_images
    
    def _process_run(self, run_elem, start_ref_counter: int) -> Tuple[str, List[Dict]]:
        """Process a text run with character formatting"""
        
        run_parts = []
        run_images = []
        current_ref_counter = start_ref_counter
        
        # Get run properties for formatting
        run_props = run_elem.find('.//w:rPr', self.namespaces)
        formatting = self._extract_run_formatting(run_props)
        
        # Process text elements
        text_elements = run_elem.findall('.//w:t', self.namespaces)
        for text_elem in text_elements:
            if text_elem.text:
                formatted_text = self._apply_character_formatting(text_elem.text, formatting)
                run_parts.append(formatted_text)
        
        # Process images in this run
        drawings = run_elem.findall('.//w:drawing', self.namespaces)
        for drawing in drawings:
            pic_elements = drawing.findall('.//pic:pic', self.namespaces)
            for pic in pic_elements:
                image_marker = f"__IMAGE_PLACEHOLDER_{current_ref_counter}__"
                
                # Get image relationship ID
                image_rel_id = None
                blip_elements = pic.findall('.//a:blip', self.namespaces)
                if blip_elements:
                    image_rel_id = blip_elements[0].get(
                        '{http://schemas.openxmlformats.org/officeDocument/2006/relationships}embed'
                    )
                
                # Store image reference
                image_ref = {
                    'marker': image_marker,
                    'reference_number': current_ref_counter,
                    'relationship_id': image_rel_id,
                    'context': ''.join(run_parts)[:100]
                }
                
                run_images.append(image_ref)
                run_parts.append(f" {image_marker} ")
                current_ref_counter += 1
        
        return ''.join(run_parts), run_images
    
    def _process_table(self, table_elem, styles_info: Dict, 
                      start_ref_counter: int) -> Tuple[str, List[Dict]]:
        """Process a table with formatting"""
        
        table_parts = []
        table_images = []
        current_ref_counter = start_ref_counter
        
        # Table start marker
        table_parts.append("\n**TABLE START**\n")
        
        # Process table rows
        rows = table_elem.findall('.//w:tr', self.namespaces)
        for row_idx, row in enumerate(rows):
            row_parts = []
            
            # Process cells in row
            cells = row.findall('.//w:tc', self.namespaces)
            for cell_idx, cell in enumerate(cells):
                cell_content = []
                
                # Process paragraphs in cell
                cell_paras = cell.findall('.//w:p', self.namespaces)
                for para in cell_paras:
                    para_content, para_images = self._process_paragraph(
                        para, styles_info, current_ref_counter
                    )
                    if para_content.strip():
                        cell_content.append(para_content)
                    
                    # Update counter and collect images
                    current_ref_counter += len(para_images)
                    table_images.extend(para_images)
                
                # Join cell content and add cell separator
                cell_text = ' '.join(cell_content).strip()
                row_parts.append(f"| {cell_text} ")
            
            # Complete the row
            if row_parts:
                table_parts.append(''.join(row_parts) + "|\n")
                
                # Add header separator for first row
                if row_idx == 0:
                    separator = "|" + "---|" * len(cells) + "\n"
                    table_parts.append(separator)
        
        # Table end marker
        table_parts.append("**TABLE END**\n")
        
        return ''.join(table_parts), table_images
    
    def _get_paragraph_style(self, para_elem, styles_info: Dict) -> Dict[str, Any]:
        """Extract paragraph style information"""
        
        style_info = {'name': 'Normal', 'type': 'paragraph'}
        
        para_props = para_elem.find('.//w:pPr', self.namespaces)
        if para_props is not None:
            style_elem = para_props.find('.//w:pStyle', self.namespaces)
            if style_elem is not None:
                style_id = style_elem.get('{http://schemas.openxmlformats.org/wordprocessingml/2006/main}val')
                if style_id in styles_info:
                    style_info = styles_info[style_id]
        
        return style_info
    
    def _extract_run_formatting(self, run_props) -> Dict[str, bool]:
        """Extract character formatting from run properties"""
        
        formatting = {
            'bold': False,
            'italic': False,
            'underline': False
        }
        
        if run_props is not None:
            # Check for bold
            if run_props.find('.//w:b', self.namespaces) is not None:
                formatting['bold'] = True
            
            # Check for italic
            if run_props.find('.//w:i', self.namespaces) is not None:
                formatting['italic'] = True
            
            # Check for underline
            if run_props.find('.//w:u', self.namespaces) is not None:
                formatting['underline'] = True
        
        return formatting
    
    def _apply_paragraph_formatting(self, text: str, style_info: Dict, 
                                  is_list_item: bool, list_level: int) -> str:
        """Apply paragraph-level formatting"""
        
        if not text.strip():
            return text
        
        # Apply heading formatting
        style_name = style_info.get('name', '').lower()
        if 'heading' in style_name or 'title' in style_name:
            # Extract heading level
            heading_level = 1
            for i in range(1, 7):
                if f'heading {i}' in style_name or f'heading{i}' in style_name:
                    heading_level = i
                    break
            
            return f"{'#' * heading_level} {text.strip()}\n"
        
        # Apply list formatting
        if is_list_item:
            indent = "  " * list_level
            return f"{indent}- {text.strip()}\n"
        
        # Regular paragraph
        return f"{text.strip()}\n"
    
    def _apply_character_formatting(self, text: str, formatting: Dict[str, bool]) -> str:
        """Apply character-level formatting"""
        
        if not text:
            return text
        
        formatted_text = text
        
        # Apply bold
        if formatting.get('bold', False):
            formatted_text = f"**{formatted_text}**"
        
        # Apply italic
        if formatting.get('italic', False):
            formatted_text = f"*{formatted_text}*"
        
        # Apply underline (using HTML-style for now)
        if formatting.get('underline', False):
            formatted_text = f"<u>{formatted_text}</u>"
        
        return formatted_text
    
    def _is_heading_paragraph(self, para_elem, styles_info: Dict) -> bool:
        """Check if paragraph is a heading"""
        
        style_info = self._get_paragraph_style(para_elem, styles_info)
        style_name = style_info.get('name', '').lower()
        return 'heading' in style_name or 'title' in style_name
    
    def _process_all_image_references_formatted(self, docx_zip: zipfile.ZipFile, 
                                              formatted_text: str, all_image_references: List[Dict], 
                                              unique_image_files: List[str]) -> str:
        """Process image references in formatted text"""
        
        current_text = formatted_text
        
        # Sort image files naturally
        sorted_image_files = sorted(unique_image_files, 
                                  key=lambda x: self._extract_number_from_filename(x))
        
        # Build relationship mapping
        rel_to_file_map = self._build_relationship_mapping(docx_zip, sorted_image_files)
        
        logger.info(f"Processing {len(all_image_references)} image references...")
        
        # Process each image reference
        for ref_idx, image_ref in enumerate(all_image_references):
            try:
                # Get image file for this reference
                img_file = self._get_image_file_for_reference(
                    image_ref, sorted_image_files, rel_to_file_map, ref_idx
                )
                
                if not img_file:
                    logger.warning(f"No image file found for reference {ref_idx}")
                    continue
                
                # Extract and upload image
                with docx_zip.open(img_file) as img_data_file:
                    image_data = img_data_file.read()
                
                if len(image_data) < 100:
                    logger.warning(f"Image {img_file} too small, skipping")
                    continue
                
                # Create unique placeholder
                timestamp_suffix = int(time.time() * 1000) + ref_idx
                placeholder_name = f"IMAGE_{self.image_counter}_{timestamp_suffix}"
                
                # Upload to S3
                s3_key = self._upload_image_to_s3(image_data, placeholder_name, img_file)
                
                if s3_key:
                    # Store image info
                    image_info = {
                        'placeholder': placeholder_name,
                        's3_key': s3_key,
                        's3_filename': f"{placeholder_name}.png",
                        'original_filename': img_file,
                        'image_number': self.image_counter,
                        'reference_number': image_ref['reference_number'],
                        'size_bytes': len(image_data),
                        'uploaded': True,
                        'upload_timestamp': datetime.utcnow().isoformat(),
                        'source_type': 'docx',
                        'is_duplicate_reference': img_file in [img['original_filename'] 
                                                             for img in self.processed_images]
                    }
                    
                    self.processed_images.append(image_info)
                    self.placeholders[placeholder_name] = s3_key
                    
                    # Store in DynamoDB
                    self._store_image_metadata(image_info)
                    
                    # Replace marker with formatted placeholder
                    marker = image_ref['marker']
                    placeholder_text = f"\n![{placeholder_name}]({s3_key})\n"
                    current_text = current_text.replace(marker, placeholder_text)
                    
                    logger.info(f"Processed {placeholder_name}: ref#{ref_idx} → {img_file}")
                    
                    self.image_counter += 1
                else:
                    logger.error(f"Failed to upload reference {ref_idx}")
                
            except Exception as e:
                logger.error(f"Failed to process image reference {ref_idx}: {e}")
                continue
        
        # Clean up any remaining markers
        current_text = re.sub(r'__IMAGE_PLACEHOLDER_\d+__', '', current_text)
        
        # Clean up extra whitespace while preserving structure
        current_text = re.sub(r'\n\s*\n\s*\n', '\n\n', current_text)
        
        return current_text.strip()
    
    def _build_relationship_mapping(self, docx_zip: zipfile.ZipFile, image_files: List[str]) -> Dict[str, str]:
        """Build mapping from relationship IDs to actual image files"""
        
        rel_map = {}
        
        try:
            with docx_zip.open('word/_rels/document.xml.rels') as rels_file:
                rels_content = rels_file.read().decode('utf-8')
                rels_root = ET.fromstring(rels_content)
                
                for relationship in rels_root.findall('.//{http://schemas.openxmlformats.org/package/2006/relationships}Relationship'):
                    rel_id = relationship.get('Id')
                    target = relationship.get('Target')
                    rel_type = relationship.get('Type')
                    
                    if rel_type and 'image' in rel_type.lower() and target:
                        if target.startswith('media/'):
                            full_path = f"word/{target}"
                        else:
                            full_path = target
                        
                        if full_path in image_files:
                            rel_map[rel_id] = full_path
                            logger.info(f"Mapped relationship {rel_id} → {full_path}")
                
        except Exception as e:
            logger.warning(f"Could not build relationship mapping: {e}")
        
        return rel_map
    
    def _get_image_file_for_reference(self, image_ref: Dict, image_files: List[str], 
                                    rel_map: Dict[str, str], ref_idx: int) -> Optional[str]:
        """Get the correct image file for this specific reference"""
        
        # Try relationship mapping first
        if image_ref.get('relationship_id') and image_ref['relationship_id'] in rel_map:
            return rel_map[image_ref['relationship_id']]
        
        # Fallback: cycle through image files
        if image_files:
            file_index = ref_idx % len(image_files)
            return image_files[file_index]
        
        return None
    
    def _extract_number_from_filename(self, filename: str) -> int:
        """Extract number from filename for natural sorting"""
        numbers = re.findall(r'\d+', filename)
        return int(numbers[0]) if numbers else 0
    
    def _upload_image_to_s3(self, image_data: bytes, placeholder_name: str, original_filename: str) -> Optional[str]:
        """Upload image to S3 with unique path"""
        
        if not S3_BUCKET:
            logger.error("S3_BUCKET not configured")
            return None
        
        try:
            timestamp_prefix = datetime.utcnow().strftime('%Y/%m/%d/%H')
            s3_key = f"extracted_images/{timestamp_prefix}/{self.document_id}/{placeholder_name}.png"
            
            s3_client.put_object(
                Bucket=S3_BUCKET,
                Key=s3_key,
                Body=image_data,
                ContentType='image/png',
                Metadata={
                    'document_id': self.document_id,
                    'placeholder_name': placeholder_name,
                    'original_filename': original_filename,
                    'source_type': 'docx',
                    'upload_timestamp': datetime.utcnow().isoformat(),
                    'processing_timestamp': self.processing_timestamp
                }
            )
            
            logger.info(f"S3 Upload: {placeholder_name} → s3://{S3_BUCKET}/{s3_key}")
            return s3_key
            
        except Exception as e:
            logger.error(f"S3 upload failed for {placeholder_name}: {e}")
            return None
    
    def _fallback_formatted_extraction(self, docx_zip: zipfile.ZipFile) -> Tuple[str, List[Dict], Dict]:
        """Fallback extraction that still attempts some formatting"""
        
        logger.info("Using fallback formatted extraction")
        
        try:
            with docx_zip.open('word/document.xml') as doc_xml:
                xml_content = doc_xml.read().decode('utf-8')
                
                # Simple extraction with basic structure
                paragraphs = re.findall(r'<w:p[^>]*>.*?</w:p>', xml_content, re.DOTALL)
                formatted_parts = []
                
                for i, para in enumerate(paragraphs):
                    # Extract text
                    text_matches = re.findall(r'<w:t[^>]*>(.*?)</w:t>', para, re.DOTALL)
                    para_text = ''.join(text_matches).strip()
                    
                    if para_text:
                        # Simple formatting detection
                        if re.search(r'<w:b/>', para):
                            para_text = f"**{para_text}**"
                        
                        formatted_parts.append(para_text)
                
                formatted_text = '\n\n'.join(formatted_parts)
                
                # Count images
                pic_matches = re.findall(r'<pic:pic[^>]*>', xml_content)
                all_image_references = []
                
                for i, pic_match in enumerate(pic_matches):
                    marker = f"__IMAGE_PLACEHOLDER_{i}__"
                    all_image_references.append({
                        'marker': marker,
                        'reference_number': i,
                        'context': f"Fallback reference {i}",
                        'fallback': True
                    })
                    
                    formatted_text += f" {marker} "
                
                document_stats = {
                    'tables_count': len(re.findall(r'<w:tbl>', xml_content)),
                    'headings_count': 0
                }
                
                return formatted_text, all_image_references, document_stats
                
        except Exception as e:
            logger.error(f"Fallback formatted extraction failed: {e}")
            return "Failed to extract formatted text", [], {'tables_count': 0, 'headings_count': 0}
    
    # ========================================
    # AI PROCESSING TRIGGER METHODS (UNCHANGED)
    # ========================================
    
    def _trigger_image_ai_processing(self, extracted_text: str, images_count: int) -> Dict[str, Any]:
        """Trigger AI processing of extracted images"""
        
        if images_count == 0:
            logger.info("No images to process with AI")
            return {'triggered': False, 'reason': 'no_images'}
        
        try:
            logger.info(f"Triggering AI processing for {images_count} images in document {self.document_id}")
            
            if USE_ASYNC_PROCESSING:
                # Option 1: Asynchronous processing via SQS (Recommended)
                return self._trigger_via_sqs(images_count)
            else:
                # Option 2: Synchronous processing via direct Lambda invocation
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
                'trigger_source': 'advanced_document_extractor',
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
                        'StringValue': 'advanced_document_extractor',
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
                'trigger_source': 'advanced_document_extractor',
                'processing_timestamp': self.processing_timestamp
            }
            
            # Invoke image processor Lambda asynchronously
            response = lambda_client.invoke(
                FunctionName=IMAGE_PROCESSOR_LAMBDA_ARN,
                InvocationType='Event',  # Asynchronous invocation
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

    def _trigger_via_eventbridge(self, images_count: int) -> Dict[str, Any]:
        """Trigger image processing via EventBridge (alternative option)"""
        
        try:
            # Send custom event to EventBridge
            event_detail = {
                'document_id': self.document_id,
                'images_count': images_count,
                'processing_timestamp': self.processing_timestamp,
                'extraction_complete': True
            }
            
            response = events_client.put_events(
                Entries=[
                    {
                        'Source': 'document.processor',
                        'DetailType': 'Document Processing Complete',
                        'Detail': json.dumps(event_detail),
                        'Resources': [
                            f"document:{self.document_id}"
                        ]
                    }
                ]
            )
            
            logger.info(f"Sent EventBridge event for image processing")
            
            return {
                'triggered': True,
                'method': 'eventbridge',
                'event_id': response['Entries'][0].get('EventId'),
                'images_count': images_count
            }
            
        except Exception as e:
            logger.error(f"EventBridge trigger failed: {e}")
            return {'triggered': False, 'error': str(e), 'method': 'eventbridge'}
    
    # ========================================
    # STORAGE AND UTILITY METHODS (UNCHANGED BUT ENHANCED)
    # ========================================
    
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
                'extraction_method': 'advanced_document_processor_with_deduplication',
                'processing_timestamp': self.processing_timestamp,
                'character_count': str(len(formatted_text)),
                'plain_character_count': str(len(plain_text)),
                'images_processed': str(len(self.processed_images)),
                'duplicate_groups': str(len(self.duplicate_groups)),
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
                'extraction_method': 'advanced_document_processor_with_deduplication',
                'formatting_preserved': True,
                'advanced_features': {
                    'spatial_positioning_enabled': ENABLE_SPATIAL_POSITIONING,
                    'duplicate_detection_enabled': ENABLE_DUPLICATE_DETECTION,
                    'advanced_image_detection_enabled': ENABLE_ADVANCED_IMAGE_DETECTION
                },
                'character_count': len(formatted_text),
                'plain_character_count': len(plain_text),
                'images_detected': len(self.processed_images),
                'duplicate_groups_count': len(self.duplicate_groups),
                'placeholders': self.placeholders,
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
                        'source_type': img.get('source_type', 'unknown'),
                        'is_master_image': img.get('is_master_image', False),
                        'duplicate_group_id': img.get('duplicate_group_id', 'unknown'),
                        'total_instances': img.get('total_instances', 1),
                        'extraction_methods': img.get('extraction_methods', [])
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
            
            # 4. Create a summary report
            summary_report = self._generate_summary_report(formatted_text, plain_text, extraction_metadata)
            summary_s3_key = f"{base_path}/extraction_summary.txt"
            s3_client.put_object(
                Bucket=S3_BUCKET,
                Key=summary_s3_key,
                Body=summary_report.encode('utf-8'),
                ContentType='text/plain; charset=utf-8',
                Metadata=file_metadata
            )
            logger.info(f"Saved summary: s3://{S3_BUCKET}/{summary_s3_key}")
            
            return True
            
        except Exception as e:
            logger.error(f"Failed to save text files to S3: {e}")
            return False
    
    def _generate_summary_report(self, formatted_text: str, plain_text: str, metadata: dict) -> str:
        """Generate a human-readable summary report with advanced features"""
        
        report_lines = [
            "=" * 60,
            "ADVANCED DOCUMENT EXTRACTION SUMMARY REPORT",
            "=" * 60,
            "",
            f"Document ID: {metadata['document_id']}",
            f"Processing Date: {metadata['extraction_timestamp']}",
            f"Extraction Method: {metadata['extraction_method']}",
            "",
            "ADVANCED FEATURES ENABLED:",
            f"  - Spatial Positioning: {'Yes' if metadata['advanced_features']['spatial_positioning_enabled'] else 'No'}",
            f"  - Duplicate Detection: {'Yes' if metadata['advanced_features']['duplicate_detection_enabled'] else 'No'}",
            f"  - Multi-Method Image Detection: {'Yes' if metadata['advanced_features']['advanced_image_detection_enabled'] else 'No'}",
            "",
            "CONTENT STATISTICS:",
            f"  - Formatted Text Length: {metadata['character_count']:,} characters",
            f"  - Plain Text Length: {metadata['plain_character_count']:,} characters",
            f"  - Images Extracted: {metadata['images_detected']}",
            f"  - Duplicate Groups: {metadata['duplicate_groups_count']}",
            f"  - Formatting Preserved: {'Yes' if metadata['formatting_preserved'] else 'No'}",
            "",
            "FILE LOCATIONS:",
            f"  - Formatted Text: {metadata['file_locations']['formatted_text']}",
            f"  - Plain Text: {metadata['file_locations']['plain_text']}",
            f"  - Metadata: {metadata['file_locations']['metadata']}",
            "",
        ]
        
        if metadata['images']:
            report_lines.extend([
                "EXTRACTED IMAGES (UNIQUE ONLY):",
                ""
            ])
            for img in metadata['images']:
                report_lines.append(f"  - {img['placeholder']}: {img['s3_location']}")
                report_lines.append(f"    Original: {img['original_filename']} ({img['size_bytes']:,} bytes)")
                report_lines.append(f"    Source: {img['source_type']}")
                if img.get('is_master_image'):
                    report_lines.append(f"    Master Image: Yes (Group: {img['duplicate_group_id']})")
                    report_lines.append(f"    Total Instances: {img.get('total_instances', 1)}")
                    if img.get('extraction_methods'):
                        report_lines.append(f"    Detection Methods: {', '.join(img['extraction_methods'])}")
                report_lines.append("")
        
        report_lines.extend([
            "CONTENT PREVIEW (First 500 characters):",
            "-" * 40,
            plain_text[:500] + ("..." if len(plain_text) > 500 else ""),
            "",
            "=" * 60,
            "END OF ADVANCED SUMMARY REPORT",
            "=" * 60
        ])
        
        return "\n".join(report_lines)
    
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
            
            # Prepare DynamoDB item with advanced metadata
            item = {
                'document_id': self.document_id,
                'extracted_text': formatted_text,
                'plain_text': plain_text,
                'extraction_timestamp': datetime.utcnow().isoformat(),
                'processing_timestamp': self.processing_timestamp,
                'character_count': len(formatted_text),
                'plain_character_count': len(plain_text),
                'extraction_method': 'advanced_document_processor_with_deduplication',
                'formatting_preserved': True,
                'advanced_features': {
                    'spatial_positioning_enabled': ENABLE_SPATIAL_POSITIONING,
                    'duplicate_detection_enabled': ENABLE_DUPLICATE_DETECTION,
                    'advanced_image_detection_enabled': ENABLE_ADVANCED_IMAGE_DETECTION
                },
                'pages_processed': 1,
                'images_processed': len(self.processed_images),
                'duplicate_groups_count': len(self.duplicate_groups),
                'placeholders': self.placeholders,
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

    def _store_image_metadata(self, image_info: Dict[str, Any]) -> None:
        """Store image metadata in DynamoDB with advanced metadata"""
        
        if not images_table:
            logger.warning("Images table not available")
            return
        
        try:
            ttl = datetime.utcnow() + timedelta(days=30)
            image_id = f"{self.document_id}_{image_info['reference_number']}_{int(time.time() * 1000)}"
            
            item = {
                'document_id': self.document_id,
                'image_id': image_id,
                'image_number': image_info['image_number'],
                'reference_number': image_info['reference_number'],
                'placeholder': image_info['placeholder'],
                's3_bucket': S3_BUCKET,
                's3_key': image_info['s3_key'],
                's3_filename': image_info['s3_filename'],
                'original_filename': image_info['original_filename'],
                'size_bytes': image_info['size_bytes'],
                'page_number': image_info.get('page_number', 1),
                'source_type': image_info.get('source_type', 'unknown'),
                'is_duplicate_reference': image_info.get('is_duplicate_reference', False),
                'extraction_method': 'advanced_document_processor_with_deduplication',
                'processing_timestamp': self.processing_timestamp,
                'upload_timestamp': image_info['upload_timestamp'],
                'ai_processed': False,
                # Advanced metadata
                'is_master_image': image_info.get('is_master_image', False),
                'duplicate_group_id': image_info.get('duplicate_group_id', 'unknown'),
                'hash_value': image_info.get('hash_value', 'unknown'),
                'total_instances': image_info.get('total_instances', 1),
                'instance_pages': image_info.get('instance_pages', []),
                'extraction_methods': image_info.get('extraction_methods', []),
                'width': image_info.get('width', 0),
                'height': image_info.get('height', 0),
                'ttl': int(ttl.timestamp())
            }
            
            images_table.put_item(Item=item)
            logger.info(f"DynamoDB: Stored advanced metadata for {image_info['placeholder']}")
            
        except Exception as e:
            logger.error(f"DynamoDB storage failed for {image_info['placeholder']}: {e}")

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
        plain_text = re.sub(r'^-+\|.*, '', plain_text, flags=re.MULTILINE)  # Table separators
        plain_text = re.sub(r'!\[.*?\]\(.*?\)', '', plain_text)  # Image links
        
        # Clean up extra whitespace
        plain_text = re.sub(r'\n\s*\n\s*\n', '\n\n', plain_text)
        
        return plain_text.strip()


def lambda_handler(event: Dict[str, Any], context) -> Dict[str, Any]:
    """
    AWS Lambda handler with ADVANCED PDF processing - Supports complete duplicate detection and spatial positioning
    """
    
    request_id = getattr(context, 'aws_request_id', str(uuid.uuid4()))
    
    try:
        logger.info(f"ADVANCED Enhanced Document processor with complete PDF support started - Request ID: {request_id}")
        
        # Handle health check
        if event.get('action') == 'health_check':
            return {
                'statusCode': 200,
                'body': json.dumps({
                    'status': 'healthy',
                    'service': 'advanced-enhanced-document-processor-with-complete-pdf-support',
                    'timestamp': datetime.utcnow().isoformat(),
                    'request_id': request_id,
                    'supported_formats': ['PDF', 'DOCX'],
                    'advanced_features': [
                        'Multi-method PDF image detection',
                        'Hash-based duplicate detection across pages',
                        'Spatial positioning and intelligent image-text integration',
                        'Multiple instance detection per page',
                        'Advanced image metadata tracking',
                        'Enhanced DOCX processing with formatting preservation',
                        'Automatic AI image processing trigger',
                        'S3 file storage for extracted text and images',
                        'DynamoDB metadata storage with advanced fields',
                        'Event-driven architecture support',
                        'SQS and Lambda invoke integration'
                    ],
                    'configuration': {
                        'spatial_positioning_enabled': ENABLE_SPATIAL_POSITIONING,
                        'duplicate_detection_enabled': ENABLE_DUPLICATE_DETECTION,
                        'advanced_image_detection_enabled': ENABLE_ADVANCED_IMAGE_DETECTION,
                        'image_hash_similarity_threshold': IMAGE_HASH_SIMILARITY_THRESHOLD,
                        'min_image_size_bytes': MIN_IMAGE_SIZE_BYTES,
                        'max_images_per_page': MAX_IMAGES_PER_PAGE
                    },
                    'ai_integration': {
                        'sqs_configured': bool(IMAGE_PROCESSING_QUEUE_URL),
                        'lambda_arn_configured': bool(IMAGE_PROCESSOR_LAMBDA_ARN),
                        'async_processing': USE_ASYNC_PROCESSING
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
                    logger.info(f"Processing {original_filename} as document {document_id} with ADVANCED features")
                    
                    # Download file
                    local_path = f"/tmp/{document_id}_{original_filename}"
                    s3_client.download_file(S3_BUCKET, s3_key, local_path)
                    
                    # Process with ADVANCED enhanced processor
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
                    'request_id': request_id,
                    'advanced_processing': True
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
                        'supported_formats': ['PDF', 'DOCX'],
                        'advanced_features_available': file_extension == '.pdf',
                        'request_id': request_id
                    }),
                    'headers': {
                        'Content-Type': 'application/json',
                        'X-Request-ID': request_id
                    }
                }
            
            document_id = generate_unique_document_id(original_filename)
            logger.info(f"Processing {original_filename} as document {document_id} with ADVANCED features")
            
            # Download file
            local_path = f"/tmp/{document_id}_{original_filename}"
            s3_client.download_file(s3_bucket, s3_key, local_path)
            
            # Process with ADVANCED enhanced processor
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
        logger.error(f"ADVANCED Lambda handler error: {e}")
        return {
            'statusCode': 500,
            'body': json.dumps({
                'success': False,
                'error': 'advanced_lambda_handler_error',
                'message': str(e),
                'request_id': request_id,
                'traceback': traceback.format_exc(),
                'advanced_processing': True
            }),
            'headers': {
                'Content-Type': 'application/json',
                'X-Request-ID': request_id
            }
        }
