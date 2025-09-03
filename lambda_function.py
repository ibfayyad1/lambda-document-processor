"""
Complete Integrated Document Processor with Auto AI Image Processing
Extracts text/images from DOCX files and automatically triggers AI analysis
(Updated: adds PDF pipeline via PyMuPDF with exact placeholders and metadata)
"""

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
from typing import Dict, Any, List, Optional, Tuple
from pathlib import Path
from decimal import Decimal
from datetime import datetime, timedelta

# --- PDF support
try:
    import fitz  # PyMuPDF
except Exception:
    fitz = None

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
    """Enhanced processor that preserves document formatting and triggers AI processing"""
    
    def __init__(self, document_id: str):
        self.document_id = document_id
        self.placeholders = {}
        self.processed_images = []
        self.image_counter = 1
        self.processing_timestamp = datetime.utcnow().isoformat()
        self.namespaces = {
            'w': 'http://schemas.openxmlformats.org/wordprocessingml/2006/main',
            'pic': 'http://schemas.openxmlformats.org/drawingml/2006/picture',
            'a': 'http://schemas.openxmlformats.org/drawingml/2006/main',
            'r': 'http://schemas.openxmlformats.org/officeDocument/2006/relationships',
            'wp': 'http://schemas.openxmlformats.org/drawingml/2006/wordprocessingDrawing'
        }
        
    def process_document(self, file_path: str) -> Dict[str, Any]:
        """Main processing method with formatting preservation and AI trigger"""
        start_time = time.time()
        
        try:
            logger.info(f"Starting enhanced processing for {self.document_id}")
            
            # Validate file
            if not os.path.exists(file_path):
                raise Exception(f"File not found: {file_path}")
            
            file_size = os.path.getsize(file_path)
            if file_size > MAX_FILE_SIZE:
                raise Exception(f"File too large: {file_size} bytes")
            
            # Process per file type
            if file_path.lower().endswith('.docx'):
                result = self._process_docx_with_formatting(file_path)
            elif file_path.lower().endswith('.pdf'):
                result = self._process_pdf_with_pymupdf(file_path)  # NEW: PDF support
            else:
                raise Exception(f"Unsupported file type")
            
            processing_time = time.time() - start_time
            
            # Validate extracted text (keep same behavior as before)
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

            # TRIGGER IMAGE AI PROCESSING (updated to send per-image metadata)
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
                'extraction_method': result.get('method', 'enhanced_docx_with_formatting'),
                'pages_processed': 1,
                'images_detected': result.get('total_image_references', 0),
                'unique_image_files': result.get('unique_image_files', 0),
                'images_extracted': len(self.processed_images),
                'images_uploaded': len([img for img in self.processed_images if img.get('uploaded')]),
                'tables_detected': result.get('tables_count', 0),
                'headings_detected': result.get('headings_count', 0),
                'formatting_preserved': True,
                'files_saved_to_s3': True,
                'output_files': file_locations,
                's3_base_path': f"s3://{S3_BUCKET}/{base_path}/",
                'placeholder_pdf_s3': result.get('placeholder_pdf_s3'),  # NEW for PDF
                'ai_processing': ai_trigger_result,  # AI processing trigger info
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
                'extraction_method': 'enhanced_docx_with_formatting',
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
    
    def _trigger_image_ai_processing(self, extracted_text: str, images_count: int) -> Dict[str, Any]:
        """Trigger AI processing of extracted images – now sends full image metadata."""
        if images_count == 0:
            logger.info("No images to process with AI")
            return {'triggered': False, 'reason': 'no_images'}

        payload_images = [{
            'placeholder': img.get('placeholder'),
            's3_bucket': S3_BUCKET,
            's3_key': img.get('s3_key'),
            'page_number': img.get('page_number'),
            'sequence_in_page': img.get('sequence_in_page'),
            'bbox': img.get('bbox'),                 # {x0,y0,x1,y1}
            'bbox_norm': img.get('bbox_norm'),       # normalized to page size
            'page_size': img.get('page_size'),       # {width,height}
            'ext': img.get('ext'),
            'original_filename': img.get('original_filename'),
        } for img in self.processed_images]

        try:
            logger.info(f"Triggering AI processing for {images_count} images in document {self.document_id}")
            message_body = {
                'document_id': self.document_id,
                'images_count': images_count,
                'processing_timestamp': self.processing_timestamp,
                'trigger_timestamp': datetime.utcnow().isoformat(),
                'images': payload_images,
                's3_base_path': f"s3://{S3_BUCKET}/document_extractions/{datetime.utcnow().strftime('%Y/%m/%d')}/{self.document_id}/",
                'trigger_source': 'document_extractor',
                'text_excerpt_first_2k': extracted_text[:2000] if extracted_text else ""
            }

            if USE_ASYNC_PROCESSING:
                if not IMAGE_PROCESSING_QUEUE_URL:
                    logger.warning("IMAGE_PROCESSING_QUEUE_URL not configured")
                    return {'triggered': False, 'reason': 'sqs_not_configured'}
                response = sqs_client.send_message(
                    QueueUrl=IMAGE_PROCESSING_QUEUE_URL,
                    MessageBody=json.dumps(message_body),
                    MessageAttributes={
                        'DocumentId': {'StringValue': self.document_id, 'DataType': 'String'},
                        'ImagesCount': {'StringValue': str(images_count), 'DataType': 'Number'},
                        'TriggerSource': {'StringValue': 'document_extractor', 'DataType': 'String'}
                    }
                )
                return {'triggered': True, 'method': 'sqs', 'message_id': response['MessageId'], 'images_count': images_count}
            else:
                if not IMAGE_PROCESSOR_LAMBDA_ARN:
                    logger.warning("IMAGE_PROCESSOR_LAMBDA_ARN not configured")
                    return {'triggered': False, 'reason': 'lambda_arn_not_configured'}
                resp = lambda_client.invoke(
                    FunctionName=IMAGE_PROCESSOR_LAMBDA_ARN,
                    InvocationType='Event',
                    Payload=json.dumps(message_body)
                )
                return {'triggered': True, 'method': 'lambda_invoke', 'status_code': resp['StatusCode'], 'images_count': images_count}

        except Exception as e:
            logger.error(f"Failed to trigger image AI processing: {e}")
            return {'triggered': False, 'error': str(e), 'method': 'failed'}

    def _trigger_via_sqs(self, images_count: int) -> Dict[str, Any]:
        """(Deprecated in favor of unified method above)"""
        if not IMAGE_PROCESSING_QUEUE_URL:
            logger.warning("IMAGE_PROCESSING_QUEUE_URL not configured")
            return {'triggered': False, 'reason': 'sqs_not_configured'}
        try:
            # Basic body used previously; kept for backward compatibility if you call it elsewhere
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
                    'DocumentId': {'StringValue': self.document_id, 'DataType': 'String'},
                    'ImagesCount': {'StringValue': str(images_count), 'DataType': 'Number'},
                    'TriggerSource': {'StringValue': 'document_extractor', 'DataType': 'String'}
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
        """(Deprecated in favor of unified method above)"""
        if not IMAGE_PROCESSOR_LAMBDA_ARN:
            logger.warning("IMAGE_PROCESSOR_LAMBDA_ARN not configured")
            return {'triggered': False, 'reason': 'lambda_arn_not_configured'}
        try:
            payload = {
                'document_id': self.document_id,
                'images_count': images_count,
                'trigger_source': 'document_extractor',
                'processing_timestamp': self.processing_timestamp
            }
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

    def _trigger_via_eventbridge(self, images_count: int) -> Dict[str, Any]:
        """Trigger image processing via EventBridge (alternative option)"""
        try:
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
                        'Resources': [f"document:{self.document_id}"]
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

    # ------------------------ PDF PROCESSING (NEW) ------------------------

    def _process_pdf_with_pymupdf(self, file_path: str) -> Dict[str, Any]:
        """
        Process PDF with PyMuPDF:
          - Detect every image in reading order with exact bbox
          - Upload each image to S3 (unique placeholder name)
          - Save per-image metadata (page, bbox, normalized bbox) to DynamoDB
          - Replace images with in-place placeholders using redactions (exact same rectangles)
          - Save placeholder-preview PDF to S3
          - Extract text for storage (plain + light formatting)
        """
        if fitz is None:
            raise Exception("PyMuPDF (fitz) not available in this runtime")

        logger.info("Starting enhanced PDF processing with precise image placeholders...")

        pdf = fitz.open(file_path)
        extracted_plain_parts: List[str] = []
        images_detected_total = 0

        placeholder_local_path = f"/tmp/{self.document_id}_placeholders.pdf"

        for page_index in range(len(pdf)):
            page = pdf[page_index]
            page_num = page_index + 1
            page_rect = page.rect
            page_w, page_h = float(page_rect.width), float(page_rect.height)

            # Extract text (plain) for storage
            extracted_plain_parts.append(page.get_text("text"))

            # Reading-order structured dict to capture images with bbox
            p_dict = page.get_text("dict")
            seq_in_page = 0

            for blk in p_dict.get("blocks", []):
                if blk.get("type") == 1:  # image block
                    seq_in_page += 1
                    images_detected_total += 1

                    bbox = blk.get("bbox")  # [x0, y0, x1, y1]
                    ext = (blk.get("ext") or "png").lower()
                    img_bytes = blk.get("image")  # raw bytes

                    if not img_bytes:
                        logger.warning("Image bytes missing in dict block; fallback skipped.")
                        continue

                    # Unique placeholder
                    placeholder_name = f"PDFIMG_{self.image_counter}_{int(time.time()*1000)}"

                    # Upload image to S3
                    s3_key = self._upload_image_to_s3_ext(
                        img_bytes, placeholder_name, ext, f"page{page_num}_img{seq_in_page}.{ext}"
                    )
                    if not s3_key:
                        logger.error(f"Failed S3 upload for {placeholder_name}, skipping redaction/placeholder")
                        continue

                    # Persist image metadata (DDB + local state)
                    img_info = {
                        'placeholder': placeholder_name,
                        's3_key': s3_key,
                        's3_filename': f"{placeholder_name}.{ext}",
                        'original_filename': f"page{page_num}_img{seq_in_page}.{ext}",
                        'image_number': self.image_counter,
                        'reference_number': images_detected_total - 1,  # global sequence
                        'size_bytes': len(img_bytes),
                        'uploaded': True,
                        'upload_timestamp': datetime.utcnow().isoformat(),
                        'is_duplicate_reference': False,
                        'page_number': page_num,
                        'sequence_in_page': seq_in_page,
                        'bbox': {'x0': bbox[0], 'y0': bbox[1], 'x1': bbox[2], 'y1': bbox[3]},
                        'bbox_norm': {'x0': bbox[0]/page_w, 'y0': bbox[1]/page_h, 'x1': bbox[2]/page_w, 'y1': bbox[3]/page_h},
                        'page_size': {'width': page_w, 'height': page_h},
                        'ext': ext,
                        'extraction_method': 'pdf_pymupdf_blocks',
                        'processing_timestamp': self.processing_timestamp
                    }
                    self.processed_images.append(img_info)
                    self.placeholders[placeholder_name] = s3_key
                    self._store_image_metadata(img_info)

                    # Placeholder via redact annotation on exact rect
                    rect = fitz.Rect(bbox)
                    ph_text = f"{placeholder_name}"
                    page.add_redact_annot(
                        rect,
                        text=ph_text,
                        fill=(0.92, 0.92, 0.92),
                        text_color=(0, 0, 0),
                        fontname="helv",
                        fontsize=9,
                        align=1
                    )

                    self.image_counter += 1

            # Apply redactions to remove underlying image pixels
            page.apply_redactions()

        # Save placeholder-preview PDF locally, then upload to S3
        pdf.save(placeholder_local_path, garbage=4, deflate=True, clean=True)
        pdf.close()

        placeholder_pdf_s3_key = self._save_pdf_with_placeholders_to_s3(placeholder_local_path)

        # Extracted text variants
        plain_text_all = "\n".join(extracted_plain_parts).strip()
        formatted_text = plain_text_all

        # Clean up local temp
        try:
            os.unlink(placeholder_local_path)
        except Exception:
            pass

        result = {
            'formatted_text': formatted_text,
            'plain_text': plain_text_all,
            'method': 'pdf_pymupdf_blocks',
            'total_image_references': images_detected_total,
            'unique_image_files': images_detected_total,
            'tables_count': 0,
            'headings_count': 0,
            'placeholder_pdf_s3': f"s3://{S3_BUCKET}/{placeholder_pdf_s3_key}"
        }
        logger.info(f"Enhanced PDF processing complete. Images: {images_detected_total}.")
        return result

    def _upload_image_to_s3_ext(self, image_data: bytes, placeholder_name: str, ext: str, original_filename: str) -> Optional[str]:
        """Upload PDF image bytes to S3 honoring the original extension."""
        if not S3_BUCKET:
            logger.error("S3_BUCKET not configured")
            return None
        try:
            timestamp_prefix = datetime.utcnow().strftime('%Y/%m/%d/%H')
            ext = (ext or 'png').lower().strip('.')
            s3_key = f"extracted_images/{timestamp_prefix}/{self.document_id}/{placeholder_name}.{ext}"
            # Basic content-type inference
            if ext in ('jpg', 'jpeg'):
                content_type = 'image/jpeg'
            elif ext == 'png':
                content_type = 'image/png'
            elif ext == 'tiff' or ext == 'tif':
                content_type = 'image/tiff'
            elif ext == 'bmp':
                content_type = 'image/bmp'
            elif ext == 'gif':
                content_type = 'image/gif'
            else:
                content_type = f'image/{ext}'

            s3_client.put_object(
                Bucket=S3_BUCKET,
                Key=s3_key,
                Body=image_data,
                ContentType=content_type,
                Metadata={
                    'document_id': self.document_id,
                    'placeholder_name': placeholder_name,
                    'original_filename': original_filename,
                    'upload_timestamp': datetime.utcnow().isoformat(),
                    'processing_timestamp': self.processing_timestamp,
                    'source': 'pdf_pymupdf'
                }
            )
            logger.info(f"S3 Upload: {placeholder_name} → s3://{S3_BUCKET}/{s3_key}")
            return s3_key
        except Exception as e:
            logger.error(f"S3 upload failed for {placeholder_name}: {e}")
            return None

    def _save_pdf_with_placeholders_to_s3(self, local_pdf_path: str) -> str:
        """Upload the placeholder-preview PDF to S3 alongside text artifacts."""
        if not S3_BUCKET:
            raise Exception("S3_BUCKET not configured for PDF upload")

        timestamp_prefix = datetime.utcnow().strftime('%Y/%m/%d')
        base_path = f"document_extractions/{timestamp_prefix}/{self.document_id}"
        s3_key = f"{base_path}/placeholder_preview.pdf"

        with open(local_pdf_path, "rb") as fh:
            s3_client.put_object(
                Bucket=S3_BUCKET,
                Key=s3_key,
                Body=fh.read(),
                ContentType='application/pdf',
                Metadata={
                    'document_id': self.document_id,
                    'processing_timestamp': self.processing_timestamp,
                    'extraction_method': 'pdf_pymupdf_blocks'
                }
            )
        logger.info(f"Uploaded placeholder PDF: s3://{S3_BUCKET}/{s3_key}")
        return s3_key

    # ------------------------ DOCX PROCESSING (unchanged) ------------------------

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
                'total_image_references': len(all_image_references),
                'unique_image_files': len(unique_image_files),
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
                document_stats = {'tables_count': 0, 'headings_count': 0}
                body = root.find('.//w:body', self.namespaces)
                if body is not None:
                    for element in body:
                        if element.tag.endswith('}p'):  # Paragraph
                            para_content, para_images = self._process_paragraph(
                                element, styles_info, reference_counter
                            )
                            if para_content.strip():
                                formatted_parts.append(para_content)
                                if self._is_heading_paragraph(element, styles_info):
                                    document_stats['headings_count'] += 1
                            reference_counter += len(para_images)
                            all_image_references.extend(para_images)
                        elif element.tag.endswith('}tbl'):  # Table
                            table_content, table_images = self._process_table(
                                element, styles_info, reference_counter
                            )
                            if table_content.strip():
                                formatted_parts.append(table_content)
                                document_stats['tables_count'] += 1
                            reference_counter += len(table_images)
                            all_image_references.extend(table_images)
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
        para_style = self._get_paragraph_style(para_elem, styles_info)
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
        runs = para_elem.findall('.//w:r', self.namespaces)
        for run in runs:
            run_text, run_images = self._process_run(run, current_ref_counter)
            if run_text or run_images:
                para_parts.append(run_text)
                para_images.extend(run_images)
                current_ref_counter += len(run_images)
        para_text = ''.join(para_parts)
        formatted_para = self._apply_paragraph_formatting(
            para_text, para_style, is_list_item, list_level
        )
        return formatted_para, para_images
    
    def _process_run(self, run_elem, start_ref_counter: int) -> Tuple[str, List[Dict]]:
        """Process a text run with character formatting"""
        run_parts = []
        run_images = []
        current_ref_counter = start_ref_counter
        run_props = run_elem.find('.//w:rPr', self.namespaces)
        formatting = self._extract_run_formatting(run_props)
        text_elements = run_elem.findall('.//w:t', self.namespaces)
        for text_elem in text_elements:
            if text_elem.text:
                formatted_text = self._apply_character_formatting(text_elem.text, formatting)
                run_parts.append(formatted_text)
        drawings = run_elem.findall('.//w:drawing', self.namespaces)
        for drawing in drawings:
            pic_elements = drawing.findall('.//pic:pic', self.namespaces)
            for pic in pic_elements:
                image_marker = f"__IMAGE_PLACEHOLDER_{current_ref_counter}__"
                image_rel_id = None
                blip_elements = pic.findall('.//a:blip', self.namespaces)
                if blip_elements:
                    image_rel_id = blip_elements[0].get(
                        '{http://schemas.openxmlformats.org/officeDocument/2006/relationships}embed'
                    )
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
        table_parts.append("\n**TABLE START**\n")
        rows = table_elem.findall('.//w:tr', self.namespaces)
        for row_idx, row in enumerate(rows):
            row_parts = []
            cells = row.findall('.//w:tc', self.namespaces)
            for cell_idx, cell in enumerate(cells):
                cell_content = []
                cell_paras = cell.findall('.//w:p', self.namespaces)
                for para in cell_paras:
                    para_content, para_images = self._process_paragraph(
                        para, styles_info, current_ref_counter
                    )
                    if para_content.strip():
                        cell_content.append(para_content)
                    current_ref_counter += len(para_images)
                    table_images.extend(para_images)
                cell_text = ' '.join(cell_content).strip()
                row_parts.append(f"| {cell_text} ")
            if row_parts:
                table_parts.append(''.join(row_parts) + "|\n")
                if row_idx == 0:
                    separator = "|" + "---|" * len(cells) + "\n"
                    table_parts.append(separator)
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
        formatting = {'bold': False, 'italic': False, 'underline': False}
        if run_props is not None:
            if run_props.find('.//w:b', self.namespaces) is not None:
                formatting['bold'] = True
            if run_props.find('.//w:i', self.namespaces) is not None:
                formatting['italic'] = True
            if run_props.find('.//w:u', self.namespaces) is not None:
                formatting['underline'] = True
        return formatting
    
    def _apply_paragraph_formatting(self, text: str, style_info: Dict, 
                                  is_list_item: bool, list_level: int) -> str:
        """Apply paragraph-level formatting"""
        if not text.strip():
            return text
        style_name = style_info.get('name', '').lower()
        if 'heading' in style_name or 'title' in style_name:
            heading_level = 1
            for i in range(1, 7):
                if f'heading {i}' in style_name or f'heading{i}' in style_name:
                    heading_level = i
                    break
            return f"{'#' * heading_level} {text.strip()}\n"
        if is_list_item:
            indent = "  " * list_level
            return f"{indent}- {text.strip()}\n"
        return f"{text.strip()}\n"
    
    def _apply_character_formatting(self, text: str, formatting: Dict[str, bool]) -> str:
        """Apply character-level formatting"""
        if not text:
            return text
        formatted_text = text
        if formatting.get('bold', False):
            formatted_text = f"**{formatted_text}**"
        if formatting.get('italic', False):
            formatted_text = f"*{formatted_text}*"
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
        sorted_image_files = sorted(unique_image_files, key=lambda x: self._extract_number_from_filename(x))
        rel_to_file_map = self._build_relationship_mapping(docx_zip, sorted_image_files)
        logger.info(f"Processing {len(all_image_references)} image references...")
        for ref_idx, image_ref in enumerate(all_image_references):
            try:
                img_file = self._get_image_file_for_reference(
                    image_ref, sorted_image_files, rel_to_file_map, ref_idx
                )
                if not img_file:
                    logger.warning(f"No image file found for reference {ref_idx}")
                    continue
                with docx_zip.open(img_file) as img_data_file:
                    image_data = img_data_file.read()
                if len(image_data) < 100:
                    logger.warning(f"Image {img_file} too small, skipping")
                    continue
                timestamp_suffix = int(time.time() * 1000) + ref_idx
                placeholder_name = f"IMAGE_{self.image_counter}_{timestamp_suffix}"
                s3_key = self._upload_image_to_s3(image_data, placeholder_name, img_file)
                if s3_key:
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
                        'is_duplicate_reference': img_file in [img['original_filename'] for img in self.processed_images],
                        'page_number': 1,
                        'extraction_method': 'enhanced_docx_with_formatting'
                    }
                    self.processed_images.append(image_info)
                    self.placeholders[placeholder_name] = s3_key
                    self._store_image_metadata(image_info)
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
        current_text = re.sub(r'__IMAGE_PLACEHOLDER_\d+__', '', current_text)
        current_text = re.sub(r'\n\s*\n\s*\n', '\n\n', current_text)
        return current_text.strip()
    
    def _strip_formatting_markers(self, formatted_text: str) -> str:
        """Generate plain text version by removing formatting markers"""
        plain_text = formatted_text
        plain_text = re.sub(r'\*\*(.*?)\*\*', r'\1', plain_text)
        plain_text = re.sub(r'\*(.*?)\*', r'\1', plain_text)
        plain_text = re.sub(r'<u>(.*?)</u>', r'\1', plain_text)
        plain_text = re.sub(r'^#+\s*', '', plain_text, flags=re.MULTILINE)
        plain_text = re.sub(r'^\s*-\s*', '', plain_text, flags=re.MULTILINE)
        plain_text = re.sub(r'\*\*TABLE START\*\*\n', '', plain_text)
        plain_text = re.sub(r'\*\*TABLE END\*\*\n', '', plain_text)
        plain_text = re.sub(r'\|.*?\|', '', plain_text, flags=re.MULTILINE)
        plain_text = re.sub(r'^-+\|.*$', '', plain_text, flags=re.MULTILINE)
        plain_text = re.sub(r'\n\s*\n\s*\n', '\n\n', plain_text)
        return plain_text.strip()
    
    def _fallback_formatted_extraction(self, docx_zip: zipfile.ZipFile) -> Tuple[str, List[Dict], Dict]:
        """Fallback extraction that still attempts some formatting"""
        logger.info("Using fallback formatted extraction")
        try:
            with docx_zip.open('word/document.xml') as doc_xml:
                xml_content = doc_xml.read().decode('utf-8')
                paragraphs = re.findall(r'<w:p[^>]*>.*?</w:p>', xml_content, re.DOTALL)
                formatted_parts = []
                for i, para in enumerate(paragraphs):
                    text_matches = re.findall(r'<w:t[^>]*>(.*?)</w:t>', para, re.DOTALL)
                    para_text = ''.join(text_matches).strip()
                    if para_text:
                        if re.search(r'<w:b/>', para):
                            para_text = f"**{para_text}**"
                        formatted_parts.append(para_text)
                formatted_text = '\n\n'.join(formatted_parts)
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
        if image_ref.get('relationship_id') and image_ref['relationship_id'] in rel_map:
            return rel_map[image_ref['relationship_id']]
        if image_files:
            file_index = ref_idx % len(image_files)
            return image_files[file_index]
        return None
    
    def _extract_number_from_filename(self, filename: str) -> int:
        """Extract number from filename for natural sorting"""
        numbers = re.findall(r'\d+', filename)
        return int(numbers[0]) if numbers else 0
    
    def _upload_image_to_s3(self, image_data: bytes, placeholder_name: str, original_filename: str) -> Optional[str]:
        """Upload image to S3 with unique path (PNG default)"""
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
                    'upload_timestamp': datetime.utcnow().isoformat(),
                    'processing_timestamp': self.processing_timestamp
                }
            )
            logger.info(f"S3 Upload: {placeholder_name} → s3://{S3_BUCKET}/{s3_key}")
            return s3_key
        except Exception as e:
            logger.error(f"S3 upload failed for {placeholder_name}: {e}")
            return None
    
    def _store_image_metadata(self, image_info: Dict[str, Any]) -> None:
        """Store image metadata in DynamoDB"""
        if not images_table:
            logger.warning("Images table not available")
            return
        try:
            ttl = datetime.utcnow() + timedelta(days=30)
            image_id = f"{self.document_id}_{image_info['reference_number']}_{int(time.time() * 1000)}"
            item = {
                'document_id': self.document_id,
                'image_id': image_id,
                'image_number': image_info.get('image_number'),
                'reference_number': image_info.get('reference_number'),
                'placeholder': image_info.get('placeholder'),
                's3_bucket': S3_BUCKET,
                's3_key': image_info.get('s3_key'),
                's3_filename': image_info.get('s3_filename'),
                'original_filename': image_info.get('original_filename'),
                'size_bytes': image_info.get('size_bytes'),
                'is_duplicate_reference': image_info.get('is_duplicate_reference', False),
                'page_number': image_info.get('page_number', 1),
                'page_size': image_info.get('page_size'),
                'bbox': image_info.get('bbox'),
                'bbox_norm': image_info.get('bbox_norm'),
                'ext': image_info.get('ext'),
                'extraction_method': image_info.get('extraction_method', 'enhanced_docx_with_formatting'),
                'processing_timestamp': self.processing_timestamp,
                'upload_timestamp': image_info.get('upload_timestamp'),
                'ai_processed': False,
                'ttl': int(ttl.timestamp())
            }
            images_table.put_item(Item=item)
            logger.info(f"DynamoDB: Stored metadata for {image_info['placeholder']}")
        except Exception as e:
            logger.error(f"DynamoDB storage failed for {image_info.get('placeholder')}: {e}")
    
    def _save_text_files_to_s3(self, formatted_text: str) -> bool:
        """Primary method: Save extracted text as files in S3"""
        if not S3_BUCKET:
            logger.error("S3_BUCKET not configured for text file storage")
            return False
        try:
            timestamp_prefix = datetime.utcnow().strftime('%Y/%m/%d')
            base_path = f"document_extractions/{timestamp_prefix}/{self.document_id}"
            plain_text = self._strip_formatting_markers(formatted_text)
            file_metadata = {
                'document_id': self.document_id,
                'extraction_method': 'enhanced_docx_with_formatting',
                'processing_timestamp': self.processing_timestamp,
                'character_count': str(len(formatted_text)),
                'plain_character_count': str(len(plain_text)),
                'images_processed': str(len(self.processed_images)),
                'extraction_timestamp': datetime.utcnow().isoformat()
            }
            formatted_s3_key = f"{base_path}/formatted_text.md"
            s3_client.put_object(
                Bucket=S3_BUCKET,
                Key=formatted_s3_key,
                Body=formatted_text.encode('utf-8'),
                ContentType='text/markdown; charset=utf-8',
                Metadata=file_metadata
            )
            logger.info(f"Saved formatted text: s3://{S3_BUCKET}/{formatted_s3_key}")
            plain_s3_key = f"{base_path}/plain_text.txt"
            s3_client.put_object(
                Bucket=S3_BUCKET,
                Key=plain_s3_key,
                Body=plain_text.encode('utf-8'),
                ContentType='text/plain; charset=utf-8',
                Metadata=file_metadata
            )
            logger.info(f"Saved plain text: s3://{S3_BUCKET}/{plain_s3_key}")
            extraction_metadata = {
                'document_id': self.document_id,
                'processing_timestamp': self.processing_timestamp,
                'extraction_timestamp': datetime.utcnow().isoformat(),
                'extraction_method': 'enhanced_docx_with_formatting',
                'formatting_preserved': True,
                'character_count': len(formatted_text),
                'plain_character_count': len(plain_text),
                'images_detected': len(self.processed_images),
                'placeholders': self.placeholders,
                'file_locations': {
                    'formatted_text': f"s3://{S3_BUCKET}/{formatted_s3_key}",
                    'plain_text': f"s3://{S3_BUCKET}/{plain_s3_key}",
                    'metadata': f"s3://{S3_BUCKET}/{base_path}/metadata.json"
                },
                'images': [
                    {
                        'placeholder': img.get('placeholder'),
                        's3_location': f"s3://{S3_BUCKET}/{img.get('s3_key')}",
                        'original_filename': img.get('original_filename'),
                        'size_bytes': img.get('size_bytes')
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
            summary_report = self._generate_summary_report(formatted_text, plain_text, extraction_metadata)
            summary_s3_key = f"{base_path}/extraction_summary.txt"
            s3_client.put_object(
                Bucket=S3_BUCKET,
                Key=summary_s3_key,
                Body=summary_report.encode('utf-8'),
                ContentType='text/plain; charset=utf-8',
                Metadata[file_metadata
                ]
            )
            logger.info(f"Saved summary: s3://{S3_BUCKET}/{summary_s3_key}")
            return True
        except Exception as e:
            logger.error(f"Failed to save text files to S3: {e}")
            return False
    
    def _generate_summary_report(self, formatted_text: str, plain_text: str, metadata: dict) -> str:
        """Generate a human-readable summary report"""
        report_lines = [
            "=" * 60,
            "DOCUMENT EXTRACTION SUMMARY REPORT",
            "=" * 60,
            "",
            f"Document ID: {metadata['document_id']}",
            f"Processing Date: {metadata['extraction_timestamp']}",
            f"Extraction Method: {metadata['extraction_method']}",
            "",
            "CONTENT STATISTICS:",
            f"  - Formatted Text Length: {metadata['character_count']:,} characters",
            f"  - Plain Text Length: {metadata['plain_character_count']:,} characters",
            f"  - Images Extracted: {metadata['images_detected']}",
            f"  - Formatting Preserved: {'Yes' if metadata['formatting_preserved'] else 'No'}",
            "",
            "FILE LOCATIONS:",
            f"  - Formatted Text: {metadata['file_locations']['formatted_text']}",
            f"  - Plain Text: {metadata['file_locations']['plain_text']}",
            f"  - Metadata: {metadata['file_locations']['metadata']}",
            "",
        ]
        if metadata.get('images'):
            report_lines.extend(["EXTRACTED IMAGES:", ""])
            for img in metadata['images']:
                report_lines.append(f"  - {img['placeholder']}: {img['s3_location']}")
                report_lines.append(f"    Original: {img['original_filename']} ({img['size_bytes']:,} bytes)")
                report_lines.append("")
        report_lines.extend([
            "CONTENT PREVIEW (First 500 characters):",
            "-" * 40,
            plain_text[:500] + ("..." if len(plain_text) > 500 else ""),
            "",
            "=" * 60,
            "END OF SUMMARY REPORT",
            "=" * 60
        ])
        return "\n".join(report_lines)
    
    def _store_formatted_text(self, formatted_text: str) -> bool:
        """Store formatted text in DynamoDB with robust error handling"""
        logger.info(f"Attempting to store text for document {self.document_id}")
        logger.info(f"Text length: {len(formatted_text)} characters")
        if not text_table:
            logger.error("DynamoDB text table not initialized!")
            logger.error(f"DYNAMODB_TEXT_TABLE environment variable: {DYNAMODB_TEXT_TABLE}")
            self._save_text_to_file(formatted_text)
            return False
        try:
            ttl = datetime.utcnow() + timedelta(days=30)
            plain_text = self._strip_formatting_markers(formatted_text)
            item = {
                'document_id': self.document_id,
                'extracted_text': formatted_text,
                'plain_text': plain_text,
                'extraction_timestamp': datetime.utcnow().isoformat(),
                'processing_timestamp': self.processing_timestamp,
                'character_count': len(formatted_text),
                'plain_character_count': len(plain_text),
                'extraction_method': 'enhanced_docx_with_formatting',
                'formatting_preserved': True,
                'pages_processed': 1,
                'images_processed': len(self.processed_images),
                'placeholders': self.placeholders,
                'ttl': int(ttl.timestamp())
            }
            logger.info(f"Attempting DynamoDB put_item for document {self.document_id}")
            response = text_table.put_item(Item=item)
            logger.info(f"DynamoDB: Successfully stored formatted text for document {self.document_id}")
            self._save_text_to_file(formatted_text)
            return True
        except Exception as e:
            logger.error(f"DynamoDB text storage failed: {e}")
            logger.error(f"Exception type: {type(e).__name__}")
            logger.error(f"Exception details: {str(e)}")
            self._save_text_to_file(formatted_text)
            raise e
    
    def _save_text_to_file(self, formatted_text: str) -> None:
        """Fallback: Save text to local file for debugging"""
        try:
            formatted_file_path = f"/tmp/{self.document_id}_formatted.txt"
            with open(formatted_file_path, 'w', encoding='utf-8') as f:
                f.write(formatted_text)
            logger.info(f"Backup: Saved formatted text to {formatted_file_path}")
            plain_text = self._strip_formatting_markers(formatted_text)
            plain_file_path = f"/tmp/{self.document_id}_plain.txt"
            with open(plain_file_path, 'w', encoding='utf-8') as f:
                f.write(plain_text)
            logger.info(f"Backup: Saved plain text to {plain_file_path}")
        except Exception as e:
            logger.error(f"Failed to save backup text files: {e}")


def lambda_handler(event: Dict[str, Any], context) -> Dict[str, Any]:
    """
    AWS Lambda handler with integrated image AI processing trigger (DOCX + PDF)
    """
    request_id = getattr(context, 'aws_request_id', str(uuid.uuid4()))
    try:
        logger.info(f"Enhanced Document processor with AI integration started - Request ID: {request_id}")
        # Health check
        if event.get('action') == 'health_check':
            return {
                'statusCode': 200,
                'body': json.dumps({
                    'status': 'healthy',
                    'service': 'enhanced-document-processor-with-ai-integration',
                    'timestamp': datetime.utcnow().isoformat(),
                    'request_id': request_id,
                    'features': [
                        'Enhanced DOCX processing with formatting preservation',
                        'PDF processing with exact image placeholders (PyMuPDF)',
                        'Automatic AI image processing trigger',
                        'S3 file storage for extracted text and PDFs',
                        'DynamoDB metadata storage',
                        'Event-driven architecture support',
                        'SQS and Lambda invoke integration'
                    ],
                    'ai_integration': {
                        'sqs_configured': bool(IMAGE_PROCESSING_QUEUE_URL),
                        'lambda_arn_configured': bool(IMAGE_PROCESSOR_LAMBDA_ARN),
                        'async_processing': USE_ASYNC_PROCESSING
                    }
                }),
                'headers': {'Content-Type': 'application/json', 'X-Request-ID': request_id}
            }
        # SQS batch
        if 'Records' in event and event['Records']:
            results = []
            for record in event['Records']:
                try:
                    message_body = json.loads(record['body'])
                    file_info = message_body['file_info']
                    s3_key = file_info['key']
                    original_filename = Path(s3_key).name
                    document_id = generate_unique_document_id(original_filename)
                    logger.info(f"Processing {original_filename} as document {document_id}")
                    local_path = f"/tmp/{document_id}_{original_filename}"
                    s3_client.download_file(S3_BUCKET, s3_key, local_path)
                    processor = EnhancedDocumentProcessor(document_id)
                    result = processor.process_document(local_path)
                    results.append(result)
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
                'headers': {'Content-Type': 'application/json', 'X-Request-ID': request_id}
            }
        # Direct invocation
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
                    'headers': {'Content-Type': 'application/json', 'X-Request-ID': request_id}
                }
            if not original_filename:
                original_filename = Path(s3_key).name
            document_id = generate_unique_document_id(original_filename)
            logger.info(f"Processing {original_filename} as document {document_id}")
            local_path = f"/tmp/{document_id}_{original_filename}"
            s3_client.download_file(s3_bucket, s3_key, local_path)
            processor = EnhancedDocumentProcessor(document_id)
            result = processor.process_document(local_path)
            try:
                os.unlink(local_path)
            except Exception:
                pass
            return {
                'statusCode': 200 if result['success'] else 500,
                'body': json.dumps(result),
                'headers': {'Content-Type': 'application/json', 'X-Request-ID': request_id}
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
            'headers': {'Content-Type': 'application/json', 'X-Request-ID': request_id}
        }
