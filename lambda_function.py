"""
Complete Integrated Document Processor with Auto AI Image Processing
Extracts text/images from DOCX files and automatically triggers AI analysis
(Updated: PDF now emits INLINE placeholders in formatted_text, no redactions)
"""

import json
import boto3
import logging
import os
import base64
import time
import zipfile
import xml.etree.ElementTree as ET
import re
import uuid
import traceback
from typing import Dict, Any, List, Optional, Tuple
from pathlib import Path
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
IMAGE_PROCESSING_QUEUE_URL = os.environ.get('IMAGE_BATCH_QUEUE_URL') or os.environ.get('IMAGE_PROCESSING_QUEUE_URL')
USE_ASYNC_PROCESSING = os.environ.get('USE_ASYNC_PROCESSING', 'true').lower() == 'true'

# AWS Clients
s3_client = boto3.client('s3')
dynamodb = boto3.resource('dynamodb')
lambda_client = boto3.client('lambda')
sqs_client = boto3.client('sqs')
events_client = boto3.client('events')

# Globals for tables
text_table = None
images_table = None


def initialize_dynamodb_tables():
    """Initialize DynamoDB tables with proper error handling and logging"""
    global text_table, images_table
    logger.info("Initializing DynamoDB tables...")
    logger.info(f"Region: {AWS_REGION}")
    logger.info(f"Text table name: {DYNAMODB_TEXT_TABLE}")
    logger.info(f"Images table name: {DYNAMODB_IMAGES_TABLE}")

    try:
        if DYNAMODB_TEXT_TABLE:
            text_table = dynamodb.Table(DYNAMODB_TEXT_TABLE)
            text_table.load()
            logger.info(f"Initialized text table: {DYNAMODB_TEXT_TABLE}")
        else:
            logger.error("DYNAMODB_TEXT_TABLE env var not set!")
            text_table = None
    except Exception as e:
        logger.error(f"Failed to init text table: {e}")
        text_table = None

    try:
        if DYNAMODB_IMAGES_TABLE:
            images_table = dynamodb.Table(DYNAMODB_IMAGES_TABLE)
            images_table.load()
            logger.info(f"Initialized images table: {DYNAMODB_IMAGES_TABLE}")
        else:
            logger.error("DYNAMODB_IMAGES_TABLE env var not set!")
            images_table = None
    except Exception as e:
        logger.error(f"Failed to init images table: {e}")
        images_table = None

    if text_table and images_table:
        logger.info("All DynamoDB tables ready.")
    elif text_table:
        logger.warning("Only text table initialized.")
    elif images_table:
        logger.warning("Only images table initialized.")
    else:
        logger.error("No DynamoDB tables available.")


initialize_dynamodb_tables()


def generate_unique_document_id(original_filename: str = None) -> str:
    ts = datetime.utcnow()
    micro = ts.microsecond
    rand = str(uuid.uuid4())[:8]
    date_part = ts.strftime('%Y%m%d')
    time_part = ts.strftime('%H%M%S')
    if original_filename:
        base = Path(original_filename).stem
        clean = re.sub(r'[^\w\-_]', '_', base)[:15]
        return f"{clean}_{date_part}_{time_part}_{micro}_{rand}"
    return f"doc_{date_part}_{time_part}_{micro}_{rand}"


class EnhancedDocumentProcessor:
    """Enhanced processor that preserves document formatting and triggers AI processing"""

    def __init__(self, document_id: str):
        self.document_id = document_id
        self.placeholders: Dict[str, str] = {}
        self.processed_images: List[Dict[str, Any]] = []
        self.image_counter = 1
        self.processing_timestamp = datetime.utcnow().isoformat()
        self.namespaces = {
            'w': 'http://schemas.openxmlformats.org/wordprocessingml/2006/main',
            'pic': 'http://schemas.openxmlformats.org/drawingml/2006/picture',
            'a': 'http://schemas.openxmlformats.org/drawingml/2006/main',
            'r': 'http://schemas.openxmlformats.org/officeDocument/2006/relationships',
            'wp': 'http://schemas.openxmlformats.org/drawingml/2006/wordprocessingDrawing',
        }

    # ------------------------ Main entry ------------------------

    def process_document(self, file_path: str) -> Dict[str, Any]:
        start_time = time.time()
        try:
            logger.info(f"Processing {file_path} as {self.document_id}")

            if not os.path.exists(file_path):
                raise Exception(f"File not found: {file_path}")

            size = os.path.getsize(file_path)
            if size > MAX_FILE_SIZE:
                raise Exception(f"File too large: {size} bytes")

            if file_path.lower().endswith('.docx'):
                result = self._process_docx_with_formatting(file_path)
            elif file_path.lower().endswith('.pdf'):
                result = self._process_pdf_with_pymupdf_inline(file_path)  # <<< UPDATED
            else:
                raise Exception("Unsupported file type")

            if not result.get('formatted_text', '').strip():
                raise Exception("Text extraction failed - no content found")

            # Save to S3 (formatted/plain/metadata/summary)
            self._save_text_files_to_s3(result['formatted_text'])

            # Backup to DynamoDB (optional)
            if text_table:
                try:
                    self._store_formatted_text(result['formatted_text'])
                except Exception as e:
                    logger.warning(f"DynamoDB backup failed: {e}")

            # Trigger AI processing for images
            ai_trigger = self._trigger_image_ai_processing(result['formatted_text'], len(self.processed_images))

            elapsed = time.time() - start_time
            timestamp_prefix = datetime.utcnow().strftime('%Y/%m/%d')
            base_path = f"document_extractions/{timestamp_prefix}/{self.document_id}"
            file_locations = {
                'formatted_text': f"s3://{S3_BUCKET}/{base_path}/formatted_text.md",
                'plain_text': f"s3://{S3_BUCKET}/{base_path}/plain_text.txt",
                'metadata': f"s3://{S3_BUCKET}/{base_path}/metadata.json",
                'summary': f"s3://{S3_BUCKET}/{base_path}/extraction_summary.txt",
            }

            return {
                'success': True,
                'document_id': self.document_id,
                'processing_timestamp': self.processing_timestamp,
                'extracted_text': result['formatted_text'],
                'plain_text': result.get('plain_text', ''),
                'images_count': len(self.processed_images),
                'placeholders': self.placeholders,
                'processing_time': elapsed,
                'extraction_method': result.get('method', 'enhanced_docx_with_formatting'),
                'pages_processed': result.get('pages_processed', 1),
                'images_detected': result.get('total_image_references', 0),
                'unique_image_files': result.get('unique_image_files', 0),
                'images_extracted': len(self.processed_images),
                'images_uploaded': len([i for i in self.processed_images if i.get('uploaded')]),
                'tables_detected': result.get('tables_count', 0),
                'headings_detected': result.get('headings_count', 0),
                'formatting_preserved': True,
                'files_saved_to_s3': True,
                'output_files': file_locations,
                's3_base_path': f"s3://{S3_BUCKET}/{base_path}/",
                'placeholder_pdf_s3': result.get('placeholder_pdf_s3'),  # will be None for inline flow
                'ai_processing': ai_trigger,
                'error_count': 0,
                'warning_count': 0,
                'errors': [],
                'warnings': [],
            }

        except Exception as e:
            elapsed = time.time() - start_time
            logger.error(f"Processing failed: {e}")
            return {
                'success': False,
                'document_id': self.document_id,
                'processing_timestamp': self.processing_timestamp,
                'extracted_text': "",
                'plain_text': "",
                'images_count': 0,
                'placeholders': {},
                'processing_time': elapsed,
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
                'traceback': traceback.format_exc(),
            }

    # ------------------------ AI trigger ------------------------

    def _trigger_image_ai_processing(self, extracted_text: str, images_count: int) -> Dict[str, Any]:
        """Trigger AI processing of extracted images – sends full per-image metadata."""
        if images_count == 0:
            logger.info("No images to process with AI")
            return {'triggered': False, 'reason': 'no_images'}

        payload_images = [{
            'placeholder': img.get('placeholder'),
            's3_bucket': S3_BUCKET,
            's3_key': img.get('s3_key'),
            'page_number': img.get('page_number'),
            'sequence_in_page': img.get('sequence_in_page'),
            'bbox': img.get('bbox'),
            'bbox_norm': img.get('bbox_norm'),
            'page_size': img.get('page_size'),
            'ext': img.get('ext'),
            'original_filename': img.get('original_filename'),
        } for img in self.processed_images]

        try:
            message_body = {
                'document_id': self.document_id,
                'images_count': images_count,
                'processing_timestamp': self.processing_timestamp,
                'trigger_timestamp': datetime.utcnow().isoformat(),
                'images': payload_images,
                's3_base_path': f"s3://{S3_BUCKET}/document_extractions/{datetime.utcnow().strftime('%Y/%m/%d')}/{self.document_id}/",
                'trigger_source': 'document_extractor',
                'text_excerpt_first_2k': extracted_text[:2000] if extracted_text else "",
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
                        'TriggerSource': {'StringValue': 'document_extractor', 'DataType': 'String'},
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
            logger.error(f"AI trigger failed: {e}")
            return {'triggered': False, 'error': str(e), 'method': 'failed'}

    def _trigger_via_eventbridge(self, images_count: int) -> Dict[str, Any]:
        """Alternative trigger via EventBridge (kept for completeness)"""
        try:
            event_detail = {
                'document_id': self.document_id,
                'images_count': images_count,
                'processing_timestamp': self.processing_timestamp,
                'extraction_complete': True,
            }
            response = events_client.put_events(
                Entries=[
                    {
                        'Source': 'document.processor',
                        'DetailType': 'Document Processing Complete',
                        'Detail': json.dumps(event_detail),
                        'Resources': [f"document:{self.document_id}"],
                    }
                ]
            )
            logger.info("Sent EventBridge event for image processing")
            return {
                'triggered': True,
                'method': 'eventbridge',
                'event_id': response['Entries'][0].get('EventId'),
                'images_count': images_count,
            }
        except Exception as e:
            logger.error(f"EventBridge trigger failed: {e}")
            return {'triggered': False, 'error': str(e), 'method': 'eventbridge'}

    # ------------------------ PDF PROCESSING (INLINE PLACEHOLDERS) ------------------------

    def _process_pdf_with_pymupdf_inline(self, file_path: str) -> Dict[str, Any]:
        """
        Process PDF with PyMuPDF using reading-order dict and emit INLINE placeholders:
          - Iterate blocks in reading order (text/image)
          - On text blocks: append text to formatted_text
          - On image blocks: extract bytes, upload to S3, store metadata, and append inline placeholder
          - No redactions / no watermark PDF generated
          - Extract plain text from the same concatenated stream (without formatting marks)
        """
        if fitz is None:
            raise Exception("PyMuPDF (fitz) not available in this runtime")

        logger.info("Starting PDF processing with INLINE placeholders (no redactions)...")
        pdf = fitz.open(file_path)

        parts_formatted: List[str] = []
        parts_plain: List[str] = []
        images_detected_total = 0

        for page_index in range(len(pdf)):
            page = pdf[page_index]
            page_num = page_index + 1
            page_rect = page.rect
            page_w, page_h = float(page_rect.width), float(page_rect.height)

            # Reading-order dict
            p_dict = page.get_text("dict")
            seq_in_page = 0

            # We also want plain text of the page (once)
            page_plain_text = page.get_text("text") or ""
            # We'll rebuild formatted text by walking blocks,
            # so we don't add page_plain_text directly to formatted parts (to avoid duplication).
            # Instead, we push text blocks as they appear below.

            for blk in p_dict.get("blocks", []):
                btype = blk.get("type")
                if btype == 0:
                    # Text block: append as-is to formatted and plain
                    text_spans = []
                    for line in blk.get("lines", []):
                        for span in line.get("spans", []):
                            if span.get("text"):
                                text_spans.append(span["text"])
                    text_block = "\n".join([t for t in text_spans if t is not None]).strip()
                    if text_block:
                        parts_formatted.append(text_block)
                        parts_plain.append(text_block)
                elif btype == 1:
                    # Image block
                    seq_in_page += 1
                    images_detected_total += 1

                    bbox = blk.get("bbox")  # [x0, y0, x1, y1]
                    ext = (blk.get("ext") or "png").lower()
                    img_bytes = blk.get("image")

                    if not img_bytes:
                        # Sometimes dict block doesn't carry raw bytes; fallback via xref
                        try:
                            # Approximate: get first image from page matching bbox
                            # If not available, skip gracefully.
                            # (PyMuPDF newer versions include 'image' already in dict.)
                            logger.warning("Image bytes missing in dict block; attempting fallback xref extract")
                            # Fallback disabled to avoid complex heuristics; skip if no bytes.
                            continue
                        except Exception as _:
                            logger.warning("Fallback image extraction failed; skipping block")
                            continue

                    # Upload image to S3
                    placeholder_name = f"PDFIMG_{self.image_counter}_{int(time.time()*1000)}"
                    s3_key = self._upload_image_to_s3_ext(
                        img_bytes, placeholder_name, ext, f"page{page_num}_img{seq_in_page}.{ext}"
                    )
                    if not s3_key:
                        logger.error(f"S3 upload failed for {placeholder_name}, skipping placeholder insertion.")
                        continue

                    # Save metadata (DynamoDB)
                    img_info = {
                        'placeholder': placeholder_name,
                        's3_key': s3_key,
                        's3_filename': f"{placeholder_name}.{ext}",
                        'original_filename': f"page{page_num}_img{seq_in_page}.{ext}",
                        'image_number': self.image_counter,
                        'reference_number': images_detected_total - 1,
                        'size_bytes': len(img_bytes),
                        'uploaded': True,
                        'upload_timestamp': datetime.utcnow().isoformat(),
                        'is_duplicate_reference': False,
                        'page_number': page_num,
                        'sequence_in_page': seq_in_page,
                        'bbox': {'x0': bbox[0], 'y0': bbox[1], 'x1': bbox[2], 'y1': bbox[3]} if bbox else None,
                        'bbox_norm': {'x0': bbox[0]/page_w, 'y0': bbox[1]/page_h, 'x1': bbox[2]/page_w, 'y1': bbox[3]/page_h} if bbox else None,
                        'page_size': {'width': page_w, 'height': page_h},
                        'ext': ext,
                        'extraction_method': 'pdf_pymupdf_inline_placeholders',
                        'processing_timestamp': self.processing_timestamp,
                    }
                    self.processed_images.append(img_info)
                    self.placeholders[placeholder_name] = s3_key
                    self._store_image_metadata(img_info)

                    # Append INLINE placeholder to formatted text
                    # We use a consistent markdown-like marker identical to DOCX flow:
                    # The reconstructor will replace one of these patterns: ![PLACEHOLDER] | __PLACEHOLDER__ | [PLACEHOLDER]
                    parts_formatted.append(f"\n![{placeholder_name}]()\n")
                    parts_plain.append(f"\n[{placeholder_name}]\n")

                    self.image_counter += 1
                else:
                    # Other block types (vector, etc.) -> ignore for now
                    continue

            # Add a page separator to keep logical breaks (optional)
            parts_formatted.append("\n")
            parts_plain.append("\n")

        pdf.close()

        # Build final texts
        formatted_text = "\n".join(parts_formatted).strip()
        plain_text_all = "\n".join(parts_plain).strip()

        result = {
            'formatted_text': formatted_text,
            'plain_text': plain_text_all,
            'method': 'pdf_pymupdf_inline_placeholders',
            'total_image_references': images_detected_total,
            'unique_image_files': images_detected_total,
            'tables_count': 0,
            'headings_count': 0,
            'pages_processed': len(parts_plain),  # approximate
            'placeholder_pdf_s3': None,  # we no longer produce redaction preview PDF
        }
        logger.info(f"PDF processing (inline) complete. Images detected: {images_detected_total}.")
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
            if ext in ('jpg', 'jpeg'):
                content_type = 'image/jpeg'
            elif ext == 'png':
                content_type = 'image/png'
            elif ext in ('tiff', 'tif'):
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
                    'source': 'pdf_pymupdf_inline',
                }
            )
            logger.info(f"S3 Upload: {placeholder_name} → s3://{S3_BUCKET}/{s3_key}")
            return s3_key
        except Exception as e:
            logger.error(f"S3 upload failed for {placeholder_name}: {e}")
            return None

    # ------------------------ DOCX PROCESSING (UNCHANGED LOGIC) ------------------------

    def _process_docx_with_formatting(self, file_path: str) -> Dict[str, Any]:
        logger.info("Starting DOCX processing with formatting preservation...")
        with zipfile.ZipFile(file_path, 'r') as docx_zip:
            styles_info = self._extract_styles(docx_zip)
            numbering_info = self._extract_numbering(docx_zip)
            formatted_text, all_image_references, document_stats = self._extract_formatted_content(
                docx_zip, styles_info, numbering_info
            )
            unique_image_files = [f for f in docx_zip.namelist() if f.startswith('word/media/')]
            logger.info(f"Image references: {len(all_image_references)} | unique files: {len(unique_image_files)}")
            final_text = self._process_all_image_references_formatted(
                docx_zip, formatted_text, all_image_references, unique_image_files
            )
            plain_text = self._strip_formatting_markers(final_text)
            logger.info("DOCX processing complete")
            return {
                'formatted_text': final_text,
                'plain_text': plain_text,
                'method': 'enhanced_docx_with_formatting',
                'total_image_references': len(all_image_references),
                'unique_image_files': len(unique_image_files),
                'tables_count': document_stats.get('tables_count', 0),
                'headings_count': document_stats.get('headings_count', 0),
                'pages_processed': 1,
            }

    def _extract_styles(self, docx_zip: zipfile.ZipFile) -> Dict[str, Dict]:
        styles_info: Dict[str, Dict[str, str]] = {}
        try:
            with docx_zip.open('word/styles.xml') as styles_file:
                styles_root = ET.fromstring(styles_file.read().decode('utf-8'))
                for style in styles_root.findall('.//w:style', self.namespaces):
                    sid = style.get('{http://schemas.openxmlformats.org/wordprocessingml/2006/main}styleId')
                    stype = style.get('{http://schemas.openxmlformats.org/wordprocessingml/2006/main}type')
                    name_elem = style.find('.//w:name', self.namespaces)
                    sname = name_elem.get('{http://schemas.openxmlformats.org/wordprocessingml/2006/main}val') if name_elem is not None else sid
                    styles_info[sid] = {'name': sname, 'type': stype}
        except Exception as e:
            logger.warning(f"Could not extract styles: {e}")
        return styles_info

    def _extract_numbering(self, docx_zip: zipfile.ZipFile) -> Dict[str, Dict]:
        numbering_info: Dict[str, Dict[str, Dict]] = {}
        try:
            with docx_zip.open('word/numbering.xml') as numbering_file:
                numbering_root = ET.fromstring(numbering_file.read().decode('utf-8'))
                for num_def in numbering_root.findall('.//w:num', self.namespaces):
                    num_id = num_def.get('{http://schemas.openxmlformats.org/wordprocessingml/2006/main}numId')
                    numbering_info[num_id] = {'levels': {}}
        except Exception as e:
            logger.warning(f"Could not extract numbering: {e}")
        return numbering_info

    def _extract_formatted_content(self, docx_zip: zipfile.ZipFile, styles_info: Dict, numbering_info: Dict) -> Tuple[str, List[Dict], Dict]:
        try:
            with docx_zip.open('word/document.xml') as doc_xml:
                xml_content = doc_xml.read().decode('utf-8')
                root = ET.fromstring(xml_content)
                formatted_parts: List[str] = []
                all_image_references: List[Dict[str, Any]] = []
                reference_counter = 0
                document_stats = {'tables_count': 0, 'headings_count': 0}
                body = root.find('.//w:body', self.namespaces)
                if body is not None:
                    for element in body:
                        if element.tag.endswith('}p'):
                            para_content, para_images = self._process_paragraph(element, styles_info, reference_counter)
                            if para_content.strip():
                                formatted_parts.append(para_content)
                                if self._is_heading_paragraph(element, styles_info):
                                    document_stats['headings_count'] += 1
                            reference_counter += len(para_images)
                            all_image_references.extend(para_images)
                        elif element.tag.endswith('}tbl'):
                            table_content, table_images = self._process_table(element, styles_info, reference_counter)
                            if table_content.strip():
                                formatted_parts.append(table_content)
                                document_stats['tables_count'] += 1
                            reference_counter += len(table_images)
                            all_image_references.extend(table_images)
                formatted_text = '\n\n'.join(formatted_parts)
                logger.info(f"Formatted chars: {len(formatted_text)} | image refs: {len(all_image_references)}")
                return formatted_text, all_image_references, document_stats
        except Exception as e:
            logger.error(f"Failed to extract formatted content: {e}")
            return self._fallback_formatted_extraction(docx_zip)

    def _process_paragraph(self, para_elem, styles_info: Dict, start_ref_counter: int) -> Tuple[str, List[Dict]]:
        para_parts: List[str] = []
        para_images: List[Dict[str, Any]] = []
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
        formatted_para = self._apply_paragraph_formatting(para_text, para_style, is_list_item, list_level)
        return formatted_para, para_images

    def _process_run(self, run_elem, start_ref_counter: int) -> Tuple[str, List[Dict]]:
        run_parts: List[str] = []
        run_images: List[Dict[str, Any]] = []
        current_ref_counter = start_ref_counter
        run_props = run_elem.find('.//w:rPr', self.namespaces)
        formatting = self._extract_run_formatting(run_props)
        text_elements = run_elem.findall('.//w:t', self.namespaces)
        for text_elem in text_elements:
            if text_elem.text:
                run_parts.append(self._apply_character_formatting(text_elem.text, formatting))
        drawings = run_elem.findall('.//w:drawing', self.namespaces)
        for drawing in drawings:
            pic_elements = drawing.findall('.//pic:pic', self.namespaces)
            for pic in pic_elements:
                image_marker = f"__IMAGE_PLACEHOLDER_{current_ref_counter}__"
                image_rel_id = None
                blips = pic.findall('.//a:blip', self.namespaces)
                if blips:
                    image_rel_id = blips[0].get('{http://schemas.openxmlformats.org/officeDocument/2006/relationships}embed')
                run_images.append({
                    'marker': image_marker,
                    'reference_number': current_ref_counter,
                    'relationship_id': image_rel_id,
                    'context': ''.join(run_parts)[:100],
                })
                run_parts.append(f" {image_marker} ")
                current_ref_counter += 1
        return ''.join(run_parts), run_images

    def _process_table(self, table_elem, styles_info: Dict, start_ref_counter: int) -> Tuple[str, List[Dict]]:
        table_parts: List[str] = []
        table_images: List[Dict[str, Any]] = []
        current_ref_counter = start_ref_counter
        table_parts.append("\n**TABLE START**\n")
        rows = table_elem.findall('.//w:tr', self.namespaces)
        for row_idx, row in enumerate(rows):
            row_parts: List[str] = []
            cells = row.findall('.//w:tc', self.namespaces)
            for cell in cells:
                cell_content: List[str] = []
                cell_paras = cell.findall('.//w:p', self.namespaces)
                for para in cell_paras:
                    para_content, para_images = self._process_paragraph(para, styles_info, current_ref_counter)
                    if para_content.strip():
                        cell_content.append(para_content)
                    current_ref_counter += len(para_images)
                    table_images.extend(para_images)
                cell_text = ' '.join(cell_content).strip()
                row_parts.append(f"| {cell_text} ")
            if row_parts:
                table_parts.append(''.join(row_parts) + "|\n")
                if row_idx == 0:
                    table_parts.append("|" + ("---|" * len(cells)) + "\n")
        table_parts.append("**TABLE END**\n")
        return ''.join(table_parts), table_images

    def _get_paragraph_style(self, para_elem, styles_info: Dict) -> Dict[str, Any]:
        style_info: Dict[str, Any] = {'name': 'Normal', 'type': 'paragraph'}
        para_props = para_elem.find('.//w:pPr', self.namespaces)
        if para_props is not None:
            style_elem = para_props.find('.//w:pStyle', self.namespaces)
            if style_elem is not None:
                sid = style_elem.get('{http://schemas.openxmlformats.org/wordprocessingml/2006/main}val')
                if sid in styles_info:
                    style_info = styles_info[sid]
        return style_info

    def _extract_run_formatting(self, run_props) -> Dict[str, bool]:
        formatting = {'bold': False, 'italic': False, 'underline': False}
        if run_props is not None:
            if run_props.find('.//w:b', self.namespaces) is not None:
                formatting['bold'] = True
            if run_props.find('.//w:i', self.namespaces) is not None:
                formatting['italic'] = True
            if run_props.find('.//w:u', self.namespaces) is not None:
                formatting['underline'] = True
        return formatting

    def _apply_paragraph_formatting(self, text: str, style_info: Dict, is_list_item: bool, list_level: int) -> str:
        if not text.strip():
            return text
        style_name = style_info.get('name', '').lower()
        if 'heading' in style_name or 'title' in style_name:
            level = 1
            for i in range(1, 7):
                if f'heading {i}' in style_name or f'heading{i}' in style_name:
                    level = i
                    break
            return f"{'#' * level} {text.strip()}\n"
        if is_list_item:
            indent = "  " * list_level
            return f"{indent}- {text.strip()}\n"
        return f"{text.strip()}\n"

    def _apply_character_formatting(self, text: str, formatting: Dict[str, bool]) -> str:
        if not text:
            return text
        t = text
        if formatting.get('bold'):
            t = f"**{t}**"
        if formatting.get('italic'):
            t = f"*{t}*"
        if formatting.get('underline'):
            t = f"<u>{t}</u>"
        return t

    def _is_heading_paragraph(self, para_elem, styles_info: Dict) -> bool:
        style_info = self._get_paragraph_style(para_elem, styles_info)
        return 'heading' in style_info.get('name', '').lower() or 'title' in style_info.get('name', '').lower()

    def _process_all_image_references_formatted(self, docx_zip: zipfile.ZipFile, formatted_text: str, all_image_references: List[Dict], unique_image_files: List[str]) -> str:
        current_text = formatted_text
        sorted_imgs = sorted(unique_image_files, key=lambda x: self._extract_number_from_filename(x))
        rel_to_file_map = self._build_relationship_mapping(docx_zip, sorted_imgs)
        logger.info(f"Processing {len(all_image_references)} image references...")
        for ref_idx, image_ref in enumerate(all_image_references):
            try:
                img_file = self._get_image_file_for_reference(image_ref, sorted_imgs, rel_to_file_map, ref_idx)
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
                        'extraction_method': 'enhanced_docx_with_formatting',
                    }
                    self.processed_images.append(image_info)
                    self.placeholders[placeholder_name] = s3_key
                    self._store_image_metadata(image_info)
                    current_text = current_text.replace(image_ref['marker'], f"\n![{placeholder_name}]({s3_key})\n")
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
        plain_text = formatted_text
        plain_text = re.sub(r'\*\*(.*?)\*\*', r'\1', plain_text)  # Bold
        plain_text = re.sub(r'\*(.*?)\*', r'\1', plain_text)      # Italic
        plain_text = re.sub(r'<u>(.*?)</u>', r'\1', plain_text)   # Underline
        plain_text = re.sub(r'^#+\s*', '', plain_text, flags=re.MULTILINE)   # Headers
        plain_text = re.sub(r'^\s*-\s*', '', plain_text, flags=re.MULTILINE) # Lists
        plain_text = re.sub(r'\*\*TABLE START\*\*\n', '', plain_text)        # Table markers
        plain_text = re.sub(r'\*\*TABLE END\*\*\n', '', plain_text)
        plain_text = re.sub(r'\|.*?\|', '', plain_text, flags=re.MULTILINE)  # Table cells
        plain_text = re.sub(r'^-+\|.*$', '', plain_text, flags=re.MULTILINE) # Table separators
        plain_text = re.sub(r'\n\s*\n\s*\n', '\n\n', plain_text)             # Collapse extra blanks
        return plain_text.strip()

    def _fallback_formatted_extraction(self, docx_zip: zipfile.ZipFile) -> Tuple[str, List[Dict], Dict]:
        logger.info("Using fallback formatted extraction")
        try:
            with docx_zip.open('word/document.xml') as doc_xml:
                xml_content = doc_xml.read().decode('utf-8')
                paragraphs = re.findall(r'<w:p[^>]*>.*?</w:p>', xml_content, re.DOTALL)
                formatted_parts: List[str] = []
                for para in paragraphs:
                    texts = re.findall(r'<w:t[^>]*>(.*?)</w:t>', para, re.DOTALL)
                    para_text = ''.join(texts).strip()
                    if para_text:
                        if re.search(r'<w:b/>', para):
                            para_text = f"**{para_text}**"
                        formatted_parts.append(para_text)
                formatted_text = '\n\n'.join(formatted_parts)
                pic_matches = re.findall(r'<pic:pic[^>]*>', xml_content)
                all_refs: List[Dict[str, Any]] = []
                for i, _ in enumerate(pic_matches):
                    marker = f"__IMAGE_PLACEHOLDER_{i}__"
                    all_refs.append({'marker': marker, 'reference_number': i, 'context': f"Fallback reference {i}", 'fallback': True})
                    formatted_text += f" {marker} "
                stats = {'tables_count': len(re.findall(r'<w:tbl>', xml_content)), 'headings_count': 0}
                return formatted_text, all_refs, stats
        except Exception as e:
            logger.error(f"Fallback formatted extraction failed: {e}")
            return "Failed to extract formatted text", [], {'tables_count': 0, 'headings_count': 0}

    def _build_relationship_mapping(self, docx_zip: zipfile.ZipFile, image_files: List[str]) -> Dict[str, str]:
        rel_map: Dict[str, str] = {}
        try:
            with docx_zip.open('word/_rels/document.xml.rels') as rels_file:
                rels_root = ET.fromstring(rels_file.read().decode('utf-8'))
                for r in rels_root.findall('.//{http://schemas.openxmlformats.org/package/2006/relationships}Relationship'):
                    rid = r.get('Id')
                    target = r.get('Target')
                    rtype = r.get('Type')
                    if rtype and 'image' in rtype.lower() and target:
                        full_path = f"word/{target}" if target.startswith('media/') else target
                        if full_path in image_files:
                            rel_map[rid] = full_path
                            logger.info(f"Mapped relationship {rid} → {full_path}")
        except Exception as e:
            logger.warning(f"Could not build relationship mapping: {e}")
        return rel_map

    def _get_image_file_for_reference(self, image_ref: Dict, image_files: List[str], rel_map: Dict[str, str], ref_idx: int) -> Optional[str]:
        if image_ref.get('relationship_id') and image_ref['relationship_id'] in rel_map:
            return rel_map[image_ref['relationship_id']]
        if image_files:
            return image_files[ref_idx % len(image_files)]
        return None

    def _extract_number_from_filename(self, filename: str) -> int:
        nums = re.findall(r'\d+', filename)
        return int(nums[0]) if nums else 0

    def _upload_image_to_s3(self, image_data: bytes, placeholder_name: str, original_filename: str) -> Optional[str]:
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
                    'processing_timestamp': self.processing_timestamp,
                }
            )
            logger.info(f"S3 Upload: {placeholder_name} → s3://{S3_BUCKET}/{s3_key}")
            return s3_key
        except Exception as e:
            logger.error(f"S3 upload failed for {placeholder_name}: {e}")
            return None

    def _store_image_metadata(self, image_info: Dict[str, Any]) -> None:
        if not images_table:
            logger.warning("Images table not available")
            return
        try:
            ttl = datetime.utcnow() + timedelta(days=30)
            # NOTE: your images table key schema might be (document_id, image_number).
            # We're not changing it; just writing consistent attributes.
            item = {
                'document_id': self.document_id,
                'image_number': image_info.get('image_number'),  # sort key in your image-processor code
                'image_id': f"{self.document_id}_{image_info.get('reference_number')}_{int(time.time() * 1000)}",
                'reference_number': image_info.get('reference_number'),
                'placeholder': image_info.get('placeholder'),
                's3_bucket': S3_BUCKET,
                's3_key': image_info.get('s3_key'),
                's3_filename': image_info.get('s3_filename'),
                'original_filename': image_info.get('original_filename'),
                'size_bytes': image_info.get('size_bytes'),
                'is_duplicate_reference': image_info.get('is_duplicate_reference', False),
                'page_number': image_info.get('page_number', 1),
                'sequence_in_page': image_info.get('sequence_in_page'),
                'page_size': image_info.get('page_size'),
                'bbox': image_info.get('bbox'),
                'bbox_norm': image_info.get('bbox_norm'),
                'ext': image_info.get('ext'),
                'extraction_method': image_info.get('extraction_method', 'enhanced_docx_with_formatting'),
                'processing_timestamp': self.processing_timestamp,
                'upload_timestamp': image_info.get('upload_timestamp'),
                'ai_processed': False,
                'ttl': int(ttl.timestamp()),
            }
            images_table.put_item(Item=item)
            logger.info(f"DynamoDB: Stored metadata for {image_info.get('placeholder')}")
        except Exception as e:
            logger.error(f"DynamoDB storage failed for {image_info.get('placeholder')}: {e}")

    # ------------------------ Text artifacts to S3 ------------------------

    def _save_text_files_to_s3(self, formatted_text: str) -> bool:
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
                'extraction_timestamp': datetime.utcnow().isoformat(),
            }
            # formatted
            formatted_s3_key = f"{base_path}/formatted_text.md"
            s3_client.put_object(
                Bucket=S3_BUCKET,
                Key=formatted_s3_key,
                Body=formatted_text.encode('utf-8'),
                ContentType='text/markdown; charset=utf-8',
                Metadata=file_metadata
            )
            logger.info(f"Saved formatted text: s3://{S3_BUCKET}/{formatted_s3_key}")
            # plain
            plain_s3_key = f"{base_path}/plain_text.txt"
            s3_client.put_object(
                Bucket=S3_BUCKET,
                Key=plain_s3_key,
                Body=plain_text.encode('utf-8'),
                ContentType='text/plain; charset=utf-8',
                Metadata=file_metadata
            )
            logger.info(f"Saved plain text: s3://{S3_BUCKET}/{plain_s3_key}")
            # metadata.json
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
                    'metadata': f"s3://{S3_BUCKET}/{base_path}/metadata.json",
                },
                'images': [
                    {
                        'placeholder': img.get('placeholder'),
                        's3_location': f"s3://{S3_BUCKET}/{img.get('s3_key')}",
                        'original_filename': img.get('original_filename'),
                        'size_bytes': img.get('size_bytes'),
                    } for img in self.processed_images
                ],
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
            # summary
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
        report_lines: List[str] = [
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
            "=" * 60,
        ])
        return "\n".join(report_lines)

    # ------------------------ Text backup to /tmp + DynamoDB ------------------------

    def _store_formatted_text(self, formatted_text: str) -> bool:
        logger.info(f"Storing text for document {self.document_id}")
        if not text_table:
            logger.error("DynamoDB text table not initialized!")
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
                'ttl': int(ttl.timestamp()),
            }
            text_table.put_item(Item=item)
            logger.info(f"DynamoDB: stored text for {self.document_id}")
            self._save_text_to_file(formatted_text)  # backup copy locally
            return True
        except Exception as e:
            logger.error(f"DynamoDB text storage failed: {e}")
            self._save_text_to_file(formatted_text)
            raise e

    def _save_text_to_file(self, formatted_text: str) -> None:
        try:
            formatted_file_path = f"/tmp/{self.document_id}_formatted.txt"
            with open(formatted_file_path, 'w', encoding='utf-8') as f:
                f.write(formatted_text)
            plain_text = self._strip_formatting_markers(formatted_text)
            plain_file_path = f"/tmp/{self.document_id}_plain.txt"
            with open(plain_file_path, 'w', encoding='utf-8') as f:
                f.write(plain_text)
            logger.info(f"Backups saved: {formatted_file_path}, {plain_file_path}")
        except Exception as e:
            logger.error(f"Failed to save backup files: {e}")


# ------------------------ Lambda Handler ------------------------

def lambda_handler(event: Dict[str, Any], context) -> Dict[str, Any]:
    """
    AWS Lambda handler with integrated image AI processing trigger (DOCX + PDF inline placeholders)
    """
    request_id = getattr(context, 'aws_request_id', str(uuid.uuid4()))
    try:
        logger.info(f"Document processor started - Request ID: {request_id}")

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
                        'PDF inline placeholders (PyMuPDF reading-order)',
                        'Automatic AI image processing trigger',
                        'S3 file storage for extracted text',
                        'DynamoDB metadata storage',
                        'Event-driven architecture support',
                        'SQS and Lambda invoke integration',
                    ],
                    'ai_integration': {
                        'sqs_configured': bool(IMAGE_PROCESSING_QUEUE_URL),
                        'lambda_arn_configured': bool(IMAGE_PROCESSOR_LAMBDA_ARN),
                        'async_processing': USE_ASYNC_PROCESSING,
                    }
                }),
                'headers': {'Content-Type': 'application/json', 'X-Request-ID': request_id}
            }

        # SQS batch
        if 'Records' in event and event['Records']:
            results: List[Dict[str, Any]] = []
            for record in event['Records']:
                try:
                    message_body = json.loads(record['body'])
                    file_info = message_body['file_info']
                    s3_key = file_info['key']
                    original_filename = Path(s3_key).name
                    document_id = generate_unique_document_id(original_filename)
                    logger.info(f"SQS → processing {original_filename} as {document_id}")
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
                    results.append({'success': False, 'error': str(e), 'traceback': traceback.format_exc()})
            successful = len([r for r in results if r.get('success')])
            return {
                'statusCode': 200 if successful > 0 else 400,
                'body': json.dumps({
                    'success': successful > 0,
                    'processed_count': successful,
                    'failed_count': len(results) - successful,
                    'total_count': len(results),
                    'results': results,
                    'request_id': request_id,
                }),
                'headers': {'Content-Type': 'application/json', 'X-Request-ID': request_id}
            }

        # Direct invocation
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
                    'request_id': request_id,
                }),
                'headers': {'Content-Type': 'application/json', 'X-Request-ID': request_id}
            }
        if not original_filename:
            original_filename = Path(s3_key).name
        document_id = generate_unique_document_id(original_filename)
        logger.info(f"Direct → processing {original_filename} as {document_id}")
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
                'traceback': traceback.format_exc(),
            }),
            'headers': {'Content-Type': 'application/json', 'X-Request-ID': request_id}
        }
