# -*- coding: utf-8 -*-
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

try:
    import fitz
except Exception:
    fitz = None

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

AWS_REGION = os.environ.get('AWS_REGION', 'us-east-1')
S3_BUCKET = os.environ.get('S3_BUCKET')
DYNAMODB_TEXT_TABLE = os.environ.get('EXTRACTED_TEXT_TABLE', 'extracted_text')
DYNAMODB_IMAGES_TABLE = os.environ.get('IMAGES_TABLE', 'images')
MAX_FILE_SIZE = int(os.environ.get('MAX_FILE_SIZE', '104857600'))
IMAGE_PROCESSOR_LAMBDA_ARN = os.environ.get('IMAGE_PROCESSOR_LAMBDA_ARN')
IMAGE_PROCESSING_QUEUE_URL = os.environ.get('IMAGE_PROCESSING_QUEUE_URL') or os.environ.get('IMAGE_BATCH_QUEUE_URL')
USE_ASYNC_PROCESSING = os.environ.get('USE_ASYNC_PROCESSING', 'true').lower() == 'true'
EVENT_BUS_NAME = os.environ.get('EVENT_BUS_NAME', 'default')
MODULE_ROOT_PREFIX = os.environ.get('MODULE_ROOT_PREFIX', 'submissions')

bedrock_runtime = boto3.client('bedrock-runtime', region_name=AWS_REGION)
ANALYSIS_MODEL_ID = os.environ.get('ANALYSIS_MODEL_ID', 'anthropic.claude-3-7-sonnet-20250219-v1:0')
ANALYSIS_MAX_TOKENS = int(os.environ.get('ANALYSIS_MAX_TOKENS', '800'))
ANALYSIS_TEMPERATURE = float(os.environ.get('ANALYSIS_TEMPERATURE', '0.0'))
ANALYSIS_PROMPT = os.environ.get(
    'ANALYSIS_PROMPT',
    "You are an expert visual analyst. Provide a concise, factual, Markdown-formatted analysis of the image. "
    "Include: a one-sentence caption, key elements, any text detected (OCR), any tables (as Markdown), and "
    "relevant insights for academic assignment grading."
)

s3_client = boto3.client('s3', region_name=AWS_REGION)
dynamodb = boto3.resource('dynamodb', region_name=AWS_REGION)
lambda_client = boto3.client('lambda', region_name=AWS_REGION)
sqs_client = boto3.client('sqs', region_name=AWS_REGION)
events_client = boto3.client('events', region_name=AWS_REGION)

text_table = None
images_table = None

def initialize_dynamodb_tables():
    global text_table, images_table
    try:
        text_table = dynamodb.Table(DYNAMODB_TEXT_TABLE) if DYNAMODB_TEXT_TABLE else None
        if text_table:
            text_table.load()
    except Exception as e:
        logger.warning(f"Text table init failed: {e}")
        text_table = None
    try:
        images_table = dynamodb.Table(DYNAMODB_IMAGES_TABLE) if DYNAMODB_IMAGES_TABLE else None
        if images_table:
            images_table.load()
    except Exception as e:
        logger.warning(f"Images table init failed: {e}")
        images_table = None

initialize_dynamodb_tables()

def _now_parts():
    dt = datetime.utcnow()
    return dt.strftime('%Y'), dt.strftime('%m'), dt.strftime('%d'), dt.strftime('%H')

def generate_unique_document_id(original_filename: str = None) -> str:
    ts = datetime.utcnow()
    micro = ts.microsecond
    rand = str(uuid.uuid4())[:8]
    date_part = ts.strftime('%Y%m%d')
    time_part = ts.strftime('%H%M%S')
    if original_filename:
        base = Path(original_filename).stem
        clean = re.sub(r'[^\w\-_]', '_', base)[:30]
        return f"{clean}_{date_part}_{time_part}_{micro}_{rand}"
    return f"doc_{date_part}_{time_part}_{micro}_{rand}"

def _md_strip(formatted_text: str) -> str:
    t = formatted_text
    t = re.sub(r'```.*?```', '', t, flags=re.DOTALL)
    t = re.sub(r'!\[[^\]]*\]\([^)]+\)', '', t)
    t = re.sub(r'\[([^\]]+)\]\([^)]+\)', r'\1', t)
    t = re.sub(r'[>#*_`~-]+', ' ', t)
    t = re.sub(r'\n{3,}', '\n\n', t)
    return t.strip()

def _emit_event(detail_type: str, detail: Dict[str, Any]) -> None:
    try:
        events_client.put_events(
            Entries=[{
                "Source": "ai-grading-system",
                "DetailType": detail_type,
                "Detail": json.dumps(detail, default=str),
                "EventBusName": EVENT_BUS_NAME
            }]
        )
    except Exception as e:
        logger.warning(f"EventBridge put_events failed: {e}")

def _parse_student_path_from_key(key: str) -> Tuple[Optional[str], Optional[str], Optional[str]]:
    parts = key.split("/")
    try:
        i = parts.index(MODULE_ROOT_PREFIX)
        module_id = parts[i + 1]
        if parts[i + 2] != "assignments":
            return None, None, None
        assignment_id = parts[i + 3]
        if parts[i + 4] != "files":
            return None, None, None
        student_id = parts[i + 5]
        return module_id, assignment_id, student_id
    except Exception:
        return None, None, None

class EnhancedDocumentProcessor:
    def __init__(self, document_id: str):
        self.document_id = document_id
        self.placeholders: Dict[str, str] = {}
        self.processed_images: List[Dict[str, Any]] = []
        self.image_counter = 1
        self.processing_timestamp = datetime.utcnow().isoformat()
        self.module_id: Optional[str] = None
        self.assignment_id: Optional[str] = None
        self.student_id: Optional[str] = None
        self.namespaces = {
            'w': 'http://schemas.openxmlformats.org/wordprocessingml/2006/main',
            'pic': 'http://schemas.openxmlformats.org/drawingml/2006/picture',
            'a': 'http://schemas.openxmlformats.org/drawingml/2006/main',
            'r': 'http://schemas.openxmlformats.org/officeDocument/2006/relationships',
            'wp': 'http://schemas.openxmlformats.org/drawingml/2006/wordprocessingDrawing',
        }

    def process_document(self, file_path: str) -> Dict[str, Any]:
        start_time = time.time()
        try:
            if not os.path.exists(file_path):
                raise Exception(f"File not found: {file_path}")
            size = os.path.getsize(file_path)
            if size > MAX_FILE_SIZE:
                raise Exception(f"File too large: {size} bytes")
            if file_path.lower().endswith('.docx'):
                result = self._process_docx_with_formatting(file_path)
            elif file_path.lower().endswith('.pdf'):
                result = self._process_pdf_with_inline_markers(file_path)
            else:
                raise Exception("Unsupported file type")
            if not result.get('formatted_text', '').strip():
                raise Exception("Text extraction failed - no content found")
            saved_keys = self._save_text_files_to_s3(result['formatted_text'])
            if text_table:
                try:
                    self._store_formatted_text(result['formatted_text'])
                except Exception as e:
                    logger.warning(f"DynamoDB backup failed: {e}")
            ai_trigger = self._trigger_image_ai_processing(
                extracted_text=result['formatted_text'],
                images_count=len(self.processed_images),
                pipeline_mode=result.get('method', 'enhanced_docx_with_formatting'),
                formatted_text_s3_key=saved_keys.get('formatted_s3_key')
            )
            elapsed = time.time() - start_time
            yyyy, mm, dd, _ = _now_parts()
            base_path = f"document_extractions/{yyyy}/{mm}/{dd}/{self.document_id}"
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
                'output_files': {
                    'formatted_text': f"s3://{S3_BUCKET}/{base_path}/formatted_text.md",
                    'plain_text': f"s3://{S3_BUCKET}/{base_path}/plain_text.txt",
                    'metadata': f"s3://{S3_BUCKET}/{base_path}/metadata.json",
                    'summary': f"s3://{S3_BUCKET}/{base_path}/extraction_summary.txt",
                },
                's3_base_path': f"s3://{S3_BUCKET}/{base_path}/",
                'ai_processing': ai_trigger,
                'error_count': 0,
                'warning_count': 0,
                'errors': [],
                'warnings': [],
            }
        except Exception as e:
            logger.error(f"Processing failed: {e}")
            return {
                'success': False,
                'document_id': self.document_id,
                'processing_timestamp': self.processing_timestamp,
                'extracted_text': "",
                'plain_text': "",
                'images_count': 0,
                'placeholders': {},
                'processing_time': 0,
                'extraction_method': 'error',
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
        finally:
            try:
                if os.path.exists(file_path):
                    os.unlink(file_path)
            except Exception:
                pass

    def _trigger_image_ai_processing(self, extracted_text: str, images_count: int, pipeline_mode: str, formatted_text_s3_key: Optional[str]) -> Dict[str, Any]:
        if images_count == 0:
            return {'triggered': False, 'reason': 'no_images'}
        yyyy, mm, dd, _ = _now_parts()
        s3_base_path = f"s3://{S3_BUCKET}/document_extractions/{yyyy}/{mm}/{dd}/{self.document_id}/"
        payload_images = [{
            'placeholder': img.get('placeholder'),
            's3_bucket': S3_BUCKET,
            's3_key': img.get('s3_key'),
            'page_number': img.get('page_number', 1),
            'sequence_in_page': img.get('sequence_in_page'),
            'bbox': img.get('bbox'),
            'bbox_norm': img.get('bbox_norm'),
            'page_size': img.get('page_size'),
            'ext': img.get('ext', 'png'),
            'original_filename': img.get('original_filename'),
            'reference_number': img.get('reference_number', 0),
            'upload_timestamp': img.get('upload_timestamp', self.processing_timestamp),
        } for img in self.processed_images]
        message_body = {
            'document_id': self.document_id,
            'images_count': images_count,
            'processing_timestamp': self.processing_timestamp,
            'trigger_timestamp': datetime.utcnow().isoformat(),
            'images': payload_images,
            's3_base_path': s3_base_path,
            'formatted_text_s3_key': formatted_text_s3_key or f"document_extractions/{yyyy}/{mm}/{dd}/{self.document_id}/formatted_text.md",
            'trigger_source': 'document_extractor',
            'pipeline_mode': pipeline_mode,
            'text_excerpt_first_2k': extracted_text[:2000] if extracted_text else "",
            'reconstruction': {
                'inline_markers': True,
                'output_reconstructed_key': 'reconstructed_text.md',
                'reconstructed_documents_dir': 'reconstructed_documents'
            },
            'module_id': self.module_id,
            'assignment_id': self.assignment_id,
            'student_id': self.student_id
        }
        try:
            if USE_ASYNC_PROCESSING:
                if not IMAGE_PROCESSING_QUEUE_URL:
                    return {'triggered': False, 'reason': 'sqs_not_configured'}
                resp = sqs_client.send_message(
                    QueueUrl=IMAGE_PROCESSING_QUEUE_URL,
                    MessageBody=json.dumps(message_body),
                    MessageAttributes={
                        'DocumentId': {'StringValue': self.document_id, 'DataType': 'String'},
                        'ImagesCount': {'StringValue': str(images_count), 'DataType': 'Number'},
                        'PipelineMode': {'StringValue': pipeline_mode, 'DataType': 'String'},
                    }
                )
                _emit_event("ImageBatchEnqueued", {
                    "document_id": self.document_id,
                    "images_count": images_count,
                    "queue": IMAGE_PROCESSING_QUEUE_URL,
                    "module_id": self.module_id,
                    "assignment_id": self.assignment_id,
                    "student_id": self.student_id,
                    "timestamp": datetime.utcnow().isoformat()
                })
                return {'triggered': True, 'method': 'sqs', 'message_id': resp.get('MessageId'), 'images_count': images_count}
            else:
                if not IMAGE_PROCESSOR_LAMBDA_ARN:
                    return {'triggered': False, 'reason': 'lambda_arn_not_configured'}
                lambda_client.invoke(FunctionName=IMAGE_PROCESSOR_LAMBDA_ARN, InvocationType='Event', Payload=json.dumps(message_body).encode('utf-8'))
                _emit_event("ImageBatchEnqueued", {
                    "document_id": self.document_id,
                    "images_count": images_count,
                    "lambda": IMAGE_PROCESSOR_LAMBDA_ARN,
                    "module_id": self.module_id,
                    "assignment_id": self.assignment_id,
                    "student_id": self.student_id,
                    "timestamp": datetime.utcnow().isoformat()
                })
                return {'triggered': True, 'method': 'lambda_invoke', 'images_count': images_count}
        except Exception as e:
            logger.error(f"AI trigger failed: {e}")
            return {'triggered': False, 'error': str(e), 'method': 'failed'}

    def _process_pdf_with_inline_markers(self, file_path: str) -> Dict[str, Any]:
        if fitz is None:
            raise Exception("PyMuPDF (fitz) not available")
        pdf = fitz.open(file_path)
        inline_parts: List[str] = []
        extracted_plain_parts: List[str] = []
        images_detected_total = 0
        for page_index in range(len(pdf)):
            page = pdf[page_index]
            page_num = page_index + 1
            extracted_plain_parts.append(page.get_text("text"))
            p_dict = page.get_text("dict")
            seq_in_page = 0
            for blk in p_dict.get("blocks", []):
                btype = blk.get("type")
                if btype == 0:
                    block_text = []
                    for line in blk.get("lines", []):
                        for span in line.get("spans", []):
                            if span.get("text"):
                                block_text.append(span["text"])
                    txt = " ".join(block_text).strip()
                    if txt:
                        inline_parts.append(txt)
                elif btype == 1:
                    seq_in_page += 1
                    images_detected_total += 1
                    ext = (blk.get("ext") or "png").lower()
                    img_bytes = blk.get("image")
                    if not img_bytes:
                        continue
                    placeholder = f"IMAGE_{self.image_counter}_{int(time.time()*1000)}"
                    yyyy, mm, dd, hh = _now_parts()
                    key = f"extracted_images/{yyyy}/{mm}/{dd}/{hh}/{self.document_id}/{placeholder}.{ext}"
                    s3_client.put_object(
                        Bucket=S3_BUCKET,
                        Key=key,
                        Body=img_bytes,
                        ContentType=f'image/{ext}',
                        Metadata={
                            'document_id': self.document_id,
                            'placeholder_name': placeholder,
                            'upload_timestamp': datetime.utcnow().isoformat(),
                            'processing_timestamp': self.processing_timestamp,
                            'source': 'pdf_inline_markers',
                        }
                    )
                    img_info = {
                        'placeholder': placeholder,
                        's3_key': key,
                        's3_filename': f"{placeholder}.{ext}",
                        'original_filename': f"page{page_num}_img{seq_in_page}.{ext}",
                        'image_number': self.image_counter,
                        'reference_number': images_detected_total - 1,
                        'size_bytes': len(img_bytes),
                        'uploaded': True,
                        'upload_timestamp': datetime.utcnow().isoformat(),
                        'is_duplicate_reference': False,
                        'page_number': page_num,
                        'sequence_in_page': seq_in_page,
                        'bbox': None,
                        'bbox_norm': None,
                        'page_size': None,
                        'ext': ext,
                        'extraction_method': 'pdf_inline_markers',
                        'processing_timestamp': self.processing_timestamp,
                    }
                    self.processed_images.append(img_info)
                    self.placeholders[placeholder] = key
                    self._store_image_metadata(img_info)
                    inline_parts.append(f"\n![{placeholder}](s3://{S3_BUCKET}/{key})\n")
                    self.image_counter += 1
        pdf.close()
        plain_text_all = "\n".join(extracted_plain_parts).strip()
        formatted_text = ("\n\n".join([p for p in inline_parts if p.strip()])).strip()
        return {
            'formatted_text': formatted_text,
            'plain_text': plain_text_all,
            'method': 'pdf_inline_markers',
            'total_image_references': images_detected_total,
            'unique_image_files': images_detected_total,
            'tables_count': 0,
            'headings_count': 0,
            'pages_processed': len(extracted_plain_parts),
        }

    def _process_docx_with_formatting(self, file_path: str) -> Dict[str, Any]:
        with zipfile.ZipFile(file_path, 'r') as docx_zip:
            styles_info = self._extract_styles(docx_zip)
            numbering_info = self._extract_numbering(docx_zip)
            formatted_text, all_image_references, document_stats = self._extract_formatted_content(
                docx_zip, styles_info, numbering_info
            )
            unique_image_files = [f for f in docx_zip.namelist() if f.startswith('word/media/')]
            final_text = self._process_all_image_references_formatted(
                docx_zip, formatted_text, all_image_references, unique_image_files
            )
            plain_text = self._strip_formatting_markers(final_text)
            return {
                'formatted_text': final_text,
                'plain_text': plain_text,
                'method': 'enhanced_docx_with_formatting',
                'total_image_references': len(all_image_references),
                'unique_image_files': len(unique_image_files),
                'tables_count': document_stats.get('tables_count', 0),
                'headings_count': document_stats.get('headings_count', 0),
                'pages_processed': 1
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
        run_images: List[Dict] = []
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

    def _process_all_image_references_formatted(self, docx_zip: zipfile.ZipFile, formatted_text: str, all_image_references: List[Dict], unique_image_files: List[str]) -> str:
        current_text = formatted_text
        sorted_imgs = sorted(unique_image_files, key=lambda x: self._extract_number_from_filename(x))
        rel_to_file_map = self._build_relationship_mapping(docx_zip, sorted_imgs)
        for ref_idx, image_ref in enumerate(all_image_references):
            try:
                img_file = self._get_image_file_for_reference(image_ref, sorted_imgs, rel_to_file_map, ref_idx)
                if not img_file:
                    continue
                with docx_zip.open(img_file) as img_data_file:
                    image_data = img_data_file.read()
                if len(image_data) < 100:
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
                        'sequence_in_page': image_ref['reference_number'] + 1,
                        'bbox': None,
                        'bbox_norm': None,
                        'page_size': None,
                        'ext': 'png',
                        'extraction_method': 'enhanced_docx_with_formatting',
                    }
                    self.processed_images.append(image_info)
                    self.placeholders[placeholder_name] = s3_key
                    self._store_image_metadata(image_info)
                    current_text = current_text.replace(image_ref['marker'], f"\n![{placeholder_name}](s3://{S3_BUCKET}/{s3_key})\n")
                    self.image_counter += 1
            except Exception as e:
                logger.error(f"Failed to process image reference {ref_idx}: {e}")
                continue
        current_text = re.sub(r'__IMAGE_PLACEHOLDER_\d+__', '', current_text)
        current_text = re.sub(r'\n\s*\n\s*\n', '\n\n', current_text)
        return current_text.strip()

    def _strip_formatting_markers(self, formatted_text: str) -> str:
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

    def _upload_image_to_s3(self, image_data: bytes, placeholder_name: str, original_filename: str) -> Optional[str]:
        if not S3_BUCKET:
            return None
        try:
            yyyy, mm, dd, hh = _now_parts()
            s3_key = f"extracted_images/{yyyy}/{mm}/{dd}/{hh}/{self.document_id}/{placeholder_name}.png"
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
                    'source': 'docx',
                }
            )
            return s3_key
        except Exception as e:
            logger.error(f"S3 upload failed for {placeholder_name}: {e}")
            return None

    def _store_image_metadata(self, image_info: Dict[str, Any]) -> None:
        if not images_table:
            return
        try:
            ttl = datetime.utcnow() + timedelta(days=30)
            image_id = f"{self.document_id}_{image_info.get('reference_number', 0)}_{int(time.time() * 1000)}"
            item = {
                'document_id': self.document_id,
                'image_id': image_id,
                'image_number': image_info.get('image_number', 0),
                'reference_number': image_info.get('reference_number', 0),
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
                'extraction_method': image_info.get('extraction_method', 'unknown'),
                'processing_timestamp': self.processing_timestamp,
                'upload_timestamp': image_info.get('upload_timestamp'),
                'ai_processed': False,
                'ttl': int(ttl.timestamp()),
            }
            images_table.put_item(Item=item)
        except Exception as e:
            logger.error(f"DynamoDB storage failed for {image_info.get('placeholder')}: {e}")

    def _save_text_files_to_s3(self, formatted_text: str) -> Dict[str, str]:
        if not S3_BUCKET:
            raise Exception("S3_BUCKET not configured")
        yyyy, mm, dd, _ = _now_parts()
        base_path = f"document_extractions/{yyyy}/{mm}/{dd}/{self.document_id}"
        file_metadata = {
            'document_id': self.document_id,
            'extraction_method': 'markdown_inline_markers',
            'processing_timestamp': self.processing_timestamp,
            'character_count': str(len(formatted_text)),
            'images_processed': str(len(self.processed_images)),
            'extraction_timestamp': datetime.utcnow().isoformat(),
            'module_id': self.module_id or '',
            'assignment_id': self.assignment_id or '',
            'student_id': self.student_id or '',
        }
        formatted_s3_key = f"{base_path}/formatted_text.md"
        s3_client.put_object(
            Bucket=S3_BUCKET, Key=formatted_s3_key,
            Body=formatted_text.encode('utf-8'),
            ContentType='text/markdown; charset=utf-8',
            Metadata=file_metadata
        )
        plain_text = self._strip_formatting_markers(formatted_text)
        plain_s3_key = f"{base_path}/plain_text.txt"
        s3_client.put_object(
            Bucket=S3_BUCKET, Key=plain_s3_key,
            Body=plain_text.encode('utf-8'),
            ContentType='text/plain; charset=utf-8',
            Metadata=file_metadata
        )
        extraction_metadata = {
            'document_id': self.document_id,
            'processing_timestamp': self.processing_timestamp,
            'extraction_timestamp': datetime.utcnow().isoformat(),
            'extraction_method': 'markdown_inline_markers',
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
            'module_id': self.module_id,
            'assignment_id': self.assignment_id,
            'student_id': self.student_id,
            'images': [
                {
                    'placeholder': img.get('placeholder'),
                    's3_location': f"s3://{S3_BUCKET}/{img.get('s3_key')}",
                    'original_filename': img.get('original_filename'),
                    'size_bytes': img.get('size_bytes'),
                    'page_number': img.get('page_number'),
                    'sequence_in_page': img.get('sequence_in_page'),
                } for img in self.processed_images
            ],
        }
        metadata_s3_key = f"{base_path}/metadata.json"
        s3_client.put_object(
            Bucket=S3_BUCKET, Key=metadata_s3_key,
            Body=json.dumps(extraction_metadata, indent=2).encode('utf-8'),
            ContentType='application/json; charset=utf-8',
            Metadata=file_metadata
        )
        summary_report = self._generate_summary_report(self._strip_formatting_markers(formatted_text), extraction_metadata)
        summary_s3_key = f"{base_path}/extraction_summary.txt"
        s3_client.put_object(
            Bucket=S3_BUCKET, Key=summary_s3_key,
            Body=summary_report.encode('utf-8'),
            ContentType='text/plain; charset=utf-8',
            Metadata=file_metadata
        )
        return {'formatted_s3_key': formatted_s3_key, 'plain_s3_key': plain_s3_key}

    def _generate_summary_report(self, plain_text: str, metadata: dict) -> str:
        lines = [
            "=" * 60,
            "DOCUMENT EXTRACTION SUMMARY REPORT",
            "=" * 60,
            "",
            f"Document ID: {metadata['document_id']}",
            f"Processing Date: {metadata['extraction_timestamp']}",
            f"Extraction Method: {metadata['extraction_method']}",
            "",
            "CONTENT STATISTICS:",
            f"  - Plain Text Length: {metadata['plain_character_count']:,} characters",
            f"  - Images Extracted: {metadata['images_detected']}",
            f"  - Formatting Preserved: {'Yes' if metadata.get('formatting_preserved') else 'No'}",
            "",
            "FILE LOCATIONS:",
            f"  - Formatted Text: {metadata['file_locations']['formatted_text']}",
            f"  - Plain Text: {metadata['file_locations']['plain_text']}",
            f"  - Metadata: {metadata['file_locations']['metadata']}",
            "",
            "CONTENT PREVIEW:",
            "-" * 40,
            plain_text[:500] + ("..." if len(plain_text) > 500 else ""),
            "",
            "=" * 60,
            "END OF SUMMARY REPORT",
            "=" * 60,
        ]
        return "\n".join(lines)

    def _store_formatted_text(self, formatted_text: str) -> bool:
        if not text_table:
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
                'extraction_method': 'markdown_inline_markers',
                'formatting_preserved': True,
                'pages_processed': 1,
                'images_processed': len(self.processed_images),
                'placeholders': self.placeholders,
                'module_id': self.module_id,
                'assignment_id': self.assignment_id,
                'student_id': self.student_id,
                'ttl': int(ttl.timestamp()),
            }
            text_table.put_item(Item=item)
            return True
        except Exception as e:
            logger.error(f"DynamoDB text storage failed: {e}")
            return False

    def _fallback_formatted_extraction(self, docx_zip: zipfile.ZipFile) -> Tuple[str, List[Dict], Dict]:
        try:
            with docx_zip.open('word/document.xml') as doc_xml:
                xml_content = doc_xml.read().decode('utf-8')
                text_content = re.sub(r'<.*?>', '', xml_content)
                text_content = re.sub(r'\s+', ' ', text_content).strip()
                return text_content, [], {'tables_count': 0, 'headings_count': 0}
        except Exception as e:
            logger.error(f"Fallback extraction failed: {e}")
            return "", [], {'tables_count': 0, 'headings_count': 0}

def lambda_handler(event: Dict[str, Any], context) -> Dict[str, Any]:
    request_id = getattr(context, 'aws_request_id', str(uuid.uuid4()))
    try:
        if event.get('action') == 'health_check':
            return {
                'statusCode': 200,
                'body': json.dumps({'status': 'healthy', 'service': 'unified-extractor', 'request_id': request_id}),
                'headers': {'Content-Type': 'application/json'}
            }
        if 'Records' in event and event['Records']:
            results: List[Dict[str, Any]] = []
            for record in event['Records']:
                try:
                    message_body = json.loads(record['body'])
                    file_info = message_body['file_info']
                    s3_key = file_info['key']
                    s3_bucket = file_info.get('bucket') or S3_BUCKET
                    original_filename = Path(s3_key).name
                    document_id = generate_unique_document_id(original_filename)
                    module_id, assignment_id, student_id = _parse_student_path_from_key(s3_key)
                    _emit_event("DocumentExtractionStarted", {
                        "document_id": document_id,
                        "bucket": s3_bucket,
                        "s3_key": s3_key,
                        "module_id": module_id,
                        "assignment_id": assignment_id,
                        "student_id": student_id,
                        "timestamp": datetime.utcnow().isoformat()
                    })
                    local_path = f"/tmp/{document_id}_{original_filename}"
                    s3_client.download_file(s3_bucket, s3_key, local_path)
                    processor = EnhancedDocumentProcessor(document_id)
                    processor.module_id = module_id
                    processor.assignment_id = assignment_id
                    processor.student_id = student_id
                    result = processor.process_document(local_path)
                    _emit_event("DocumentExtractionCompleted", {
                        "document_id": document_id,
                        "bucket": s3_bucket,
                        "s3_key": s3_key,
                        "module_id": module_id,
                        "assignment_id": assignment_id,
                        "student_id": student_id,
                        "images_extracted": result.get("images_extracted", 0),
                        "timestamp": datetime.utcnow().isoformat()
                    })
                    results.append(result)
                except Exception as e:
                    try:
                        _emit_event("DocumentExtractionFailed", {
                            "document_id": document_id if 'document_id' in locals() else None,
                            "bucket": s3_bucket if 's3_bucket' in locals() else S3_BUCKET,
                            "s3_key": s3_key if 's3_key' in locals() else None,
                            "error": str(e),
                            "timestamp": datetime.utcnow().isoformat()
                        })
                    except Exception:
                        pass
                    logger.error(f"SQS record failed: {e}")
                    results.append({'success': False, 'error': str(e), 'traceback': traceback.format_exc()})
            successful = len([r for r in results if r.get('success')])
            return {
                'statusCode': 200 if successful > 0 else 400,
                'body': json.dumps({'success': successful > 0, 'results': results, 'request_id': request_id}),
                'headers': {'Content-Type': 'application/json'}
            }
        s3_key = event.get('s3_key') or event.get('key')
        s3_bucket = event.get('s3_bucket') or S3_BUCKET
        if not s3_bucket or not s3_key:
            return {'statusCode': 400, 'body': json.dumps({'success': False, 'error': 'missing s3_bucket/s3_key'})}
        original_filename = event.get('original_filename') or Path(s3_key).name
        document_id = generate_unique_document_id(original_filename)
        module_id, assignment_id, student_id = _parse_student_path_from_key(s3_key)
        _emit_event("DocumentExtractionStarted", {
            "document_id": document_id,
            "bucket": s3_bucket,
            "s3_key": s3_key,
            "module_id": module_id,
            "assignment_id": assignment_id,
            "student_id": student_id,
            "timestamp": datetime.utcnow().isoformat()
        })
        local_path = f"/tmp/{document_id}_{original_filename}"
        s3_client.download_file(s3_bucket, s3_key, local_path)
        processor = EnhancedDocumentProcessor(document_id)
        processor.module_id = module_id
        processor.assignment_id = assignment_id
        processor.student_id = student_id
        result = processor.process_document(local_path)
        _emit_event("DocumentExtractionCompleted", {
            "document_id": document_id,
            "bucket": s3_bucket,
            "s3_key": s3_key,
            "module_id": module_id,
            "assignment_id": assignment_id,
            "student_id": student_id,
            "images_extracted": result.get("images_extracted", 0),
            "timestamp": datetime.utcnow().isoformat()
        })
        return {'statusCode': 200 if result['success'] else 500, 'body': json.dumps(result)}
    except Exception as e:
        logger.error(f"Extractor error: {e}")
        try:
            _emit_event("DocumentExtractionFailed", {
                "document_id": None,
                "bucket": s3_bucket if 's3_bucket' in locals() else S3_BUCKET,
                "s3_key": s3_key if 's3_key' in locals() else None,
                "error": str(e),
                "timestamp": datetime.utcnow().isoformat()
            })
        except Exception:
            pass
        return {'statusCode': 500, 'body': json.dumps({'success': False, 'error': str(e), 'traceback': traceback.format_exc()})}

def _detect_media_type_from_key(key: str) -> str:
    k = key.lower()
    if k.endswith(('.jpg', '.jpeg')):
        return 'image/jpeg'
    if k.endswith('.png'):
        return 'image/png'
    if k.endswith('.gif'):
        return 'image/gif'
    if k.endswith(('.tif', '.tiff')):
        return 'image/tiff'
    if k.endswith('.bmp'):
        return 'image/bmp'
    return 'image/png'

def _bedrock_analyze_image(image_bytes: bytes, media_type: str = 'image/png') -> str:
    try:
        b64_img = base64.b64encode(image_bytes).decode('utf-8')
        body = {
            "anthropic_version": "bedrock-2023-05-31",
            "max_tokens": ANALYSIS_MAX_TOKENS,
            "temperature": ANALYSIS_TEMPERATURE,
            "messages": [
                {
                    "role": "user",
                    "content": [
                        {"type": "text", "text": ANALYSIS_PROMPT},
                        {"type": "image", "source": {"type": "base64", "media_type": media_type, "data": b64_img}}
                    ]
                }
            ]
        }
        response = bedrock_runtime.invoke_model(modelId=ANALYSIS_MODEL_ID, body=json.dumps(body).encode('utf-8'))
        payload = json.loads(response.get('body', '{}'))
        for block in payload.get('content', []):
            if block.get('type') == 'text' and block.get('text'):
                return block['text'].strip()
        return "_no text from model_"
    except Exception as e:
        logger.error(f"Bedrock analysis failed: {e}")
        return f"_Image analysis failed: {e}_"

def _analysis_block(idx: int, placeholder: str, analysis_md: str, img_s3_uri: str) -> str:
    return (
        f"---\n"
        f"**Image {idx} Analysis:**\n\n"
        f"{analysis_md}\n\n"
        f"*({img_s3_uri})*\n"
        f"---\n"
    )

def image_ai_consumer_handler(event: Dict[str, Any], context) -> Dict[str, Any]:
    request_id = getattr(context, 'aws_request_id', str(uuid.uuid4()))
    try:
        if 'Records' not in event or not event['Records']:
            return {'statusCode': 200, 'body': json.dumps({'ok': True, 'message': 'no records'})}
        results = []
        for record in event['Records']:
            try:
                msg = json.loads(record['body'])
                document_id = msg['document_id']
                s3_base_path = msg['s3_base_path']
                images = msg.get('images', [])
                formatted_text_s3_key = msg.get('formatted_text_s3_key')
                module_id = msg.get('module_id')
                assignment_id = msg.get('assignment_id')
                student_id = msg.get('student_id')
                m = re.match(r'^s3://([^/]+)/document_extractions/(\d{4})/(\d{2})/(\d{2})/([^/]+)/?$', s3_base_path.rstrip('/'))
                if not m:
                    raise Exception(f"Invalid s3_base_path: {s3_base_path}")
                bucket, yyyy, mm, dd, doc_from_path = m.groups()
                base_prefix = f"document_extractions/{yyyy}/{mm}/{dd}/{doc_from_path}"
                if not formatted_text_s3_key:
                    formatted_text_s3_key = f"{base_prefix}/formatted_text.md"
                obj = s3_client.get_object(Bucket=bucket, Key=formatted_text_s3_key)
                formatted_text = obj['Body'].read().decode('utf-8')
                analyses_for_manifest: List[Dict[str, Any]] = []
                for i, img in enumerate(images, start=1):
                    placeholder = img['placeholder']
                    img_key = img['s3_key']
                    media_type = _detect_media_type_from_key(img_key)
                    img_obj = s3_client.get_object(Bucket=bucket, Key=img_key)
                    img_bytes = img_obj['Body'].read()
                    analysis_md = _bedrock_analyze_image(img_bytes, media_type=media_type)
                    block = _analysis_block(i, placeholder, analysis_md, f"s3://{bucket}/{img_key}")
                    pat_md = re.compile(r'!\[' + re.escape(placeholder) + r'\]\([^)]+\)')
                    formatted_text, n1 = pat_md.subn(block, formatted_text, count=1)
                    if n1 == 0:
                        pat_html = re.compile(r'<!--\s*' + re.escape(placeholder) + r'\s*-->')
                        formatted_text, _ = pat_html.subn(block, formatted_text, count=1)
                    analyses_for_manifest.append({
                        "placeholder": placeholder,
                        "s3_image": f"s3://{bucket}/{img_key}",
                        "page_number": img.get("page_number"),
                        "sequence_in_page": img.get("sequence_in_page"),
                        "analysis_markdown": analysis_md
                    })
                    if images_table:
                        try:
                            images_table.update_item(
                                Key={
                                    'document_id': document_id,
                                    'image_id': f"{document_id}_{img.get('reference_number',0)}_{(img.get('upload_timestamp','')).replace(':','').replace('-','').replace('.','') or 't'}"
                                },
                                UpdateExpression="SET ai_processed = :true, ai_processed_timestamp = :ts",
                                ExpressionAttributeValues={':true': True, ':ts': datetime.utcnow().isoformat()}
                            )
                        except Exception:
                            pass
                reconstructed_key_base = f"{base_prefix}/reconstructed_text.md"
                s3_client.put_object(
                    Bucket=bucket, Key=reconstructed_key_base,
                    Body=formatted_text.encode('utf-8'),
                    ContentType='text/markdown; charset=utf-8',
                    Metadata={'document_id': document_id, 'reconstructed': 'true', 'module_id': module_id or '', 'assignment_id': assignment_id or '', 'student_id': student_id or ''}
                )
                legacy_prefix = f"reconstructed_documents/{yyyy}/{mm}/{dd}/{document_id}"
                s3_client.put_object(
                    Bucket=bucket, Key=f"{legacy_prefix}/final_document.md",
                    Body=formatted_text.encode('utf-8'),
                    ContentType='text/markdown; charset=utf-8'
                )
                s3_client.put_object(
                    Bucket=bucket, Key=f"{legacy_prefix}/plain_text.txt",
                    Body=_md_strip(formatted_text).encode('utf-8'),
                    ContentType='text/plain; charset=utf-8'
                )
                recon_meta = {
                    "document_id": document_id,
                    "generated_at": datetime.utcnow().isoformat(),
                    "source_formatted_text": f"s3://{bucket}/{formatted_text_s3_key}",
                    "base_reconstructed_md": f"s3://{bucket}/{reconstructed_key_base}",
                    "images_count": len(images),
                    "module_id": module_id,
                    "assignment_id": assignment_id,
                    "student_id": student_id,
                    "analyses": analyses_for_manifest
                }
                s3_client.put_object(
                    Bucket=bucket, Key=f"{legacy_prefix}/reconstruction_metadata.json",
                    Body=json.dumps(recon_meta, indent=2).encode('utf-8'),
                    ContentType='application/json; charset=utf-8'
                )
                summary_lines = [
                    f"Document: {document_id}",
                    f"Generated: {datetime.utcnow().isoformat()}",
                    f"Images analyzed: {len(images)}",
                    "",
                    "Markers replaced (first 5):",
                    *[f"  - {a['placeholder']} (p{a.get('page_number')}, seq {a.get('sequence_in_page')})" for a in analyses_for_manifest[:5]],
                    "",
                    f"Base reconstructed MD: s3://{bucket}/{reconstructed_key_base}"
                ]
                s3_client.put_object(
                    Bucket=bucket, Key=f"{legacy_prefix}/reconstruction_summary.txt",
                    Body=("\n".join(summary_lines)).encode('utf-8'),
                    ContentType='text/plain; charset=utf-8'
                )
                s3_client.put_object(
                    Bucket=bucket, Key=f"{legacy_prefix}/comparison_analysis.md",
                    Body="(auto-generated) No baseline document provided for comparison.\n".encode('utf-8'),
                    ContentType='text/markdown; charset=utf-8'
                )
                results.append({
                    'document_id': document_id,
                    'base_reconstructed': f"s3://{bucket}/{reconstructed_key_base}",
                    'legacy_folder': f"s3://{bucket}/{legacy_prefix}/"
                })
            except Exception as e:
                logger.error(f"Consumer record failed: {e}")
                results.append({'error': str(e), 'traceback': traceback.format_exc()})
        return {'statusCode': 200, 'body': json.dumps({'ok': True, 'results': results, 'request_id': request_id})}
    except Exception as e:
        logger.error(f"Consumer error: {e}")
        return {
            'statusCode': 500,
            'body': json.dumps({'ok': False, 'error': str(e), 'traceback': traceback.format_exc(), 'request_id': request_id})
        }
