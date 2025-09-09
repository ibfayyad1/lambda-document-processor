# -*- coding: utf-8 -*-
"""
Unified DOCX/PDF Extractor + Image-AI Consumer

- One class: DocumentProcessor
- DOCX & PDF -> Markdown with inline image markers: ![IMAGE_*](s3://bucket/key)
- Sends a single SQS/Lambda trigger with image metadata
- Consumer (image_ai_consumer_handler) analyzes each image via Bedrock and
  replaces the inline marker with a visible analysis block.
- Final artifacts written to:
  A) s3://<bucket>/document_extractions/YYYY/MM/DD/{document_id}/reconstructed_text.md
  B) s3://<bucket>/reconstructed_documents/YYYY/MM/DD/{document_id}/
       final_document.md
       plain_text.txt
       reconstruction_metadata.json
       reconstruction_summary.txt
       comparison_analysis.md
"""

import os
import re
import json
import time
import uuid
import base64
import zipfile
import logging
import traceback
from pathlib import Path
from datetime import datetime
from typing import Dict, Any, List, Optional, Tuple

import boto3

# Optional PDF support
try:
    import fitz  # PyMuPDF
except Exception:
    fitz = None

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# --------------------- ENV ---------------------
AWS_REGION = os.environ.get("AWS_REGION", "us-east-1")
S3_BUCKET = os.environ.get("S3_BUCKET")
IMAGE_PROCESSING_QUEUE_URL = os.environ.get("IMAGE_BATCH_QUEUE_URL", "")
IMAGE_PROCESSOR_LAMBDA_ARN = os.environ.get("IMAGE_PROCESSOR_LAMBDA_ARN", "")
USE_ASYNC_PROCESSING = os.environ.get("USE_ASYNC_PROCESSING", "true").lower() == "true"
MAX_FILE_SIZE = int(os.environ.get("MAX_FILE_SIZE", "104857600"))  # 100 MB

# Bedrock (consumer) defaults
ANALYSIS_MODEL_ID = os.environ.get("ANALYSIS_MODEL_ID", "anthropic.claude-3-7-sonnet-20250219-v1:0")
ANALYSIS_MAX_TOKENS = int(os.environ.get("ANALYSIS_MAX_TOKENS", "800"))
ANALYSIS_TEMPERATURE = float(os.environ.get("ANALYSIS_TEMPERATURE", "0.0"))
ANALYSIS_PROMPT = os.environ.get(
    "ANALYSIS_PROMPT",
    "You are an expert visual analyst. Provide a concise, factual, Markdown-formatted analysis of the image. "
    "Include: a one-sentence caption, key elements, any text detected (OCR), any tables (as Markdown), "
    "and relevant insights for academic assignment grading."
)

# --------------------- AWS Clients ---------------------
s3_client = boto3.client("s3", region_name=AWS_REGION)
sqs_client = boto3.client("sqs", region_name=AWS_REGION)
lambda_client = boto3.client("lambda", region_name=AWS_REGION)
bedrock_runtime = boto3.client("bedrock-runtime", region_name=AWS_REGION)

# --------------------- Helpers ---------------------
def _now_parts():
    dt = datetime.utcnow()
    return dt.strftime("%Y"), dt.strftime("%m"), dt.strftime("%d"), dt.strftime("%H")

def _unique_document_id(original_filename: Optional[str] = None) -> str:
    ts = datetime.utcnow().strftime("%Y%m%d_%H%M%S")
    micro = datetime.utcnow().microsecond
    rand = str(uuid.uuid4())[:8]
    if original_filename:
        base = Path(original_filename).stem
        base = re.sub(r"[^\w\-]+", "_", base)[:30]
        return f"{base}_{ts}_{micro}_{rand}"
    return f"doc_{ts}_{micro}_{rand}"

def _md_strip(md: str) -> str:
    t = re.sub(r"```.*?```", "", md, flags=re.DOTALL)            # code fences
    t = re.sub(r"!\[[^\]]*\]\([^)]+\)", "", t)                   # images
    t = re.sub(r"\[([^\]]+)\]\([^)]+\)", r"\1", t)               # links
    t = re.sub(r"[#>*_`~-]+", " ", t)                            # md punctuation
    t = re.sub(r"\n{3,}", "\n\n", t)
    return t.strip()

# --------------------- Document Processor (DOCX + PDF) ---------------------
class DocumentProcessor:
    """
    Produces Markdown with inline markers for both DOCX and PDF:
      ![IMAGE_*](s3://bucket/key)
    """
    NAMESPACES = {
        "w": "http://schemas.openxmlformats.org/wordprocessingml/2006/main",
        "pic": "http://schemas.openxmlformats.org/drawingml/2006/picture",
        "a": "http://schemas.openxmlformats.org/drawingml/2006/main",
        "r": "http://schemas.openxmlformats.org/officeDocument/2006/relationships",
        "wp": "http://schemas.openxmlformats.org/drawingml/2006/wordprocessingDrawing",
    }

    def __init__(self, document_id: str):
        self.document_id = document_id
        self.image_counter = 1
        self.processed_images: List[Dict[str, Any]] = []
        self.processing_timestamp = datetime.utcnow().isoformat()

    # --------- Public entry ---------
    def process_document(self, local_path: str) -> Dict[str, Any]:
        if not os.path.exists(local_path):
            raise FileNotFoundError(local_path)
        if os.path.getsize(local_path) > MAX_FILE_SIZE:
            raise RuntimeError(f"File too large: {os.path.getsize(local_path)} bytes")

        lower = local_path.lower()
        if lower.endswith(".docx"):
            result = self._extract_docx(local_path)
            method = "docx_markdown_inline"
        elif lower.endswith(".pdf"):
            result = self._extract_pdf(local_path)
            method = "pdf_markdown_inline"
        else:
            raise RuntimeError("Unsupported file type")

        if not result["formatted_text"].strip():
            raise RuntimeError("No text extracted")

        formatted_s3_key, plain_s3_key = self._write_text_artifacts(result["formatted_text"])
        ai_trigger = self._trigger_ai(
            formatted_text=result["formatted_text"],
            formatted_text_s3_key=formatted_s3_key,
            method=method
        )

        yyyy, mm, dd, _ = _now_parts()
        base_prefix = f"document_extractions/{yyyy}/{mm}/{dd}/{self.document_id}"

        return {
            "success": True,
            "document_id": self.document_id,
            "formatted_text_s3": f"s3://{S3_BUCKET}/{formatted_s3_key}",
            "plain_text_s3": f"s3://{S3_BUCKET}/{plain_s3_key}",
            "images_detected": len(self.processed_images),
            "output_base": f"s3://{S3_BUCKET}/{base_prefix}/",
            "ai_processing": ai_trigger,
            "extraction_method": method,
        }

    # --------- DOCX ---------
    def _extract_docx(self, local_path: str) -> Dict[str, Any]:
        import xml.etree.ElementTree as ET

        with zipfile.ZipFile(local_path, "r") as z:
            # document.xml
            with z.open("word/document.xml") as f:
                xml = f.read().decode("utf-8")
            root = ET.fromstring(xml)

            formatted_parts: List[str] = []
            image_refs: List[Dict[str, Any]] = []
            ref_counter = 0

            body = root.find(".//w:body", self.NAMESPACES)
            if body is not None:
                for el in body:
                    if el.tag.endswith("}p"):
                        # runs
                        runs = el.findall(".//w:r", self.NAMESPACES)
                        buf = []
                        for r in runs:
                            # text
                            for t in r.findall(".//w:t", self.NAMESPACES):
                                if t.text:
                                    buf.append(t.text)

                            # drawings (images)
                            drawings = r.findall(".//w:drawing", self.NAMESPACES)
                            for d in drawings:
                                pic = d.findall(".//pic:pic", self.NAMESPACES)
                                if pic:
                                    marker = f"__IMAGE_PLACEHOLDER_{ref_counter}__"
                                    buf.append(f" {marker} ")
                                    # get relationship id
                                    blips = d.findall(".//a:blip", self.NAMESPACES)
                                    rid = blips[0].get("{http://schemas.openxmlformats.org/officeDocument/2006/relationships}embed") if blips else None
                                    image_refs.append({"marker": marker, "relationship_id": rid, "ref": ref_counter})
                                    ref_counter += 1

                        txt = "".join(buf).strip()
                        if txt:
                            formatted_parts.append(txt)

            formatted = "\n\n".join(formatted_parts)

            # map rel id -> media path
            rel_map: Dict[str, str] = {}
            try:
                with z.open("word/_rels/document.xml.rels") as f:
                    rel_xml = f.read().decode("utf-8")
                rel_root = ET.fromstring(rel_xml)
                for r in rel_root.findall(
                    ".//{http://schemas.openxmlformats.org/package/2006/relationships}Relationship"
                ):
                    rid = r.get("Id")
                    target = r.get("Target")
                    rtype = r.get("Type") or ""
                    if "image" in rtype and target:
                        p = f"word/{target}" if target.startswith("media/") else target
                        rel_map[rid] = p
            except Exception:
                pass

            # list all media files
            media_files = [n for n in z.namelist() if n.startswith("word/media/")]
            media_files_sorted = sorted(media_files, key=lambda s: int(re.findall(r"\d+", s)[0]) if re.findall(r"\d+", s) else 0)

            # replace placeholders with uploaded images
            out = formatted
            for i, ref in enumerate(image_refs):
                img_path = rel_map.get(ref["relationship_id"]) or (media_files_sorted[i % len(media_files_sorted)] if media_files_sorted else None)
                if not img_path:
                    continue
                with z.open(img_path) as f:
                    img_bytes = f.read()
                placeholder = f"IMAGE_{self.image_counter}_{int(time.time()*1000)}"
                yyyy, mm, dd, hh = _now_parts()
                key = f"extracted_images/{yyyy}/{mm}/{dd}/{hh}/{self.document_id}/{placeholder}.png"
                s3_client.put_object(
                    Bucket=S3_BUCKET, Key=key, Body=img_bytes, ContentType="image/png",
                    Metadata={"document_id": self.document_id, "source": "docx"}
                )

                self.processed_images.append({
                    "placeholder": placeholder,
                    "s3_key": key,
                    "page_number": 1,
                    "sequence_in_page": ref["ref"] + 1,
                })
                out = out.replace(ref["marker"], f"\n![{placeholder}](s3://{S3_BUCKET}/{key})\n")
                self.image_counter += 1

            out = re.sub(r"__IMAGE_PLACEHOLDER_\d+__", "", out)
            return {"formatted_text": out, "plain_text": _md_strip(out)}

    # --------- PDF ---------
    def _extract_pdf(self, local_path: str) -> Dict[str, Any]:
        if fitz is None:
            raise RuntimeError("PyMuPDF (fitz) not available")

        pdf = fitz.open(local_path)
        inline_parts: List[str] = []
        plain_parts: List[str] = []

        for pidx in range(len(pdf)):
            page = pdf[pidx]
            ptxt = page.get_text("text")
            if ptxt.strip():
                plain_parts.append(ptxt)

            pdict = page.get_text("dict")
            seq_in_page = 0
            for blk in pdict.get("blocks", []):
                if blk.get("type") == 0:
                    # text block
                    txt = " ".join(
                        span.get("text", "")
                        for line in blk.get("lines", [])
                        for span in line.get("spans", [])
                    ).strip()
                    if txt:
                        inline_parts.append(txt)
                elif blk.get("type") == 1:
                    # image block
                    seq_in_page += 1
                    img_bytes = blk.get("image")
                    ext = (blk.get("ext") or "png").lower()
                    if not img_bytes:
                        continue

                    placeholder = f"IMAGE_{self.image_counter}_{int(time.time()*1000)}"
                    yyyy, mm, dd, hh = _now_parts()
                    key = f"extracted_images/{yyyy}/{mm}/{dd}/{hh}/{self.document_id}/{placeholder}.{ext}"
                    s3_client.put_object(
                        Bucket=S3_BUCKET, Key=key, Body=img_bytes, ContentType=f"image/{ext}",
                        Metadata={"document_id": self.document_id, "source": "pdf"}
                    )
                    self.processed_images.append({
                        "placeholder": placeholder,
                        "s3_key": key,
                        "page_number": pidx + 1,
                        "sequence_in_page": seq_in_page,
                    })
                    inline_parts.append(f"\n![{placeholder}](s3://{S3_BUCKET}/{key})\n")
                    self.image_counter += 1

        pdf.close()
        formatted = ("\n\n".join([p for p in inline_parts if p.strip()])).strip()
        return {"formatted_text": formatted, "plain_text": "\n".join(plain_parts)}

    # --------- Write base text artifacts ---------
    def _write_text_artifacts(self, formatted_text: str) -> Tuple[str, str]:
        yyyy, mm, dd, _ = _now_parts()
        base = f"document_extractions/{yyyy}/{mm}/{dd}/{self.document_id}"
        formatted_key = f"{base}/formatted_text.md"
        plain_key = f"{base}/plain_text.txt"

        s3_client.put_object(
            Bucket=S3_BUCKET, Key=formatted_key,
            Body=formatted_text.encode("utf-8"),
            ContentType="text/markdown; charset=utf-8",
            Metadata={"document_id": self.document_id}
        )
        s3_client.put_object(
            Bucket=S3_BUCKET, Key=plain_key,
            Body=_md_strip(formatted_text).encode("utf-8"),
            ContentType="text/plain; charset=utf-8",
            Metadata={"document_id": self.document_id}
        )
        # simple metadata for discoverability
        meta = {
            "document_id": self.document_id,
            "images_detected": len(self.processed_images),
            "generated_at": datetime.utcnow().isoformat(),
            "formatted_text": f"s3://{S3_BUCKET}/{formatted_key}"
        }
        s3_client.put_object(
            Bucket=S3_BUCKET, Key=f"{base}/metadata.json",
            Body=json.dumps(meta, indent=2).encode("utf-8"),
            ContentType="application/json; charset=utf-8"
        )
        return formatted_key, plain_key

    # --------- Trigger downstream AI ---------
    def _trigger_ai(self, formatted_text: str, formatted_text_s3_key: str, method: str) -> Dict[str, Any]:
        images = [{
            "placeholder": img["placeholder"],
            "s3_key": img["s3_key"],
            "page_number": img.get("page_number"),
            "sequence_in_page": img.get("sequence_in_page"),
        } for img in self.processed_images]

        yyyy, mm, dd, _ = _now_parts()
        s3_base_path = f"s3://{S3_BUCKET}/document_extractions/{yyyy}/{mm}/{dd}/{self.document_id}/"

        message = {
            "document_id": self.document_id,
            "images": images,
            "formatted_text_s3_key": f"document_extractions/{yyyy}/{mm}/{dd}/{self.document_id}/formatted_text.md",
            "s3_base_path": s3_base_path,
            "pipeline_mode": method,
            "reconstruction": {
                "output_reconstructed_key": "reconstructed_text.md",
                "reconstructed_documents_dir": "reconstructed_documents"
            }
        }

        try:
            if USE_ASYNC_PROCESSING and IMAGE_PROCESSING_QUEUE_URL:
                resp = sqs_client.send_message(
                    QueueUrl=IMAGE_PROCESSING_QUEUE_URL,
                    MessageBody=json.dumps(message),
                    MessageAttributes={
                        "DocumentId": {"StringValue": self.document_id, "DataType": "String"},
                        "ImagesCount": {"StringValue": str(len(images)), "DataType": "Number"},
                        "PipelineMode": {"StringValue": method, "DataType": "String"},
                    }
                )
                return {"triggered": True, "method": "sqs", "message_id": resp.get("MessageId")}
            elif IMAGE_PROCESSOR_LAMBDA_ARN:
                lambda_client.invoke(
                    FunctionName=IMAGE_PROCESSOR_LAMBDA_ARN,
                    InvocationType="Event",
                    Payload=json.dumps(message).encode("utf-8")
                )
                return {"triggered": True, "method": "lambda"}
            else:
                return {"triggered": False, "reason": "no_queue_or_lambda"}
        except Exception as e:
            logger.error(f"AI trigger failed: {e}")
            return {"triggered": False, "error": str(e)}


# --------------------- Extractor Lambda Handler ---------------------
def extractor_lambda_handler(event: Dict[str, Any], context) -> Dict[str, Any]:
    """Direct invoke or SQS batch for extraction."""
    req_id = getattr(context, "aws_request_id", str(uuid.uuid4()))
    try:
        if event.get("action") == "health_check":
            return {"statusCode": 200, "body": json.dumps({"ok": True, "service": "unified-extractor"})}

        # SQS batch (incoming files to extract)
        if "Records" in event and event["Records"]:
            results = []
            for rec in event["Records"]:
                try:
                    body = json.loads(rec["body"])
                    s3_key = body["file_info"]["key"]
                    original_filename = Path(s3_key).name
                    document_id = _unique_document_id(original_filename)

                    local = f"/tmp/{document_id}_{original_filename}"
                    s3_client.download_file(S3_BUCKET, s3_key, local)
                    proc = DocumentProcessor(document_id)
                    out = proc.process_document(local)
                    results.append(out)
                    try:
                        os.unlink(local)
                    except Exception:
                        pass
                except Exception as e:
                    logger.error(f"SQS extract failed: {e}")
                    results.append({"success": False, "error": str(e), "traceback": traceback.format_exc()})
            return {"statusCode": 200, "body": json.dumps({"ok": True, "results": results, "request_id": req_id})}

        # Direct invoke
        s3_key = event.get("s3_key") or event.get("key")
        s3_bucket = event.get("s3_bucket") or S3_BUCKET
        if not s3_bucket or not s3_key:
            return {"statusCode": 400, "body": json.dumps({"ok": False, "error": "missing s3_bucket/s3_key"})}

        original_filename = event.get("original_filename") or Path(s3_key).name
        document_id = _unique_document_id(original_filename)
        local = f"/tmp/{document_id}_{original_filename}"
        s3_client.download_file(s3_bucket, s3_key, local)
        proc = DocumentProcessor(document_id)
        out = proc.process_document(local)
        try:
            os.unlink(local)
        except Exception:
            pass
        return {"statusCode": 200, "body": json.dumps(out)}
    except Exception as e:
        logger.error(f"extractor error: {e}")
        return {"statusCode": 500, "body": json.dumps({"ok": False, "error": str(e), "traceback": traceback.format_exc()})}


# --------------------- Consumer (SQS -> Bedrock -> Reconstruct) ---------------------
def _detect_media_type_from_key(key: str) -> str:
    k = key.lower()
    if k.endswith((".jpg", ".jpeg")): return "image/jpeg"
    if k.endswith(".png"): return "image/png"
    if k.endswith(".gif"): return "image/gif"
    if k.endswith((".tif", ".tiff")): return "image/tiff"
    if k.endswith(".bmp"): return "image/bmp"
    return "image/png"

def _bedrock_analyze_image(image_bytes: bytes, media_type: str = "image/png") -> str:
    """Anthropic on Bedrock — returns Markdown text."""
    try:
        b64 = base64.b64encode(image_bytes).decode("utf-8")
        body = {
            "anthropic_version": "bedrock-2023-05-31",
            "max_tokens": ANALYSIS_MAX_TOKENS,
            "temperature": ANALYSIS_TEMPERATURE,
            "messages": [
                {
                    "role": "user",
                    "content": [
                        {"type": "text", "text": ANALYSIS_PROMPT},
                        {"type": "image", "source": {"type": "base64", "media_type": media_type, "data": b64}},
                    ],
                }
            ],
        }
        resp = bedrock_runtime.invoke_model(modelId=ANALYSIS_MODEL_ID, body=json.dumps(body).encode("utf-8"))
        payload = json.loads(resp.get("body", "{}"))
        # Anthropic messages returns list of blocks under "content"
        for blk in payload.get("content", []):
            if blk.get("type") == "text" and blk.get("text"):
                return blk["text"].strip()
        return "_(no text in model response)_"
    except Exception as e:
        logger.error(f"Bedrock analysis failed: {e}")
        return f"_Image analysis failed: {e}_"

def _analysis_block(idx: int, placeholder: str, analysis_md: str, img_key: str) -> str:
    return (
        f"---\n"
        f"**Image {idx} Analysis:**\n\n"
        f"{analysis_md}\n\n"
        f"*({img_key})*\n"
        f"---\n"
    )

def image_ai_consumer_handler(event: Dict[str, Any], context) -> Dict[str, Any]:
    """
    Replaces inline markers with visible analysis blocks and writes outputs to both base & legacy paths.
    """
    req_id = getattr(context, "aws_request_id", str(uuid.uuid4()))
    try:
        if "Records" not in event or not event["Records"]:
            return {"statusCode": 200, "body": json.dumps({"ok": True, "message": "no records"})}

        results = []
        for record in event["Records"]:
            msg = json.loads(record["body"])
            document_id = msg["document_id"]
            s3_base_path = msg["s3_base_path"]  # s3://bucket/document_extractions/YYYY/MM/DD/{document_id}/
            images = msg.get("images", [])
            formatted_text_s3_key = msg.get("formatted_text_s3_key")

            m = re.match(r"^s3://([^/]+)/document_extractions/(\d{4})/(\d{2})/(\d{2})/([^/]+)/?$", s3_base_path.rstrip("/"))
            if not m:
                raise RuntimeError(f"Invalid s3_base_path: {s3_base_path}")
            bucket, yyyy, mm, dd, doc_from_path = m.groups()
            prefix = f"document_extractions/{yyyy}/{mm}/{dd}/{doc_from_path}"
            if not formatted_text_s3_key:
                formatted_text_s3_key = f"{prefix}/formatted_text.md"

            obj = s3_client.get_object(Bucket=bucket, Key=formatted_text_s3_key)
            formatted_text = obj["Body"].read().decode("utf-8")

            analyses_manifest: List[Dict[str, Any]] = []

            # Replace each marker with a standardized visible block
            for i, img in enumerate(images, start=1):
                placeholder = img["placeholder"]
                img_key = img["s3_key"]
                media_type = _detect_media_type_from_key(img_key)
                img_obj = s3_client.get_object(Bucket=bucket, Key=img_key)
                img_bytes = img_obj["Body"].read()

                analysis_md = _bedrock_analyze_image(img_bytes, media_type=media_type)
                block = _analysis_block(i, placeholder, analysis_md, f"s3://{bucket}/{img_key}")

                # primary: markdown image marker
                pat_md = re.compile(r"!\[" + re.escape(placeholder) + r"\]\([^)]+\)")
                formatted_text, n1 = pat_md.subn(block, formatted_text, count=1)
                # fallback: html comment marker
                if n1 == 0:
                    pat_html = re.compile(r"<!--\s*" + re.escape(placeholder) + r"\s*-->")
                    formatted_text, _ = pat_html.subn(block, formatted_text, count=1)

                analyses_manifest.append({
                    "placeholder": placeholder,
                    "s3_image": f"s3://{bucket}/{img_key}",
                    "page_number": img.get("page_number"),
                    "sequence_in_page": img.get("sequence_in_page"),
                    "analysis_markdown": analysis_md
                })

            # A) base reconstructed_text.md
            reconstructed_base_key = f"{prefix}/reconstructed_text.md"
            s3_client.put_object(
                Bucket=bucket, Key=reconstructed_base_key,
                Body=formatted_text.encode("utf-8"),
                ContentType="text/markdown; charset=utf-8",
                Metadata={"document_id": document_id, "reconstructed": "true"}
            )

            # B) legacy UI folder (like your DOCX screenshot)
            legacy_prefix = f"reconstructed_documents/{yyyy}/{mm}/{dd}/{document_id}"
            # final_document.md
            s3_client.put_object(
                Bucket=bucket, Key=f"{legacy_prefix}/final_document.md",
                Body=formatted_text.encode("utf-8"),
                ContentType="text/markdown; charset=utf-8"
            )
            # plain_text.txt
            s3_client.put_object(
                Bucket=bucket, Key=f"{legacy_prefix}/plain_text.txt",
                Body=_md_strip(formatted_text).encode("utf-8"),
                ContentType="text/plain; charset=utf-8"
            )
            # reconstruction_metadata.json
            recon_meta = {
                "document_id": document_id,
                "generated_at": datetime.utcnow().isoformat(),
                "source_formatted_text": f"s3://{bucket}/{formatted_text_s3_key}",
                "base_reconstructed_md": f"s3://{bucket}/{reconstructed_base_key}",
                "images_count": len(images),
                "analyses": analyses_manifest
            }
            s3_client.put_object(
                Bucket=bucket, Key=f"{legacy_prefix}/reconstruction_metadata.json",
                Body=json.dumps(recon_meta, indent=2).encode("utf-8"),
                ContentType="application/json; charset=utf-8"
            )
            # reconstruction_summary.txt
            lines = [
                f"Document: {document_id}",
                f"Generated: {datetime.utcnow().isoformat()}",
                f"Images analyzed: {len(images)}",
                "",
                "Markers replaced (first 5):",
                *[f"  - {a['placeholder']} (p{a.get('page_number')}, seq {a.get('sequence_in_page')})" for a in analyses_manifest[:5]],
                "",
                f"Base reconstructed MD: s3://{bucket}/{reconstructed_base_key}",
            ]
            s3_client.put_object(
                Bucket=bucket, Key=f"{legacy_prefix}/reconstruction_summary.txt",
                Body=("\n".join(lines)).encode("utf-8"),
                ContentType="text/plain; charset=utf-8"
            )
            # comparison_analysis.md (placeholder)
            s3_client.put_object(
                Bucket=bucket, Key=f"{legacy_prefix}/comparison_analysis.md",
                Body="(auto-generated) No baseline provided for comparison.\n".encode("utf-8"),
                ContentType="text/markdown; charset=utf-8"
            )

            results.append({
                "document_id": document_id,
                "base_reconstructed": f"s3://{bucket}/{reconstructed_base_key}",
                "legacy_folder": f"s3://{bucket}/{legacy_prefix}/"
            })

        return {"statusCode": 200, "body": json.dumps({"ok": True, "results": results, "request_id": req_id})}
    except Exception as e:
        logger.error(f"consumer error: {e}")
        return {"statusCode": 500, "body": json.dumps({"ok": False, "error": str(e), "traceback": traceback.format_exc()})}
