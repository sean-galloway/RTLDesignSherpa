#!/usr/bin/env python3

import argparse
import difflib
import json
import subprocess
from pathlib import Path

from structured_editor import EditError, apply_edits, select_approved_edits

ROOT = Path(__file__).resolve().parents[1]
QWEN = "/models/Qwen3.8-27B-FP8"
NEMOTRON = "/models/NVIDIA-Nemotron-3.5-Super-VL-120B-A12B-NVFP4"

QWEN_PROMPT = """You are a conservative technical copy editor. Propose only high-confidence improvements to grammar, spelling, punctuation, and genuinely unclear prose.

Return JSON only in this shape, with no code fence or preamble:
{
  "edits": [
    {
      "id": "edit-001",
      "old": "exact text copied from the document",
      "new": "replacement text",
      "reason": "specific editorial reason"
    }
  ]
}

Rules:
- Each old value must be an exact, unique, contiguous excerpt from the source document.
- Keep each edit within one paragraph and as localized as possible.
- Preserve the number and positions of line breaks. Do not join, rewrap, or reflow lines.
- Preserve technical meaning, claims, numbers, names, voice, and level of detail.
- Do not edit fenced code, headings, tables, links, images, HTML, front matter, references, or navigation.
- Do not add or remove facts, sections, examples, citations, or requirements.
- If the document is already clean, return {"edits": []}.
"""

NEMOTRON_PROMPT = """You are an independent, exacting technical-documentation reviewer. Review each proposed edit operation against the original document.

For each edit, return APPROVE only if it improves grammar, spelling, punctuation, or clarity without changing technical meaning, voice, or Markdown. DISAPPROVE unnecessary, incorrect, overly stylistic, or technically risky edits. Do not suggest unrelated changes.

Return JSON only in this shape:
{
  "reviews": [
    {
      "id": "edit-001",
      "verdict": "APPROVE | DISAPPROVE",
      "reason": "specific reason"
    }
  ]
}
Include exactly one review for every supplied edit ID.
"""


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def unified_diff(original, candidate, source_name):
    return "".join(difflib.unified_diff(
        original.splitlines(keepends=True),
        candidate.splitlines(keepends=True),
        fromfile=source_name,
        tofile=source_name + ".edited",
    ))


def call_model(host, model, messages, temperature, max_tokens, non_thinking=False):
    payload = {
        "model": model,
        "messages": messages,
        "temperature": temperature,
        "max_tokens": max_tokens,
        "stream": False,
    }
    if non_thinking:
        payload["chat_template_kwargs"] = {"enable_thinking": False}
    request = json.dumps(payload)
    result = subprocess.run(
        [
            "ssh", "-o", "BatchMode=yes", "-o", "ConnectTimeout=8", host,
            (
                "curl --fail --silent --show-error --max-time 900 "
                "http://127.0.0.1:8000/v1/chat/completions "
                "--header 'Content-Type: application/json' --data-binary @-"
            ),
        ],
        input=request,
        check=False,
        text=True,
        capture_output=True,
        timeout=920,
    )
    if result.returncode:
        raise RuntimeError(f"{host} model request failed: {result.stderr.strip()}")
    return request, json.loads(result.stdout)


def response_content(response):
    choice = response["choices"][0]
    if choice.get("finish_reason") != "stop":
        raise RuntimeError(f"model did not finish cleanly: {choice.get('finish_reason')}")
    return choice["message"]["content"]


def propose(source, original, doc_dir):
    request, response = call_model(
        "dgx1",
        QWEN,
        [
            {"role": "system", "content": QWEN_PROMPT},
            {"role": "user", "content": original},
        ],
        temperature=0.0,
        max_tokens=12000,
        non_thinking=True,
    )
    (doc_dir / "qwen_request.json").write_text(request + "\n")
    write_json(doc_dir / "qwen_response.json", response)
    content = response_content(response)
    (doc_dir / "qwen_content.txt").write_text(content.rstrip() + "\n")
    proposals = json.loads(content)["edits"]

    accepted = []
    rejected = []
    for proposal in proposals:
        try:
            apply_edits(original, accepted + [proposal])
        except (EditError, KeyError, TypeError) as error:
            rejected.append({"edit": proposal, "error": str(error)})
        else:
            accepted.append(proposal)
    candidate = apply_edits(original, accepted)

    write_json(doc_dir / "edits.json", {"edits": accepted})
    write_json(doc_dir / "rejected_edits.json", {"rejected": rejected})
    (doc_dir / "candidate.md").write_text(candidate)
    (doc_dir / "qwen_changes.diff").write_text(unified_diff(original, candidate, source.name))
    return accepted, rejected, candidate


def review(original, candidate, edits, doc_dir):
    if not edits:
        write_json(doc_dir / "nemotron_review.json", {"reviews": []})
        return []
    request, response = call_model(
        "dgx2",
        NEMOTRON,
        [
            {"role": "system", "content": NEMOTRON_PROMPT},
            {"role": "user", "content": "ORIGINAL DOCUMENT:\n" + original},
            {"role": "user", "content": "VALIDATED CANDIDATE:\n" + candidate},
            {"role": "user", "content": "EDIT OPERATIONS:\n" + json.dumps(edits, ensure_ascii=False)},
        ],
        temperature=0.0,
        max_tokens=10000,
    )
    (doc_dir / "nemotron_request.json").write_text(request + "\n")
    write_json(doc_dir / "nemotron_response.json", response)
    content = response_content(response)
    (doc_dir / "nemotron_content.txt").write_text(content.rstrip() + "\n")
    review_data = json.loads(content)
    reviews = review_data["reviews"]
    edit_ids = [edit["id"] for edit in edits]
    review_ids = [item["id"] for item in reviews]
    if sorted(edit_ids) != sorted(review_ids) or len(review_ids) != len(set(review_ids)):
        raise RuntimeError("Nemotron did not review every edit exactly once")
    if any(item["verdict"] not in {"APPROVE", "DISAPPROVE"} for item in reviews):
        raise RuntimeError("Nemotron returned an invalid verdict")
    write_json(doc_dir / "nemotron_review.json", review_data)
    return reviews


def artifact_dir(source, output_root):
    return output_root / source.relative_to(ROOT).with_suffix("")


def run(source, output_root):
    doc_dir = artifact_dir(source, output_root)
    doc_dir.mkdir(parents=True, exist_ok=False)
    original = source.read_text()
    (doc_dir / "original.md").write_text(original)
    edits, rejected, candidate = propose(source, original, doc_dir)
    reviews = review(original, candidate, edits, doc_dir)
    summary = {
        "document": str(source.relative_to(ROOT)),
        "accepted_proposals": len(edits),
        "mechanically_rejected": len(rejected),
        "nemotron_approved": sum(item["verdict"] == "APPROVE" for item in reviews),
        "nemotron_disapproved": sum(item["verdict"] == "DISAPPROVE" for item in reviews),
    }
    write_json(doc_dir / "run_summary.json", summary)
    print(json.dumps(summary), flush=True)


def apply_final_decisions(source, output_root):
    doc_dir = artifact_dir(source, output_root)
    original = (doc_dir / "original.md").read_text()
    if source.read_text() != original:
        raise RuntimeError(f"source changed after the snapshot: {source}")
    edits = json.loads((doc_dir / "edits.json").read_text())["edits"]
    decisions = json.loads((doc_dir / "final_decisions.json").read_text())["decisions"]
    approved = select_approved_edits(edits, decisions)
    final = apply_edits(original, approved)
    (doc_dir / "final.md").write_text(final)
    (doc_dir / "final.diff").write_text(unified_diff(original, final, source.name))
    source.write_text(final)
    print(json.dumps({
        "document": str(source.relative_to(ROOT)),
        "applied": len(approved),
        "rejected": len(edits) - len(approved),
    }), flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("run", "apply"))
    parser.add_argument("source", type=Path)
    parser.add_argument("--output-root", type=Path, default=ROOT / "sim_build/doc-editing-batch")
    args = parser.parse_args()
    source = args.source.resolve()
    output_root = args.output_root.resolve()
    if args.command == "run":
        run(source, output_root)
    else:
        apply_final_decisions(source, output_root)


if __name__ == "__main__":
    main()
