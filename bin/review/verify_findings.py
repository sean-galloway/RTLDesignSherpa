#!/usr/bin/env python3
"""Adjudicate review findings with a SECOND model (default: Claude).

The qc reviewer (Kimi) produces false positives. Historically they were
filtered by hand at triage time -- the most expensive place to do it. This
sends each finding, with the doc/RTL evidence it cites, to a different model
family under a refute-by-default brief (VERIFIER_BRIEF.md) and records a
verdict per finding: UPHELD / REFUTED / UNCERTAIN.

What this does NOT do: settle arithmetic. A finding resting on an external
constant (CRC check value, JEDEC timing) is tagged NEEDS-RECOMPUTE -- models
quote sibling variants from memory (the CRC-64/WE case), a twenty-line
reference implementation settles it instead. See kimi-review-rounds rule 5.

Inputs:  a round directory (<results>/<mode>-<model>/round_N) holding
         <unit>.md critiques + _bundle_snapshot/<unit>/ (what the reviewer
         actually read -- preferred evidence source over the live tree).
Output:  <round>/verdicts-<verifier-model>.md -- one block per finding.
         Re-running skips findings already adjudicated (never overwrite,
         same rule as the rounds themselves).

Key: ANTHROPIC_API_KEY, else parsed at runtime from an operator key file
(default ~/api-keys.txt, override with VERIFIER_KEY_FILE). The key is never
printed, never committed, and the file path stays out of logs.

Usage:
  verify_findings.py --round <results>/qc-kimi-k3/round_3 [--only cdc] [--limit 5]
  verify_findings.py --round ... --dry-run
"""
import argparse
import glob
import hashlib
import json
import os
import re
import sys
import time
import urllib.error
import urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import index_findings  # noqa: E402

BRIEF_PATH = os.path.join(HERE, "VERIFIER_BRIEF.md")
EVIDENCE_CAP = 24_000        # chars of source evidence per finding
WINDOW = 1_500               # context lines window around a located quote


def load_key():
    """ANTHROPIC_API_KEY, else a sk-ant-* token from the operator key file."""
    k = os.environ.get("ANTHROPIC_API_KEY", "").strip()
    if k:
        return k
    path = os.path.expanduser(os.environ.get("VERIFIER_KEY_FILE", "~/api-keys.txt"))
    if not os.path.exists(path):
        sys.exit(f"no ANTHROPIC_API_KEY and no key file at {path}")
    for line in open(path):
        m = re.search(r"sk-ant-\S+", line)
        if m:
            return m.group(0).rstrip(",\"'")
    sys.exit(f"no sk-ant-* key found in {path}")


def finding_id(unit, title):
    return hashlib.sha1(f"{unit}::{title}".encode()).hexdigest()[:12]


def needs_recompute(text):
    """Findings resting on an external constant a model cannot settle."""
    pats = (r"CRC", r"check value", r"polynomial", r"JEDEC", r"0x[0-9a-fA-F]{6,}",
            r"ECMA", r"ISO\s?\d+", r"tRCD|tRFC|tRAS|tRP\b", r"AxLEN")
    return any(re.search(p, text) for p in pats)


def evidence_for(round_dir, unit, finding):
    """Doc + RTL excerpts the finding cites, from the bundle snapshot first."""
    snap = os.path.join(round_dir, "_bundle_snapshot", unit)
    chunks, budget = [], EVIDENCE_CAP
    for src in sorted(glob.glob(os.path.join(snap, "*.md")) +
                      glob.glob(os.path.join(snap, "*.sv"))):
        if budget <= 0:
            break
        body = open(src, encoding="utf-8", errors="replace").read()
        quote = ""
        m = re.search(r'Says:\s*"(.+?)"', finding.get("raw", ""), re.S)
        if m:
            quote = m.group(1)[:200].strip()
        if quote and quote[:60] in body:
            i = body.index(quote[:60])
            lo, hi = max(0, i - WINDOW), min(len(body), i + len(quote) + WINDOW)
            excerpt = body[lo:hi]
        else:
            excerpt = body[:budget]
        excerpt = excerpt[:budget]
        budget -= len(excerpt)
        chunks.append(f"--- {os.path.basename(src)} ({os.path.getsize(src)} bytes) ---\n{excerpt}")
    if not chunks:
        return "(no bundle snapshot found; evidence unavailable -- verdict must be UNCERTAIN)"
    return "\n\n".join(chunks)


def call_claude(key, model, brief, user, max_tokens=2048, timeout=600, retries=3):
    """Anthropic native /v1/messages. Returns (text, stop_reason, usage)."""
    payload = {"model": model, "max_tokens": max_tokens,
               "system": brief,
               "messages": [{"role": "user", "content": user}]}
    last = None
    for attempt in range(retries):
        try:
            req = urllib.request.Request(
                "https://api.anthropic.com/v1/messages",
                data=json.dumps(payload).encode(),
                headers={"content-type": "application/json",
                         "x-api-key": key,
                         "anthropic-version": "2023-06-01"})
            with urllib.request.urlopen(req, timeout=timeout) as r:
                d = json.load(r)
            text = "".join(b.get("text", "") for b in d.get("content", []))
            return text, d.get("stop_reason"), d.get("usage", {})
        except urllib.error.HTTPError as e:
            body = e.read()[:400].decode("utf-8", "replace")
            last = f"HTTP {e.code}: {body}"
            if 400 <= e.code < 500 and e.code not in (429,):
                raise RuntimeError(last) from None
        except Exception as e:  # noqa: BLE001
            last = f"{type(e).__name__}: {str(e)[:300]}"
        if attempt < retries - 1:
            backoff = 10 * (attempt + 1)
            print(f"      transport retry {attempt + 1}/{retries - 1} in {backoff}s ({last})",
                  flush=True)
            time.sleep(backoff)
    raise RuntimeError(last or "unknown transport failure")


def parse_verdict(text):
    m = re.search(r"VERDICT:\s*(UPHELD|REFUTED|UNCERTAIN)", text)
    return m.group(1) if m else "UNPARSED"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--round", required=True, dest="round_dir",
                    help="round dir: <results>/<mode>-<model>/round_N")
    ap.add_argument("--only", nargs="*", default=[], help="unit-name allowlist")
    ap.add_argument("--limit", type=int, help="adjudicate at most N findings")
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args()

    if not os.path.isdir(a.round_dir):
        sys.exit(f"not a round directory: {a.round_dir}")
    brief = open(BRIEF_PATH).read()
    model = os.environ.get("VERIFIER_MODEL", "claude-opus-5")
    out_path = os.path.join(a.round_dir, f"verdicts-{model}.md")

    # Resume: skip findings already adjudicated in the output file.
    done = set()
    if os.path.exists(out_path):
        done = set(re.findall(r"^### ([0-9a-f]{12}) ", open(out_path).read(), re.M))

    findings = []
    for crit in sorted(glob.glob(os.path.join(a.round_dir, "*.md"))):
        base = os.path.basename(crit)
        if base.startswith(("FINDINGS", "verdicts-")):
            continue
        for f in index_findings.parse(crit):
            if a.only and not any(f["unit"].startswith(p) for p in a.only):
                continue
            f["raw"] = open(crit).read()  # for quote extraction; trimmed later
            findings.append(f)

    pending = [f for f in findings if finding_id(f["unit"], f["title"]) not in done]
    if a.limit:
        pending = pending[:a.limit]

    print(f"round     {a.round_dir}")
    print(f"verifier  {model} @ api.anthropic.com")
    print(f"findings  {len(findings)} total, {len(done)} already adjudicated, "
          f"{len(pending)} to send")
    for f in pending:
        tag = " [NEEDS-RECOMPUTE]" if needs_recompute(f["title"]) else ""
        print(f"   send   {f['unit']}: {f['title'][:70]}{tag}")
    if a.dry_run:
        print("\ndry run -- nothing sent")
        return 0
    if not pending:
        print("\nnothing to do")
        return 0

    key = load_key()
    counts = {"UPHELD": 0, "REFUTED": 0, "UNCERTAIN": 0, "UNPARSED": 0}
    with open(out_path, "a") as out:
        if not done:
            out.write(f"# Verdicts -- {model} adjudicating {os.path.basename(a.round_dir)}\n\n")
        for i, f in enumerate(pending, 1):
            fid = finding_id(f["unit"], f["title"])
            print(f"\n[{i}/{len(pending)}] {f['unit']}: {f['title'][:70]}", flush=True)
            evidence = evidence_for(a.round_dir, f["unit"], f)
            user = (f"# Finding under adjudication (unit: {f['unit']}, "
                    f"severity: {f['severity']})\n\n{f['title']}\n\n"
                    f"Files cited: {', '.join(f['files']) or '(none)'}\n\n"
                    f"## Evidence\n\n{evidence}")
            try:
                txt, stop, usage = call_claude(key, model, brief, user)
            except Exception as e:  # noqa: BLE001
                print(f"      FAIL {type(e).__name__}: {str(e)[:200]}", flush=True)
                continue
            verdict = parse_verdict(txt)
            counts[verdict] = counts.get(verdict, 0) + 1
            recompute = "\nNOTE: NEEDS-RECOMPUTE -- settle the constant arithmetically, not by model." \
                if needs_recompute(f["title"]) else ""
            out.write(f"### {fid} [{verdict}] {f['title']}\n"
                      f"- Unit: {f['unit']}  Severity: {f['severity']}{recompute}\n"
                      f"```\n{txt.strip()}\n```\n\n")
            out.flush()
            print(f"      {verdict} (stop={stop})", flush=True)

    print(f"\nverdicts: {counts} -> {out_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
