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


def _norm(s):
    """Normalized text for quote location. Critiques re-wrap the doc lines they
    quote and strip the markdown emphasis (`code`, *italic*), so a raw
    substring search misses; strip emphasis and collapse whitespace on BOTH
    sides before matching."""
    return " ".join(re.sub(r"[`*]", "", s).split())


def evidence_for(round_dir, unit, finding):
    """Doc + RTL excerpts the finding cites, from the bundle snapshot first."""
    snap = os.path.join(round_dir, "_bundle_snapshot", unit)
    chunks, budget = [], EVIDENCE_CAP
    for src in sorted(glob.glob(os.path.join(snap, "*.md")) +
                      glob.glob(os.path.join(snap, "*.sv"))):
        if budget <= 0:
            break
        nbody = _norm(open(src, encoding="utf-8", errors="replace").read())
        quote = ""
        m = re.search(r'Says:\s*"(.+?)"', finding.get("raw", ""), re.S)
        if m:
            quote = _norm(m.group(1))[:200].strip()
        if quote and quote[:60] in nbody:
            i = nbody.index(quote[:60])
            lo, hi = max(0, i - WINDOW), min(len(nbody), i + len(quote) + WINDOW)
            excerpt = nbody[lo:hi]
        else:
            excerpt = nbody[:budget]
        excerpt = excerpt[:budget]
        budget -= len(excerpt)
        chunks.append(f"--- {os.path.basename(src)} ({os.path.getsize(src)} bytes) ---\n{excerpt}")
    if not chunks:
        return "(no bundle snapshot found; evidence unavailable -- verdict must be UNCERTAIN)"
    return "\n\n".join(chunks)


def call_claude(key, model, brief, messages, max_tokens=2048, timeout=600, retries=3):
    """Anthropic native /v1/messages. Returns (text, stop_reason, usage)."""
    payload = {"model": model, "max_tokens": max_tokens,
               "system": brief,
               "messages": messages}
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


def finding_blocks(text, n):
    """Slice a critique into per-finding blocks (both layouts), so each
    finding's OWN Says: quote drives evidence location. Findings arrive from
    index_findings.parse in file order, one per severity marker; split at the
    same markers. Falls back to the whole file if the counts disagree."""
    marks = [m.start() for m in re.finditer(r"^(?:\*\*)?\[[A-Z]+\]", text, re.M)]
    if len(marks) != n:
        return [text] * n
    return [text[marks[k]:marks[k + 1] if k + 1 < n else len(text)]
            for k in range(n)]


def identifier_truth(round_dir, unit, finding):
    """Grep ground truth for the backticked identifiers a finding names.

    Wrong-identifier findings ("the doc says SYNC_STAGES but the FIFO calls it
    N_FLOP_CROSS") are settled by WHERE each identifier appears, and a verifier
    reading a 200k-char concatenated RTL.sv does not do that cross-check
    reliably (round_1 F2: REFUTED a real finding it could have grepped). Hand
    it the grep instead."""
    snap = os.path.join(round_dir, "_bundle_snapshot", unit)
    raw = finding.get("raw", "")
    idents = sorted({t for t in re.findall(r"`([A-Za-z_][A-Za-z0-9_]{2,})`", raw)
                     if "_" in t or t.isupper()} |
                    set(re.findall(r"\b([A-Z][A-Z0-9_]{3,})\b", raw)))
    if not idents:
        return ""
    out = []
    for ident in idents[:12]:
        hits = []
        for src in sorted(glob.glob(os.path.join(snap, "*"))):
            if not os.path.isfile(src):
                continue
            for n, line in enumerate(open(src, encoding="utf-8", errors="replace"), 1):
                if re.search(rf"\b{re.escape(ident)}\b", line):
                    hits.append(f"  {os.path.basename(src)}:{n}: {line.strip()[:120]}")
                    if len(hits) >= 8:
                        break
            if len(hits) >= 8:
                break
        out.append(f"`{ident}` appears in {len(hits)} place(s) shown:" if hits
                   else f"`{ident}`: NOT FOUND anywhere in the evidence")
        out += hits
    return "## Identifier ground truth (grep over the evidence)\n\n" + "\n".join(out)


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
        fs = [f for f in index_findings.parse(crit)
              if not a.only or any(f["unit"].startswith(p) for p in a.only)]
        text = open(crit).read()
        for f, blk in zip(fs, finding_blocks(text, len(fs))):
            f["raw"] = blk
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
                    f"## The finding as written\n\n{f['raw'].strip()[:4000]}\n\n"
                    f"Files cited: {', '.join(f['files']) or '(none)'}\n\n"
                    f"## Evidence\n\n{evidence}\n\n"
                    f"{identifier_truth(a.round_dir, f['unit'], f)}")
            try:
                msgs = [{"role": "user", "content": user}]
                txt, stop, usage = call_claude(key, model, brief, msgs)
                if parse_verdict(txt) == "UNPARSED":
                    # One format-compliance retry as a follow-up turn: the
                    # first answer is often substantively right but prose
                    # (opus rambling past the "exactly this" instruction).
                    print("      UNPARSED -- retrying with format reminder", flush=True)
                    msgs += [{"role": "assistant", "content": txt},
                             {"role": "user", "content":
                              "You did not follow the output format. Reply with "
                              "EXACTLY this and nothing else:\n"
                              "VERDICT: UPHELD | REFUTED | UNCERTAIN\n"
                              "REASON: <one to three sentences>\n"
                              "SETTLE: <only when UNCERTAIN>"}]
                    txt2, stop, usage = call_claude(key, model, brief, msgs)
                    if parse_verdict(txt2) != "UNPARSED":
                        txt = txt2
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
