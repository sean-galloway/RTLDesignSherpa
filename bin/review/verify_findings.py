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


def locator_quotes(raw):
    """Every quoted span a finding cites, best locator first.

    A finding's witness is not always one quote sitting immediately after
    `Says:`. Reviewers label the source first (`Says: quickstart.md: "..."`),
    quote several passages that must be read together (a claim in one file and
    the sibling page that contradicts it), and put the decisive RTL line under
    `Actually:` rather than `Says:`.

    An anchored `Says:\\s*"(.+?)"` finds none of those. When it fails the caller
    silently falls back to the head of each file, so the verifier adjudicates a
    book title instead of the cited text -- and refutes real findings for
    "unverified wording". Whole common round_1 (18/18 findings) was adjudicated
    that way before this was caught; see kimi-review-rounds rule 10.

    So: take the quoted spans from the whole finding block, Says: first, and let
    the caller try each. Longest first within a field -- a short quote like
    "registered" matches everywhere and anchors nothing.
    """
    fields, out = [], []
    for name in ("Says", "Actually", "Impact"):
        m = re.search(rf"{name}:\s*(.*?)(?=\n\s*(?:File|Says|Actually|Impact):|\Z)",
                      raw, re.S)
        if m:
            fields.append(m.group(1))
    for field in fields or [raw]:
        spans = [_norm(q).strip() for q in re.findall(r'"([^"]{12,400})"', field)]
        out += sorted({q for q in spans if len(q) >= 20}, key=len, reverse=True)
    seen, uniq = set(), []
    for q in out:
        if q not in seen:
            seen.add(q)
            uniq.append(q)
    return uniq


def evidence_for(round_dir, unit, finding):
    """Doc + RTL excerpts the finding cites, from the bundle snapshot first.

    Returns (text, stats). `stats` is what MEASURES the extractor: how many of
    the finding's quoted spans were actually located. Everything this pass
    claims rests on the verifier seeing the quoted text, so a silent locator
    failure does not degrade the pass, it INVERTS it -- a head-of-file excerpt
    reads as "the document does not say this". Callers report the located
    share; a low one invalidates the verdicts file rather than merely
    weakening it. See kimi-review-rounds rule 10."""
    snap = os.path.join(round_dir, "_bundle_snapshot", unit)
    quotes = locator_quotes(finding.get("raw", ""))
    hit = set()
    chunks, budget = [], EVIDENCE_CAP
    files = sorted(glob.glob(os.path.join(snap, "*.md")) +
                   glob.glob(os.path.join(snap, "*.sv")) +
                   glob.glob(os.path.join(snap, "*.py")))

    def windows(body):
        """Merged context windows around every quote that locates in `body`."""
        spans = []
        for q in quotes:
            key = q[:60]
            start = 0
            while key:
                i = body.find(key, start)
                if i < 0:
                    break
                hit.add(q)
                spans.append((max(0, i - WINDOW), min(len(body), i + len(q) + WINDOW)))
                start = i + 1
                if len(spans) >= 6:
                    break
        if not spans:
            return []
        spans.sort()
        merged = [spans[0]]
        for lo, hi in spans[1:]:
            if lo <= merged[-1][1]:
                merged[-1] = (merged[-1][0], max(merged[-1][1], hi))
            else:
                merged.append((lo, hi))
        return merged

    loaded = []
    for src in files:
        body = _norm(open(src, encoding="utf-8", errors="replace").read())
        loaded.append((src, body, windows(body)))
    loaded.sort(key=lambda t: not t[2])  # files carrying a located quote first
    any_located = any(w for _, _, w in loaded)
    for src, nbody, wins in loaded:
        if budget <= 0:
            break
        if wins:
            excerpt = "\n  [...]\n".join(nbody[lo:hi] for lo, hi in wins)
        else:
            excerpt = nbody[:min(budget, 1_500)]
        excerpt = excerpt[:budget]
        budget -= len(excerpt)
        tag = "" if wins else "  [HEAD OF FILE ONLY -- no cited quote located here]"
        chunks.append(f"--- {os.path.basename(src)} "
                      f"({os.path.getsize(src)} bytes){tag} ---\n{excerpt}")
    stats = {"quotes": len(quotes), "located": len(hit),
             "files": sum(1 for _, _, w in loaded if w)}
    if not chunks:
        return ("(no bundle snapshot found; evidence unavailable -- verdict must be UNCERTAIN)",
                stats)
    if not any_located:
        # Loud, not silent: the old code degraded to file heads with no signal,
        # and the verifier read that as "the doc does not say this".
        chunks.insert(0, "!! NONE of this finding's quoted text could be located in the "
                         "bundle snapshot. What follows is the HEAD of each file, NOT the "
                         "cited passage. Absence here is NOT evidence the claim is absent "
                         "from the document -- return UNCERTAIN unless you can settle the "
                         "finding some other way.")
    return "\n\n".join(chunks), stats


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


def test_skeleton(snap):
    """The structural parts of a test unit that contract findings turn on.

    Test files are tens of kB and the deciding code (the parameter generator,
    the run() call, the parametrize decorator, the TB contract methods) sits
    far from the header docstring a finding's Says: quote usually cites, so a
    quote-centered window misses it -- the second UNCERTAIN wave. Extract the
    known locations mechanically for any unit that has .py files."""
    out, budget = [], 8_000
    for src in sorted(glob.glob(os.path.join(snap, "*.py"))):
        if budget <= 0:
            break
        body = open(src, encoding="utf-8", errors="replace").read()
        hits = []
        for m in re.finditer(r"^(@pytest\.mark\.parametrize.*|def (generate\w*params\w*)\(.*|"
                             r"def (setup_clocks_and_reset|assert_reset|deassert_reset|reset_dut)\(.*|"
                             r"\s*run\(\s*$)", body, re.M):
            start = m.start()
            # take the decorator line alone; functions/call get a body slice
            span = 1_600 if not m.group(0).startswith("@") else 200
            hits.append(body[start:start + span])
        if hits:
            chunk = (f"--- {os.path.basename(src)}: params/parametrize/run/reset-methods ---\n"
                     + "\n#   [...]\n".join(hits))
            chunk = chunk[:budget]
            budget -= len(chunk)
            out.append(chunk)
    if not out:
        return ""
    return "## Test skeleton (generate_params / parametrize / run() / reset methods)\n\n" + "\n\n".join(out)


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

    # Measure the extractor BEFORE spending anything. Locating the quotes is
    # local file work; the verdicts are only worth what this share is, so it is
    # printed on every run and on --dry-run, which makes the dry run the
    # pre-flight rule 10 asks for.
    for f in pending:
        f["_ev"], f["_st"] = evidence_for(a.round_dir, f["unit"], f)
        st = f["_st"]
        tag = " [NEEDS-RECOMPUTE]" if needs_recompute(f["title"]) else ""
        loc = (f"{st['located']}/{st['quotes']} quotes in {st['files']} file(s)"
               if st["quotes"] else "NO QUOTES IN FINDING")
        flag = "" if st["located"] else "  <-- BLIND"
        print(f"   send   {f['unit']}: {f['title'][:60]}{tag}\n"
              f"          evidence: {loc}{flag}")

    blind = [f for f in pending if not f["_st"]["located"]]
    if pending:
        share = 100 * (len(pending) - len(blind)) / len(pending)
        print(f"\nextractor {len(pending) - len(blind)}/{len(pending)} findings "
              f"({share:.0f}%) resolved to a located quote")
        if blind:
            print("          BLIND findings get file heads, which read to the verifier "
                  "as\n          'the doc does not say this' -- their verdicts are not "
                  "evidence.")
        if share < 80:
            print("          LOW. Below ~80% the locator is the defect, not the "
                  "findings.\n          Fix locator_quotes()/evidence_for() and "
                  "re-adjudicate before\n          trusting this verdicts file "
                  "(kimi-review-rounds rule 10).")
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
            out.write(f"# Verdicts -- {model} adjudicating {os.path.basename(a.round_dir)}\n\n"
                      "**A REFUTED verdict is advisory and never drops a finding on its "
                      "own.** Measured on the reset corpus, this pass refutes real findings "
                      "at a rate comparable to the reviewer's own false-positive rate "
                      "(cdc round_2 reset_sync, cdc round_3 apb5 wrapper, common round_1 "
                      "shifter_barrel and shifter_universal). It earns its keep by ranking "
                      "human triage and by settling mechanical classes, not by deciding.\n\n"
                      "Each block records the evidence actually packed. A finding whose "
                      "quotes did not locate was adjudicated against file heads: its verdict "
                      "is not evidence either way.\n\n")
        for i, f in enumerate(pending, 1):
            fid = finding_id(f["unit"], f["title"])
            print(f"\n[{i}/{len(pending)}] {f['unit']}: {f['title'][:70]}", flush=True)
            evidence = f["_ev"]
            user = (f"# Finding under adjudication (unit: {f['unit']}, "
                    f"severity: {f['severity']})\n\n{f['title']}\n\n"
                    f"## The finding as written\n\n{f['raw'].strip()[:4000]}\n\n"
                    f"Files cited: {', '.join(f['files']) or '(none)'}\n\n"
                    f"## Evidence\n\n{evidence}\n\n"
                    f"{test_skeleton(os.path.join(a.round_dir, '_bundle_snapshot', f['unit']))}\n\n"
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
            st = f["_st"]
            ev = (f"{st['located']}/{st['quotes']} quotes located in {st['files']} file(s)"
                  if st["located"] else
                  "NO quote located -- adjudicated against file heads, verdict is not evidence")
            out.write(f"### {fid} [{verdict}] {f['title']}\n"
                      f"- Unit: {f['unit']}  Severity: {f['severity']}\n"
                      f"- Evidence: {ev}{recompute}\n"
                      f"```\n{txt.strip()}\n```\n\n")
            out.flush()
            print(f"      {verdict} (stop={stop})", flush=True)

    print(f"\nverdicts: {counts} -> {out_path}")
    if counts["REFUTED"]:
        print(f"          the {counts['REFUTED']} REFUTED are ADVISORY -- human-triage "
              "each one.\n          This pass has refuted real findings in four rounds.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
