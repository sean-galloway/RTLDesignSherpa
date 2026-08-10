#!/usr/bin/env python3
"""Send a batch of review units to Kimi. Runs locally or in a cloud sandbox.

Two modes:

  qc         DOCS.md + RTL.sv -> REVIEWER_BRIEF.md
             Correctness critique with the RTL as ground truth.

  humanize   DOCS.md only     -> docs/kimi_humanization_style_guide.md
             Voice/prose pass. No RTL: the humanizer must not be tempted to
             re-litigate technical content, and a doc-only unit is small enough
             that a book rarely needs splitting.

The four process rules from KIMI_REVIEW_HOWTO.md are enforced here, because
each one was learned the expensive way:

  1. Rebuild everything, send a subset. Selection happens HERE (--only/--skip),
     never in the bundler. A stale bundle produces findings indistinguishable
     from real ones -- it cost a full review pass once.
  2. Serial dispatch. Interleaved failures are hard to attribute to a unit.
  3. Never overwrite. Rounds auto-increment and existing files are never
     rewritten, only filled in.
  4. Explicit large max_tokens with an escalation ladder (see kimi_client).

WHAT IS NEW FOR CLOUD: --resume. A serial round of 20+ units takes well over an
hour, and a cloud session can end before that. Resume re-enters an existing
round and dispatches only the units that have no result file yet. It never
touches a unit that already succeeded, so rule 3 still holds.

Usage:
  run_batch.py qc       --books DIR --results DIR [--only P ...] [--skip P ...]
  run_batch.py humanize --books DIR --results DIR [--only P ...] [--limit N]
  run_batch.py qc       --books DIR --results DIR --resume 4
  run_batch.py qc       --books DIR --results DIR --dry-run
"""
import argparse
import glob
import json
import os
import shutil
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kimi_client  # noqa: E402
import update_brief_table  # noqa: E402

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
HERE = os.path.dirname(os.path.abspath(__file__))

BRIEFS = {
    "qc": os.path.join(HERE, "REVIEWER_BRIEF.md"),
    "testqc": os.path.join(HERE, "TEST_REVIEWER_BRIEF.md"),
    "humanize": os.path.join(REPO, "docs", "kimi_humanization_style_guide.md"),
}


def discover(books, mode, only, skip):
    """A unit is a directory holding DOCS.md (plus RTL.sv when mode needs it).
    testqc units hold MANIFEST.md + TESTS.py instead (build_test_review_bundle)."""
    units = []
    marker = "MANIFEST.md" if mode == "testqc" else "DOCS.md"
    for mark in sorted(glob.glob(f"{books}/**/{marker}", recursive=True)):
        d = os.path.dirname(mark)
        if mode == "qc" and not os.path.exists(f"{d}/RTL.sv"):
            continue
        name = os.path.relpath(d, books).replace("/parts/", "_").replace("/", "_")
        if only and not any(name.startswith(p) for p in only):
            continue
        if skip and any(name.startswith(p) for p in skip):
            continue
        units.append((name, d))
    return units


def brief_table_is_current(books):
    """Does REVIEWER_BRIEF.md's book table match the bundle being sent?

    The table is ground truth handed to the reviewer and rots like any other
    doc: at the start of the common round it claimed 57 docs / 56 modules
    against a tree with 50 / 49, which primes findings about modules that were
    never missing. Nothing caught that but the findings it caused, so the
    check runs on the send path -- the same reasoning as the endpoint
    preflight below."""
    try:
        rows = update_brief_table.collect(books)
        if not rows:
            return True, "no book units found; table check skipped"
        brief = open(update_brief_table.BRIEF, encoding="utf-8").read()
        if update_brief_table.BEGIN not in brief or update_brief_table.END not in brief:
            return False, "REVIEWER_BRIEF.md has no BOOK TABLE markers"
        cur = brief[brief.index(update_brief_table.BEGIN):
                    brief.index(update_brief_table.END) + len(update_brief_table.END)]
        if cur.strip() == update_brief_table.render(rows).strip():
            return True, f"book table current ({len(rows)} books)"
        return False, ("book table is STALE against this bundle -- run "
                       f"bin/review/update_brief_table.py {books}")
    except Exception as e:  # noqa: BLE001
        return True, f"table check skipped ({type(e).__name__}: {str(e)[:120]})"


def build_prompt(mode, unit, unit_dir):
    if mode == "testqc":
        parts = [f"# Test-audit unit: {unit}\n"]
        for fname, label in [("MANIFEST.md", "Manifest (test -> chains -> filelist)"),
                             ("TESTS.py", "Test files (audit target)"),
                             ("TB.py", "Shared TB classes (audit target)"),
                             ("FRAMEWORK.py", "Framework components (GOLDEN)"),
                             ("RTL_IFACES.sv", "RTL interface headers")]:
            p = f"{unit_dir}/{fname}"
            if os.path.exists(p):
                parts.append(f"\n## {label}\n\n```\n{open(p).read()}\n```\n")
        return "\n".join(parts)

    docs = open(f"{unit_dir}/DOCS.md").read()
    if mode == "humanize":
        return (f"# Rewrite unit: {unit}\n\n"
                "Rewrite the documentation below in the voice defined by your "
                "brief. Preserve every technical claim, number, signal name, "
                "code block and cross-reference EXACTLY as written -- you are "
                "changing prose and presentation, not content.\n\n"
                "Also UNIFY the formatting and structure across the pages: one "
                "consistent heading style and hierarchy, one table style for "
                "the same kind of table (parameter, port, latency), one "
                "section ordering for the same kind of page -- the book should "
                "read as one document, not as pages written years apart. "
                "EXEMPTION: worked examples and step-by-step walkthroughs "
                "(waveform analyses, reset scenarios, numeric traces) keep "
                "their own didactic structure; do not force those into the "
                "uniform mold. Never break pipeline structure while "
                "unifying: caption lines (`: ...`), HTML anchors/comments, "
                "and link targets survive byte-identical.\n\n"
                "TWO HARD RULES, both gated -- a pass that breaks either is "
                "rejected before it can be applied:\n"
                "1. Emit NO emoji anywhere: not in headings, not leading "
                "bullets, not in tables, not as status markers. This includes "
                "emoji present in the SOURCE -- they are not content to "
                "preserve. Your brief gives the replacement for each glyph "
                "class; note that a lone warning glyph in a list of positives "
                "carries meaning and becomes `Caveat: ...` rather than "
                "vanishing.\n"
                "2. Use the canonical `##` section list in your brief. Do not "
                "invent your own consistent-but-different set.\n\n"
                "Return the complete rewritten Markdown and nothing else.\n\n"
                f"{docs}\n")

    extra = ""
    nomod = f"{unit_dir}/DOCS_WITH_NO_MODULE.md"
    if os.path.exists(nomod):
        extra = ("\n## Documentation pages with no matching module\n\n"
                 + open(nomod).read() + "\n")
    rtl = open(f"{unit_dir}/RTL.sv").read()
    return (f"# Review unit: {unit}\n\n"
            f"## Documentation under review\n\n{docs}\n{extra}\n"
            f"## RTL (ground truth)\n\n```systemverilog\n{rtl}\n```\n")


def pick_round(base, resume):
    """Resume an existing round, or mint the next unused number."""
    os.makedirs(base, exist_ok=True)
    existing = sorted(int(p.rsplit("_", 1)[1]) for p in os.listdir(base)
                      if p.startswith("round_") and p.rsplit("_", 1)[1].isdigit())
    if resume is not None:
        out = os.path.join(base, f"round_{resume}")
        if not os.path.isdir(out):
            sys.exit(f"--resume {resume}: {out} does not exist")
        return out, resume
    nxt = (existing[-1] + 1) if existing else 1
    out = os.path.join(base, f"round_{nxt}")
    if os.path.exists(out):
        sys.exit(f"REFUSING to overwrite existing {out}")
    return out, nxt


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["qc", "testqc", "humanize"])
    ap.add_argument("--books", required=True, help="bundle root (dirs with DOCS.md)")
    ap.add_argument("--results", required=True, help="results root")
    ap.add_argument("--only", nargs="*", default=[], help="name-prefix allowlist")
    ap.add_argument("--skip", nargs="*", default=[], help="name-prefix denylist")
    ap.add_argument("--limit", type=int, help="dispatch at most N units this batch")
    ap.add_argument("--resume", type=int, metavar="N",
                    help="re-enter round_N and dispatch only its missing units")
    ap.add_argument("--dry-run", action="store_true",
                    help="list what would be sent, send nothing")
    ap.add_argument("--allow-stale-table", action="store_true",
                    help="send even when REVIEWER_BRIEF.md's book table "
                         "disagrees with the bundle (qc only)")
    a = ap.parse_args()

    brief_path = BRIEFS[a.mode]
    if not os.path.exists(brief_path):
        sys.exit(f"brief not found: {brief_path}")
    brief = open(brief_path).read()

    units = discover(a.books, a.mode, a.only, a.skip)
    if not units:
        sys.exit("no units matched")

    tag = f"{a.mode}-{os.environ.get('KIMI_MODEL', 'kimi-k2')}"
    base = os.path.join(a.results, tag)
    out, rnd = pick_round(base, a.resume)

    # Resume: keep whatever already landed, dispatch only the gaps.
    pending, done = [], []
    for name, d in units:
        (done if os.path.exists(os.path.join(out, f"{name}.md")) else pending).append((name, d))
    if a.limit:
        pending = pending[:a.limit]

    table_ok, table_msg = (True, "")
    if a.mode == "qc":
        table_ok, table_msg = brief_table_is_current(a.books)

    print(f"mode      {a.mode}")
    print(f"endpoint  {kimi_client.describe()}")
    print(f"brief     {os.path.relpath(brief_path, REPO)}")
    if table_msg:
        print(f"table     {table_msg}")
    print(f"round     {out}" + (f"  (resumed, {len(done)} already present)" if done else ""))
    print(f"units     {len(pending)} to send, {len(done)} skipped as complete")
    for name, _ in pending:
        print(f"   send   {name}")
    for name, _ in done:
        print(f"   have   {name}")

    if a.dry_run:
        print("\ndry run -- nothing sent")
        return 0

    if not table_ok and not a.allow_stale_table:
        sys.exit("refusing to send a qc round with a stale book table "
                 "(--allow-stale-table overrides)")

    problems = kimi_client.preflight()
    if problems:
        for p in problems:
            print(f"CONFIG  {p}", file=sys.stderr)
        return sys.exit("refusing to start with a broken endpoint config")

    if not pending:
        print("\nnothing to do -- round is complete")
        return 0

    os.makedirs(out, exist_ok=True)
    # Snapshot the exact inputs so any critique can be traced to what it read.
    snap = os.path.join(out, "_bundle_snapshot")
    for name, d in pending:
        dst = os.path.join(snap, name)
        if not os.path.exists(dst):
            shutil.copytree(d, dst)

    ok = bad = 0
    t_round = time.time()
    for i, (name, d) in enumerate(pending, 1):
        print(f"\n[{i}/{len(pending)}] {name}", flush=True)
        user = build_prompt(a.mode, name, d)
        print(f"      prompt {len(user):,} chars", flush=True)
        try:
            txt, meta = kimi_client.call_with_ladder(
                brief, user, log=lambda m: print(m, flush=True))
        except Exception as e:  # noqa: BLE001
            print(f"      FAIL {type(e).__name__}: {str(e)[:300]}", flush=True)
            bad += 1
            continue
        meta.update({"unit": name, "mode": a.mode,
                     "model": os.environ.get("KIMI_MODEL", "kimi-k2"),
                     "brief": os.path.relpath(brief_path, REPO)})
        open(os.path.join(out, f"{name}.md"), "w").write(txt)
        open(os.path.join(out, f"{name}.meta.json"), "w").write(json.dumps(meta, indent=2))
        ok += 1
        print(f"      OK {meta['elapsed_s']}s finish={meta['finish_reason']} "
              f"out={meta['usage'].get('completion_tokens', '?')} "
              f"chars={meta['content_chars']:,}", flush=True)

    mins = (time.time() - t_round) / 60
    print(f"\nround_{rnd}: {ok} ok, {bad} failed, {mins:.1f} min -> {out}")
    if bad:
        print(f"re-run the gaps with:  --resume {rnd}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
