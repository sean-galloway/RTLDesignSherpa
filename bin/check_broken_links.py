#!/usr/bin/env python3
"""A markdown link must point at something that exists.

495 broken links accumulated across 160 files before anyone counted (DOCREV-011,
2026-07-26). They did not arrive in a batch: they accumulated one move at a time,
because nothing ever looked. That task's own closing note is the reason this
file exists -- "wire the checker into a gate afterwards, or this returns."

Four categories are deliberately NOT counted, because "fixing" them corrupts
the page:

1. Links inside a ``` fence. These are templates and examples, written relative
   to the page being GENERATED, not to the file they appear in. An automated
   pass "fixed" them once and had to be reverted.
2. Links inside an inline `code` span. Documentation that TEACHES markdown
   contains "[Title](filename.md)" as an example. DOCREV-011's own regenerate
   snippet lacks this exclusion and therefore over-counts; 8 such false
   positives existed on 2026-09-21.
3. docs/review/ -- archived reviewer output. It QUOTES what a page said at the
   time; rewriting a quoted link falsifies the record.
4. Wikilinks. A dangling [[name]] in vault/ is a marker for a note worth
   writing, not a broken link (vault/Tasks/INDEX.md; DOCREV-011 notes 36 of
   them and says to leave them). This checker never looks at [[...]].

projects/ is NOT in that list. Those links are really broken, they are merely
DEFERRED by DOCREV-011 -- so they stay in the ratchet and must not grow.

Ratcheted, not hard-gated, for the reason CONV-002 records in the pre-commit
hook: a wall of red "diagnoses nothing and blocks everyone". A file may carry
its existing broken links; it may not GROW one.

Coverage is reported alongside the count. A checker that silently examines less
than it claims is the failure mode this repo has hit twice -- check_task_ids.py
was inert on 37 of 56 status lines while reporting zero warnings, and
filelist_registry.py --check printed PASS off an empty set. "0 broken" must not
be able to mean "parsed nothing".

The baseline MUST describe committed state. Generated from a working tree it
records a level the repo has never been at: on 2026-09-21 it was written from a
tree carrying another session's uncommitted doc fixes, recorded 117, and CI --
which only ever sees committed blobs -- measured 137 and failed every job. That
is why --update-baseline reads from HEAD rather than from disk.

Usage:
    bin/check_broken_links.py                  # report, exit 0 unless --ratchet
    bin/check_broken_links.py --list           # every broken link, with source
    bin/check_broken_links.py --ratchet        # fail only if a file GREW one
    bin/check_broken_links.py --update-baseline
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path

LINK = re.compile(r"\[[^\]]*\]\(([^)\s]+?)(?:#[^)\s]*)?\)")
FENCE = re.compile(r"^\s*```")
INLINE = re.compile(r"`[^`]*`")
SCHEMES = ("http://", "https://", "mailto:", "ftp://", "data:")

REPO = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"],
                                    text=True).strip())
BASELINE = REPO / "bin" / "broken_links_baseline.json"


def tracked_markdown() -> list[str]:
    out = subprocess.check_output(["git", "ls-files", "*.md"], text=True).split("\n")
    return [f for f in out if f and (REPO / f).is_file()]


def _head_tree() -> set[str]:
    out = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", "HEAD"],
                                  text=True).split("\n")
    paths = {p for p in out if p}
    # a link may target a directory; synthesise them from the file list
    for p in list(paths):
        parts = p.split("/")
        for i in range(1, len(parts)):
            paths.add("/".join(parts[:i]))
    return paths


def scan(from_head: bool = False
         ) -> tuple[dict[str, list[tuple[int, str]]], dict[str, int]]:
    """-> ({file: [(line, target)]}, coverage counters)

    from_head reads committed blobs instead of the working tree, so a baseline
    is reproducible on any clone regardless of what is uncommitted locally.
    """
    head_paths = _head_tree() if from_head else set()
    broken: dict[str, list[tuple[int, str]]] = {}
    cov = {"files": 0, "links": 0, "external": 0, "fenced": 0,
           "inline": 0, "review": 0, "resolved": 0, "broken": 0}
    for rel in tracked_markdown():
        cov["files"] += 1
        root = os.path.dirname(rel) or "."
        if from_head:
            r = subprocess.run(["git", "show", f"HEAD:{rel}"],
                               capture_output=True, text=True)
            if r.returncode != 0:
                continue
            text = r.stdout
        else:
            try:
                text = (REPO / rel).read_text(encoding="utf-8", errors="ignore")
            except OSError:
                continue
        # File-level exclusion, decided before any line-level test so a
        # review link cannot be miscounted as fenced or inline instead.
        is_review = rel.startswith("docs/review/")
        in_fence = False
        for lineno, line in enumerate(text.split("\n"), 1):
            if FENCE.match(line):
                in_fence = not in_fence
                continue
            # blank out inline code so a link inside one is not a link
            masked = INLINE.sub(lambda m: " " * len(m.group(0)), line)
            for m in LINK.finditer(line):
                cov["links"] += 1
                target = m.group(1)
                if is_review:
                    cov["review"] += 1
                    continue
                if target.startswith("#"):
                    continue          # in-page anchor, not a file reference
                if target.startswith(SCHEMES):
                    cov["external"] += 1
                    continue
                if in_fence:
                    cov["fenced"] += 1
                    continue
                if masked[m.start():m.end()].strip() == "":
                    cov["inline"] += 1
                    continue
                resolved = os.path.normpath(os.path.join(root, target))
                if (resolved in head_paths) if from_head else (REPO / resolved).exists():
                    cov["resolved"] += 1
                    continue
                cov["broken"] += 1
                broken.setdefault(rel, []).append((lineno, target))
    return broken, cov


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--list", action="store_true", help="print every broken link")
    ap.add_argument("--ratchet", action="store_true",
                    help="fail only if a file grew a broken link")
    ap.add_argument("--update-baseline", action="store_true")
    args = ap.parse_args()

    # The baseline describes COMMITTED state -- see the note at the top.
    broken, cov = scan(from_head=args.update_baseline)
    if args.update_baseline:
        print("[links] reading committed blobs (HEAD), not the working tree")
    counts = {f: len(v) for f, v in sorted(broken.items())}
    total = sum(counts.values())

    # Coverage first, always. A count is only meaningful beside what produced it.
    print(f"[links] {cov['files']} tracked .md, {cov['links']} links: "
          f"{cov['resolved']} resolve, {cov['broken']} broken, "
          f"{cov['external']} external, "
          f"{cov['fenced']} fenced, {cov['inline']} inline-code, "
          f"{cov['review']} docs/review")
    if cov["links"] == 0:
        print("[links] FAILED: matched no links at all -- the scan is broken, "
              "not the tree", file=sys.stderr)
        return 1

    if args.list:
        for f, hits in sorted(broken.items()):
            for lineno, target in hits:
                print(f"  {f}:{lineno} -> {target}")

    if args.update_baseline:
        BASELINE.write_text(json.dumps(counts, indent=2, sort_keys=True) + "\n")
        print(f"[links] baseline written: {total} broken in {len(counts)} file(s)")
        return 0

    if not args.ratchet:
        return 0

    if not BASELINE.is_file():
        BASELINE.write_text(json.dumps(counts, indent=2, sort_keys=True) + "\n")
        print(f"[links] no baseline; wrote one ({total} broken in "
              f"{len(counts)} file(s))")
        return 0

    base = json.loads(BASELINE.read_text())
    grew = [(f, base.get(f, 0), n) for f, n in counts.items() if n > base.get(f, 0)]
    if grew:
        print("", file=sys.stderr)
        print("[links] BLOCKED: file(s) grew a broken link:", file=sys.stderr)
        for f, was, now in grew:
            print(f"  {f}: {was} -> {now}", file=sys.stderr)
            for lineno, target in broken[f]:
                if not (REPO / os.path.normpath(
                        os.path.join(os.path.dirname(f) or '.', target))).exists():
                    print(f"      {lineno}: {target}", file=sys.stderr)
        print("", file=sys.stderr)
        print("  Fix the link, or if the target legitimately moved, repoint it.",
              file=sys.stderr)
        print("  Re-baseline only when the backlog genuinely shrank:", file=sys.stderr)
        print("      bin/check_broken_links.py --update-baseline", file=sys.stderr)
        return 1

    shrank = sum(max(0, base.get(f, 0) - counts.get(f, 0)) for f in base)
    msg = f"[links] PASS (ratchet): no file grew. {total} broken outstanding"
    if shrank:
        msg += f", {shrank} fewer than baseline"
    print(msg)
    return 0


if __name__ == "__main__":
    sys.exit(main())
