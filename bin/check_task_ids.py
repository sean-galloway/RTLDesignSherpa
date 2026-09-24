#!/usr/bin/env python3
"""Task-tracker integrity check for vault/Tasks/.

Three failure modes this catches, all of which have actually happened:

1. **Duplicate IDs within an area.** PUMICE-010/011 each ONCE named two
   unrelated tasks (renumbered 2026-09-06 to PUMICE-019/020); PUMICE-008
   existed as both a dropped task and a live open one.
   A bare `[[PUMICE-011]]` link is then ambiguous and the rollup counts lie.
2. **A stale `Next ID:` line.** Each area INDEX.md declares the next free
   number. If it is missing or <= the highest ID in use, the next person
   writing a task will collide again -- which is exactly how the pumice
   collisions happened.
3. **Status/page mismatch.** A task filed into closed.md whose body still
   says `**Status:** open`. Found on two pumice entries: filed but never
   re-statused, so they read as live work inside the closed page.

Historical collisions are grandfathered via KNOWN_COLLISIONS so the check
can be enforcing from day one without forcing a risky renumber of closed
history (renumbering breaks existing wikilinks). Anything NEW fails.

Usage:
    bin/check_task_ids.py                 # check every area
    bin/check_task_ids.py --area pumice   # one area
    bin/check_task_ids.py --next pumice   # print the next free ID and exit
"""
from __future__ import annotations

import argparse
import collections
import pathlib
import re
import subprocess
import sys

# Separator after the ID may be an em/en dash, a hyphen, or a COLON. The
# colon form was missing, and because a heading that does not match is
# simply not registered, a whole area could contain zero recognised IDs
# and still report "check passed" -- which is how a duplicate NEXYS-002
# got committed under an enabled checker. A checker that silently sees
# nothing is worse than no checker.
HEADING = re.compile(r"^#{2,3}\s+([A-Z][A-Z0-9]*-[A-Z0-9]+(?:\.\d+)?)\s*[—\-–:]")
# Level is part of the contract, not cosmetics (Sean, 2026-09-14): a task entry
# is `## <ID>`, a subtask is `## <ID>.nn`, and prose sections inside a body are
# `###` or deeper. Hierarchy lives in the ID, never in the heading level.
#
# Enforced because mixing the two levels broke COUNTING, not looks. With 136
# entries at ## and 103 at ###, every rollup count was wrong and a scan that
# read one level missed nine open items in amba alone -- several of them real
# defects filed and then invisible.
ENTRY_LEVEL = re.compile(r"^(#{2,6})\s+([A-Z][A-Z0-9]*-[A-Z0-9]+(?:\.\d+)?)\s*[—\-–:]")
# CommonMark fence rules, not a naive toggle. A closing fence carries NO info
# string, so a ```systemverilog line INSIDE a block is content and does not
# close it, and a longer fence can nest a shorter one. The toggle version
# desynced on three real files and made the scanner skip whole regions of
# amba/closed.md and bridge/closed.md -- it was silently checking far less than
# it claimed, which is the exact failure this file warns about at the top.
FENCE = re.compile(r"^\s*(`{3,}|~{3,})\s*(\S*)")
# Tolerant on purpose: the line is written by humans, so accept bold either
# side of the colon and any trailing prose after the ID.
NEXT_ID = re.compile(r"Next ID\**\s*:\s*\**\s*([A-Z][A-Z0-9]*-(\d+))")
# [^\w\n]* not \s*: a Status line led by an emoji ("**Status:** <glyph> CLOSED")
# made this regex fail to match at all, so `status` came back empty and the
# terminal-page check below was skipped entirely -- silently, on 37 entries.
# Removing the emojis un-blinded it and it immediately found 23 real
# mismatches. Skip any leading non-word characters so a future glyph cannot
# disable the gate again. Note it still captures only the FIRST word.
# ...and a leading markdown checkbox, the second form found the same way:
# "**Status:** [x] Done" also failed the original \s*(\w+) match, so five
# more entries were silently unchecked. Skip an optional [x]/[ ] marker,
# then any non-word run, then capture. "[ ] Open" still reads "Open" and
# still warns, so this does not blind the rule it exists for.
STATUS = re.compile(r"^\*\*Status:\*\*\s*(?:\[\s*\w?\s*\]\s*)?[^\w\n]*(\w+)", re.M)

# Pre-existing duplicates, recorded 2026-08-28. Grandfathered so the check
# can enforce immediately; do NOT add to this list to silence a new clash --
# renumber the new task instead (the whole point of the Next ID line).
KNOWN_COLLISIONS = {
    ("amba", "AMBA-INTEG"),
    ("common", "COMMON-021"),
    ("docs-review", "DOCREV-001"),
}

# closed.md / dropped.md bodies should not claim to be live.
TERMINAL_PAGES = {"closed.md": ("closed", "complete", "done", "resolved", "fixed"),
                  "dropped.md": ("dropped", "superseded", "wontfix")}


def repo_root() -> pathlib.Path:
    out = subprocess.check_output(["git", "rev-parse", "--show-toplevel"])
    return pathlib.Path(out.decode().strip())


STATES = ("open", "active", "closed", "deferred", "dropped")
ITEM_ID = re.compile(r"^([A-Z][A-Z0-9]*-\d+(?:\.\d+)?)$")
H1 = re.compile(r"^#\s+([A-Z][A-Z0-9]*-[A-Z0-9]+(?:\.\d+)?)\s*[—\-–:]")
INDEX_ITEM = re.compile(r"^\s*-\s+\*\*([A-Z][A-Z0-9]*-\d+(?:\.\d+)?)\*\*", re.M)


def is_item_layout(area: pathlib.Path) -> bool:
    """A lane keeps one file per item under state DIRECTORIES."""
    return any((area / s).is_dir() for s in STATES)


def scan_items(area: pathlib.Path):
    """Per-item layout: <state>/<ID>.md. The ID is the FILENAME.

    Reported as `<state>.md` so the terminal-page rules below apply unchanged.
    The filename is authoritative and the H1 must agree with it: two names for
    one item is how a rename half-lands and the tracker starts lying.
    """
    ids = collections.defaultdict(list)
    blocks, errs = [], []
    for state in STATES:
        d = area / state
        if not d.is_dir():
            continue
        for f in sorted(d.glob("*.md")):
            fid = f.stem
            if not ITEM_ID.match(fid):
                errs.append(f"{area_label(area)}: {state}/{f.name} is not named "
                            f"<ID>.md (e.g. BUG-001.md)")
                continue
            ids[fid].append(f"{state}/{f.name}")
            text = f.read_text()
            head = next((ln for ln in text.split("\n") if ln.startswith("# ")), "")
            hm = H1.match(head)
            if not hm:
                errs.append(f"{area_label(area)}: {state}/{f.name} has no "
                            f"'# {fid}: <title>' heading")
            elif hm.group(1) != fid:
                errs.append(f"{area_label(area)}: {state}/{f.name} is titled "
                            f"{hm.group(1)} -- filename and heading must match")
            sm = STATUS.search(text)
            blocks.append((fid, f"{state}.md", sm.group(1).lower() if sm else None))
    return ids, blocks, errs


def scan_area(area: pathlib.Path):
    """-> (ids{id: [loc]}, blocks[(id, page, status)])"""
    if is_item_layout(area):
        return scan_items(area)
    ids = collections.defaultdict(list)
    blocks = []
    level_errs: list[str] = []
    for f in sorted(area.glob("*.md")):
        if f.name == "INDEX.md":
            continue
        lines = f.read_text().split("\n")
        infence, fence_marker = False, ""
        for i, line in enumerate(lines, 1):
            # Never read inside a fenced block: task pages quote code whose
            # comments start with '#', and those are not headings.
            fm = FENCE.match(line)
            if fm:
                if not infence:
                    infence, fence_marker = True, fm.group(1)
                elif fm.group(2) == "" and len(fm.group(1)) >= len(fence_marker):
                    infence = False
                continue
            if infence:
                continue
            lm = ENTRY_LEVEL.match(line)
            if lm and len(lm.group(1)) != 2:
                level_errs.append(
                    f"{area_label(area)}: {f.name}:{i} {lm.group(2)} is a task entry at "
                    f"'{lm.group(1)}' -- every task entry must be '##' "
                    f"(subtasks are '## {lm.group(2)}.01', not a deeper heading)")
            m = HEADING.match(line)
            if not m:
                continue
            ids[m.group(1)].append(f"{f.name}:{i}")
            body = "\n".join(lines[i:i + 6])
            sm = STATUS.search(body)
            blocks.append((m.group(1), f.name, sm.group(1).lower() if sm else None))
    return ids, blocks, level_errs


def highest(ids, prefix: str | None = None) -> int:
    """Highest number in use, counting only IDs with `prefix` when given.

    Prefix-scoped because an area may legitimately hold more than one
    namespace: STREAM's older entries are bare `TASK-` (amba's prefix, and the
    source of three live cross-area collisions) while new ones are `STREAM-`.
    Taking the max across ALL of them demanded `Next ID: STREAM-081` purely
    because a TASK-080 sits in the same directory -- which would invent 80
    phantom gaps in the STREAM sequence to dodge a collision the prefix
    already prevents. A number only collides with the same prefix.
    """
    nums = [int(m.group(2)) for i in ids
            for m in [re.fullmatch(r"([A-Z][A-Z0-9]*(?:-[A-Z0-9]+)*?)-(\d+)", i)]
            if m and (prefix is None or m.group(1) == prefix)]
    return max(nums) if nums else 0


def area_label(area: pathlib.Path) -> str:
    """Report an area by its path under vault/Tasks, not its bare name.

    Lanes made `.name` ambiguous: 18 directories are called `bug`, 18 `issue`
    and 18 `task`, so "bug: DUPLICATE ID BUG-004" named nothing. The label is
    display-only -- KNOWN_COLLISIONS stays keyed on the bare name so the six
    grandfathered historical collisions are not silently un-grandfathered.
    """
    try:
        return str(area.relative_to(repo_root() / "vault" / "Tasks"))
    except ValueError:
        return area.name


def check_area(area: pathlib.Path) -> tuple[list[str], list[str]]:
    """-> (errors, warnings). Errors block; warnings are reported only.

    Duplicate IDs and a stale Next ID are ERRORS: both are mechanical and
    both actively corrupt the tracker going forward. Status/page mismatch is
    a WARNING, because deciding whether a task filed in closed.md is 'really
    closed with a stale line' or 'still open and misfiled' needs a human who
    knows the work -- flipping the text automatically would launder open
    work into the closed pile, which is worse than the inconsistency.
    """
    errs: list[str] = []
    warns: list[str] = []
    ids, blocks, level_errs = scan_area(area)
    errs += level_errs

    # A directory with no numbered task headings is not a task AREA -- e.g.
    # vault/Tasks/projects/ holds handoff documents. Demanding an INDEX and a
    # Next ID line there is a false positive, and a checker that cries wolf
    # gets bypassed.
    if not ids:
        return errs, warns

    for tid, locs in sorted(ids.items()):
        if len(locs) > 1 and (area.name, tid) not in KNOWN_COLLISIONS:
            errs.append(f"{area_label(area)}: DUPLICATE ID {tid} at {', '.join(locs)} "
                        f"-- renumber the newer one (see the Next ID line)")

    index = area / "INDEX.md"
    if not index.exists():
        errs.append(f"{area_label(area)}: no INDEX.md")
    else:
        m = NEXT_ID.search(index.read_text())
        if not m:
            errs.append(f"{area_label(area)}: INDEX.md has no 'Next ID:' line "
                        f"(highest in use is {highest(ids)}); add one")
        else:
            # NEXT_ID group 1 is the WHOLE id ("MATH-005"), not the prefix.
            # Passing it as the prefix matched nothing, so `hi` came back 0 and
            # every Next ID compared as valid -- the check passed vacuously and
            # a deliberately broken MATH-005 against a live MATH-010 sailed
            # through. Caught by mutation, which is the only reason it was
            # caught at all.
            prefix = m.group(1).rsplit("-", 1)[0]
            hi = highest(ids, prefix)
            if int(m.group(2)) <= hi:
                errs.append(f"{area_label(area)}: Next ID is {m.group(1)} but "
                            f"{prefix}-{hi} is already in use -- bump it "
                            f"past {hi}")

    # A lane INDEX that does not list what is on disk is the drift this whole
    # directory exists to prevent -- and an index nobody reconciles is the copy
    # the next session trusts. Cheap to check, so check it.
    if is_item_layout(area) and index.exists():
        listed = set(INDEX_ITEM.findall(index.read_text()))
        present = set(ids)
        for missing in sorted(present - listed):
            errs.append(f"{area_label(area)}: {missing} exists on disk but "
                        f"INDEX.md does not list it")
        for ghost in sorted(listed - present):
            errs.append(f"{area_label(area)}: INDEX.md lists {ghost} but no "
                        f"such file exists")

    for tid, page, status in blocks:
        want = TERMINAL_PAGES.get(page)
        if want and status and not status.startswith(want):
            warns.append(f"{area_label(area)}: {tid} lives in {page} but its body says "
                         f"'**Status:** {status}' -- re-status it or move it")
    return errs, warns


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--area")
    ap.add_argument("--next", metavar="AREA",
                    help="print the next free ID for AREA and exit")
    args = ap.parse_args()

    tasks = repo_root() / "vault" / "Tasks"
    # An AREA is any directory holding task pages, at ANY depth -- not just the
    # top level. `vault/Tasks/projects/components/**` nests two and three deep,
    # and a top-level-only scan silently skipped six areas: it reported "13
    # areas" while 19 existed, so 14 mis-levelled headings and every ID in
    # those areas went unchecked (2026-09-14). A checker that quietly covers
    # less than it claims is the failure mode this file already warns about.
    PAGES = {"open.md", "active.md", "closed.md", "deferred.md", "dropped.md"}
    # TWO layouts, and missing either one makes the checker pass vacuously.
    # Legacy areas keep flat pages at the area root (frozen, closed out in
    # place). Lanes keep one file per item under state DIRECTORIES -- for those
    # no *.md is named open.md, so a PAGES-only scan finds nothing and reports
    # success over 54 unchecked lanes. That is the exact blindness this file
    # warns about at the top, so both are discovered explicitly.
    flat = {f.parent for f in tasks.rglob("*.md") if f.name in PAGES}
    laned = {d.parent for d in tasks.rglob("*")
             if d.is_dir() and d.name in STATES and (d.parent / "INDEX.md").exists()}
    areas = sorted(flat | laned)
    if args.area:
        areas = [a for a in areas
                 if a.name == args.area or str(a.relative_to(tasks)) == args.area]

    if args.next:
        a = tasks / args.next
        ids, _, _ = scan_area(a)
        prefix = next((i.rsplit("-", 1)[0] for i in ids if re.search(r"-\d+$", i)),
                      args.next.upper())
        print(f"{prefix}-{highest(ids) + 1:03d}")
        return 0

    errs, warns = [], []
    for a in areas:
        e, w = check_area(a)
        errs += e
        warns += w

    if warns:
        print(f"Task-tracker warnings ({len(warns)}) -- not blocking:")
        for w in warns:
            print(f"  ? {w}")
        print()

    if errs:
        print(f"Task-tracker check FAILED ({len(errs)} issue(s)):\n", file=sys.stderr)
        for e in errs:
            print(f"  - {e}", file=sys.stderr)
        print("\nSee vault/Tasks/INDEX.md for the ID convention.", file=sys.stderr)
        return 1
    print(f"Task-tracker check passed ({len(areas)} area(s))")
    return 0


if __name__ == "__main__":
    sys.exit(main())
