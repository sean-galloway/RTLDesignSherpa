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
4. **A count table that lies.** A lane INDEX's per-state table said
   `closed: 15` while the file sat in open/; passed until 2026-09-28
   (tooling TASK-014). Now every row must equal the files on disk.

3. **Status/page mismatch, BOTH directions.** A task filed into closed.md
   whose body still says `**Status:** open` (found on two pumice entries:
   filed but never re-statused, so they read as live work inside the closed
   page) -- and the inverse, a CLOSED/DONE body sitting in open.md/active.md,
   which inflates every rollup count with work that is actually done (six of
   those in amba, 2026-09-14; found by hand because the checker only saw one
   direction -- site-audit TASK-002).

Historical collisions are grandfathered via KNOWN_COLLISIONS so the check
can be enforcing from day one without forcing a risky renumber of closed
history (renumbering breaks existing wikilinks). Anything NEW fails.

`--area` and `--next` name an area by bare name or by path under
vault/Tasks/. Both USED TO ACCEPT ANYTHING: a name matching no area reported
"check passed (0 area(s))" with rc=0, and --next INVENTED an ID from the
string it was handed -- `--next totally-made-up` printed
TOTALLY-MADE-UP-001, and `--next RLB/hpet` printed RLB/HPET-001, a prefix
containing a slash that ITEM_ID can never match. Both now fail loudly.
This bit the moment sub-areas arrived (2026-09-25): the discovery unit is the
LANE, so `RLB/hpet` is not itself an area and every RLB/hpet argument passed
while examining nothing. --area therefore also accepts a PREFIX and checks
every lane beneath it, which is how an area with both flat pages and lanes
(`--area RLB`) gets fully checked rather than reporting 1 area and skipping
its five lanes.

Usage:
    bin/check_task_ids.py                 # check every area
    bin/check_task_ids.py --area pumice   # one area (its pages AND its lanes)
    bin/check_task_ids.py --area RLB/hpet # a sub-area: every lane beneath it
    bin/check_task_ids.py --next pumice   # print the next free ID and exit
"""
from __future__ import annotations

import argparse
import atexit
import collections
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile
from typing import Optional

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
# ... and live pages should not claim to be terminal: the SAME drift running
# the other way, which the terminal-page rule above structurally cannot see.
# Found by hand, not by checker: six entries sat in amba's open.md with bodies
# reading CLOSED/DONE -- one behind a duplicate heading that made a single task
# count as both open and closed -- and every rollup silently double-counted
# them (site-audit TASK-002, 2026-09-14). A one-directional checker leaves the
# inverse to be looked for by hand forever, so both directions warn here.
# Statuses read by prefix on BOTH sides: "closed-in-all-but-name" warns here
# exactly as "closed" does, and the terminal-page rule already worked that way.
LIVE_PAGES = {"open.md", "active.md"}
TERMINAL_STATUS = ("closed", "complete", "done", "resolved", "fixed",
                   "dropped", "superseded", "wontfix")


def repo_root() -> pathlib.Path:
    out = subprocess.check_output(["git", "rev-parse", "--show-toplevel"])
    return pathlib.Path(out.decode().strip())


# The tracker root actually being checked. Normally the worktree's
# vault/Tasks; in hook context a materialised copy of the index being committed
# (see tracker_tree). Area labels are relative to THIS, not to the worktree, or
# they silently degrade to a bare lane name -- and 18 directories are called
# `task`, so "task: DUPLICATE ID TASK-001" names nothing.
TASKS_ROOT: Optional[pathlib.Path] = None


def tracker_tree(override: Optional[str] = None) -> tuple[pathlib.Path, Optional[str]]:
    """-> (vault/Tasks to check, tempdir to clean up or None).

    `override` (--tasks-root) points the checker at any tracker tree, which is
    how you ask "what did I actually COMMIT?" -- materialise a commit and check
    that, rather than the worktree you happen to be sitting on:

        git worktree add --detach /tmp/wt <sha>
        python3 bin/check_task_ids.py --tasks-root /tmp/wt/vault/Tasks

    That is the procedure that caught BUG-014, and it was a hand-rolled
    incantation until this flag existed.

    **A gate must validate the tree it approves.** `git commit -- <paths>` builds
    a temporary index of HEAD plus only the listed paths, and `GIT_INDEX_FILE`
    names it. Those paths' content comes from the worktree, but everything else
    comes from HEAD -- so the worktree and the commit can disagree, and globbing
    directories checks the wrong one.

    How that bites, measured rather than imagined (tooling BUG-014): move an item
    with `git mv` and name only the NEW path in the pathspec. The staged deletion
    is outside the pathspec, so the commit takes the addition and leaves it
    behind; the item is committed into two states at once. On disk the old copy
    is already gone, so a directory glob sees a consistent lane and prints PASS.
    Done for real in `0804d45d3`, which put TASK-021 in both open/ and closed/
    with a count table claiming 3 against 4. Run against that committed tree the
    checker FAILS with both issues -- it has teeth, it was pointed at the wrong
    tree.

    State IS the directory in this convention, so there is no field to reconcile
    against: a half-committed move produces an item that is genuinely open and
    closed at once.

    Materialising the subtree, rather than threading an index reader through
    every glob and read, is deliberate. There are four glob sites and three read
    sites; a reader missed at any one of them reintroduces exactly this bug in a
    form nobody would look for again. This way the existing logic is unchanged
    and cannot disagree with itself. (Same reasoning as tooling TASK-017, which
    fixed this for filelist_registry.)

    Outside a hook, the worktree is the right answer -- for an interactive run
    and for CI's clean checkout alike.
    """
    if override:
        p = pathlib.Path(override).resolve()
        if not p.is_dir():
            sys.exit(f"--tasks-root {override!r} is not a directory")
        return p, None
    root = repo_root()
    if not os.environ.get("GIT_INDEX_FILE"):
        return root / "vault" / "Tasks", None

    tmp = tempfile.mkdtemp(prefix="check_task_ids-")
    ls = subprocess.run(["git", "ls-files", "-z", "--", "vault/Tasks"],
                        cwd=root, capture_output=True)
    if ls.returncode == 0 and ls.stdout:
        subprocess.run(["git", "checkout-index", "-z", "--stdin",
                        f"--prefix={tmp}/"],
                       cwd=root, input=ls.stdout, capture_output=True)
    cand = pathlib.Path(tmp) / "vault" / "Tasks"
    if not cand.is_dir():
        # The index holds no tracker files at all. Fall back rather than report
        # 0 areas: a checker that silently covers nothing is the failure mode
        # this file warns about at the top.
        shutil.rmtree(tmp, ignore_errors=True)
        return root / "vault" / "Tasks", None
    return cand, tmp


STATES = ("open", "active", "closed", "deferred", "dropped")
ITEM_ID = re.compile(r"^([A-Z][A-Z0-9]*-\d+(?:\.\d+)?)$")
# <PREFIX>-000 is the reserved template every area keeps in open/ so the next
# filing can copy it. It is not work. Counting it made every "what is left"
# answer overstate by one per area -- a lane whose real backlog was EMPTY still
# reported "1 open", and a session reported it that way (2026-09-28). There are
# 86 of these, one per area, so the error was 86 phantom open items repo-wide.
TEMPLATE_ID = re.compile(r"^[A-Z][A-Z0-9]*-0+(?:\.\d+)?$")


def is_template(fid: str) -> bool:
    """A reserved <PREFIX>-000 placeholder, not a tracked item."""
    return bool(TEMPLATE_ID.match(fid))
H1 = re.compile(r"^#\s+([A-Z][A-Z0-9]*-[A-Z0-9]+(?:\.\d+)?)\s*[—\-–:]")
INDEX_ITEM = re.compile(r"^\s*-\s+\*\*([A-Z][A-Z0-9]*-\d+(?:\.\d+)?)\*\*", re.M)
# The per-state count table in a lane INDEX: `| [open/](open/) | 3 | ... |`.
COUNT_ROW = re.compile(r"^\|\s*\[(\w+)/\]\(\1/\)\s*\|\s*(\d+)\s*\|", re.M)


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
            # The template is still checked for a well-formed name/heading
            # below -- it just is not an ITEM, so it stays out of ids and
            # therefore out of the counts and the INDEX cross-check.
            if not is_template(fid):
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
    namespace: STREAM once held bare `TASK-` entries (amba's prefix, and the
    source of three cross-area collisions) alongside new `STREAM-` ones. Taking
    the max across ALL of them demanded `Next ID: STREAM-081` purely because a
    TASK-080 sat in the same directory -- inventing 80 phantom gaps in the
    STREAM sequence to dodge a collision the prefix already prevents. A number
    only collides with the same prefix.

    That STREAM example is now HISTORICAL: the stream migration renumbered it,
    and a census on 2026-09-25 found 0 of 113 lanes holding two prefixes. So
    both callers currently agree whatever they pass, and the `prefix` argument
    guards a case that is latent rather than live -- which is exactly why
    --next's caller could ignore it for so long without anyone noticing. The
    live-again trigger is an area renumbered mid-flight, which is how STREAM
    got into that state the first time.
    """
    nums = [int(m.group(2)) for i in ids
            for m in [re.fullmatch(r"([A-Z][A-Z0-9]*(?:-[A-Z0-9]+)*?)-(\d+)", i)]
            if m and (prefix is None or m.group(1) == prefix)]
    return max(nums) if nums else 0


# A brand-new lane holds no item to read a prefix from, and the old fallback
# upper-cased the whole --next argument, so an empty `RLB/hpet/task` would have
# produced "RLB/HPET/TASK-001". The lane name is the real source.
LANE_PREFIX = {"task": "TASK", "bug": "BUG", "issue": "ISSUE"}


def area_label(area: pathlib.Path) -> str:
    """Report an area by its path under vault/Tasks, not its bare name.

    Lanes made `.name` ambiguous: 18 directories are called `bug`, 18 `issue`
    and 18 `task`, so "bug: DUPLICATE ID BUG-004" named nothing. The label is
    display-only -- KNOWN_COLLISIONS stays keyed on the bare name so the six
    grandfathered historical collisions are not silently un-grandfathered.
    """
    try:
        return str(area.relative_to(TASKS_ROOT if TASKS_ROOT is not None
                                    else repo_root() / "vault" / "Tasks"))
    except (ValueError, TypeError):
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
            # NEXT_ID group 1 is the WHOLE id ("math TASK-002 (was MATH-005)"), not the prefix.
            # Passing it as the prefix matched nothing, so `hi` came back 0 and
            # every Next ID compared as valid -- the check passed vacuously and
            # a deliberately broken math TASK-002 (was MATH-005) against a live MATH-010 sailed
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
        listed = {i for i in INDEX_ITEM.findall(index.read_text())
                  if not is_template(i)}
        present = set(ids)
        for missing in sorted(present - listed):
            errs.append(f"{area_label(area)}: {missing} exists on disk but "
                        f"INDEX.md does not list it")
        for ghost in sorted(listed - present):
            errs.append(f"{area_label(area)}: INDEX.md lists {ghost} but no "
                        f"such file exists")

    # The count TABLE is the third thing a filing must keep true, and until
    # 2026-09-28 nothing checked it: an INDEX said `closed: 15` while the file
    # still sat in open/, and this checker passed (RLB session; tooling
    # TASK-014). The item list above catches a MISSING line, not a wrong
    # number, and the number is what every rollup and every "what is left"
    # answer reads. Count the ITEMS on disk. Templates are excluded: they are
    # files in the directory, and the tables always used to count them, but
    # "the tables have always done it" is inertia, not a reason -- and the
    # number is read as "what is left", which a reserved placeholder is not.
    if is_item_layout(area) and index.exists():
        rows = {st: int(n) for st, n in COUNT_ROW.findall(index.read_text())}
        for st in STATES:
            d = area / st
            on_disk = len([f for f in d.glob("*.md")
                           if ITEM_ID.match(f.stem) and not is_template(f.stem)]) \
                      if d.is_dir() else 0
            if st not in rows:
                if on_disk:
                    errs.append(f"{area_label(area)}: INDEX.md has no count row for "
                                f"{st}/ but {on_disk} item(s) are there")
                continue
            if rows[st] != on_disk:
                errs.append(f"{area_label(area)}: INDEX.md says {st}: {rows[st]} "
                            f"but {st}/ holds {on_disk} -- fix the count table")
        for st in rows:
            if st not in STATES:
                errs.append(f"{area_label(area)}: INDEX.md counts an unknown state "
                            f"'{st}/'")

    for tid, page, status in blocks:
        want = TERMINAL_PAGES.get(page)
        if want and status and not status.startswith(want):
            warns.append(f"{area_label(area)}: {tid} lives in {page} but its body says "
                         f"'**Status:** {status}' -- re-status it or move it")
        elif page in LIVE_PAGES and status and status.startswith(TERMINAL_STATUS):
            warns.append(f"{area_label(area)}: {tid} lives in {page} but its body says "
                         f"'**Status:** {status}' -- closed work in a live page "
                         f"inflates every rollup count; re-status it or move it")
    return errs, warns


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--area")
    ap.add_argument("--next", metavar="AREA",
                    help="print the next free ID for AREA and exit")
    ap.add_argument("--tasks-root", metavar="DIR", default=None,
                    help="check this vault/Tasks tree instead of the worktree's "
                         "(e.g. a detached worktree at some commit, to ask what "
                         "that commit actually contains)")
    args = ap.parse_args()

    global TASKS_ROOT
    tasks, tmpdir = tracker_tree(args.tasks_root)
    TASKS_ROOT = tasks
    if tmpdir:
        # atexit rather than try/finally: main() has several early returns
        # (--next, --area with no match, the error paths) and a leak on any one
        # of them would litter /tmp on every commit.
        atexit.register(shutil.rmtree, tmpdir, ignore_errors=True)
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
    all_areas = list(areas)
    known = {str(a.relative_to(tasks)): a for a in all_areas}

    def resolve(want: str) -> list[pathlib.Path]:
        """Areas named by `want`: exact rel path, bare name, or PREFIX.

        The prefix arm is what makes a sub-area or grouping path addressable.
        Without it `--area RLB/hpet` selected nothing and reported success.
        """
        want = want.strip("/")
        return [a for a in all_areas
                if str(a.relative_to(tasks)) == want
                or a.name == want
                or str(a.relative_to(tasks)).startswith(want + "/")]

    def no_match(flag: str, want: str) -> int:
        print(f"{flag} {want!r} matched no area under vault/Tasks/.",
              file=sys.stderr)
        near = [r for r in sorted(known)
                if want.strip("/").lower() in r.lower()]
        if near:
            print("  did you mean:", file=sys.stderr)
            for r in near:
                print(f"    {r}", file=sys.stderr)
        else:
            print("  bin/check_task_ids.py (no args) lists every area it checks.",
                  file=sys.stderr)
        return 2

    if args.area:
        sel = resolve(args.area)
        if not sel:
            return no_match("--area", args.area)
        areas = sel

    if args.next:
        want = args.next.strip("/")
        a = known.get(want)
        if a is None:
            # A path that exists but is not itself an area -- a grouping dir or
            # a sub-area root -- must name its lanes, not invent an ID.
            under = [r for r in sorted(known) if r.startswith(want + "/")]
            if under:
                print(f"--next {args.next!r} is not a lane; IDs are per-lane. "
                      f"Pick one:", file=sys.stderr)
                for r in under:
                    print(f"    bin/check_task_ids.py --next {r}", file=sys.stderr)
                return 2
            return no_match("--next", args.next)
        ids, _, _ = scan_area(a)
        prefix = next((i.rsplit("-", 1)[0] for i in ids if re.search(r"-\d+$", i)),
                      LANE_PREFIX.get(a.name))
        if not prefix or "/" in prefix:
            print(f"--next {args.next!r}: cannot determine an ID prefix "
                  f"(no existing item and {a.name!r} is not a known lane).",
                  file=sys.stderr)
            return 2
        # The prefix above is the first item in scan order, which in a lane with
        # more than one namespace is arbitrary -- not a choice anybody made. Say
        # so rather than answer confidently for a namespace the caller may not
        # have meant. Scoping the number (below) fixes the arithmetic; it cannot
        # fix which sequence you wanted.
        seen = sorted({mm.group(1) for i in ids
                       for mm in [re.fullmatch(r"([A-Z][A-Z0-9]*(?:-[A-Z0-9]+)*?)-(\d+)", i)]
                       if mm})
        if len(seen) > 1:
            print(f"--next {args.next!r}: this lane holds {len(seen)} ID "
                  f"namespaces ({', '.join(seen)}) -- answering for {prefix}. "
                  f"Numbers collide only within a prefix, so if you meant "
                  f"another one, copy the template and name the file yourself.",
                  file=sys.stderr)
        # PREFIX-SCOPED, matching check_area above. Unscoped, a lane holding
        # two namespaces answered from the wrong one: TASK-080 beside STREAM-005
        # produced "STREAM-081", inventing 75 phantom gaps in the STREAM
        # sequence to dodge a collision that cannot happen -- a number only
        # collides within its own prefix. check_area has always scoped its
        # Next ID check this way, so the two sides disagreed.
        print(f"{prefix}-{highest(ids, prefix) + 1:03d}")
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
