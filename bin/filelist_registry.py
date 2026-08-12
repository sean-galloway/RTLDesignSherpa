#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: filelist_registry
# Purpose: Single entry point for discovering and auditing RTL filelists.
# Subsystem: tooling
"""Discover, resolve and audit every RTL filelist in the repository.

Reads bin/filelists.toml (the registry of filelist areas) and answers the
questions that previously required hand-rolling a parser:

    --list              where all the filelists live, per area
    --check             every module in a library area is reachable from some .f
    --find MODULE       which filelist(s) provide a module
    --audit             consumers that hand-list rtl/common or rtl/amba sources
    --blindspots        what the above CANNOT see: unregistered filelists,
                        tests building their own source array, .sby dead paths
    --resolve FILELIST  the fully expanded source list for one .f

Path/variable handling matches the cocotb consumer
(bin/TBClasses/shared/filelist_utils.get_sources_from_filelist): $REPO_ROOT and
the per-component $*_ROOT variables are substituted, `-f` includes are resolved
recursively with cycle protection, and a bare relative path is resolved against
the including filelist's directory, falling back to the repo root.

Exit status is 0 when the requested audit passes, 1 when it fails, so --check
and --audit are usable as CI gates.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path

try:
    import tomllib
except ModuleNotFoundError:  # Python < 3.11
    import tomli as tomllib  # type: ignore

REPO_ROOT = Path(__file__).resolve().parent.parent
REGISTRY = REPO_ROOT / "bin" / "filelists.toml"
BASELINE = REPO_ROOT / "bin" / "blindspots_baseline.json"

MODULE_RE = re.compile(r"^\s*module\s+([A-Za-z_]\w*)", re.M)

# A $VAR / ${VAR} that survived expansion. FRAMEWORK_ROOT and STREAM_CHAR_ROOT
# are exported by the per-flow Makefiles rather than by filelist_utils, and
# FRAMEWORK_ROOT's value depends on which flow is driving (stream vs ddr2), so
# they cannot be resolved statically. Lines using them are resolvable under
# `make` but not standalone; treat them as flow-scoped, not broken, or every
# board filelist reads as failing.
UNRESOLVED_VAR = re.compile(r"\$\{?[A-Z_][A-Z0-9_]*\}?")

# Root variables, mirroring env_python and filelist_utils. All three lists must
# agree: a variable used in a .f but missing from any one of them makes that
# filelist resolvable in some contexts and broken in others.
ROOT_VARS = {
    "REPO_ROOT": "",
    "APB_XBAR_ROOT": "projects/components/apbx_xbar",
    "BCH_ROOT": "projects/components/bch",
    "BRIDGE_ROOT": "projects/components/bridge",
    "CONVERTERS_ROOT": "projects/components/converters",
    "DELTA_ROOT": "projects/components/delta",
    "MISC_ROOT": "projects/components/misc",
    "RAPIDS_ROOT": "projects/components/dmas/rapids",
    "RETRO_ROOT": "projects/components/retro_legacy_blocks",
    "STREAM_ROOT": "projects/components/dmas/stream",
    "STREAM_CHAR_ROOT": "projects/NexysA7/stream_characterization/flows-stream-bridge",
    "STREAM_CHAR_FRAMEWORK_ROOT": "projects/NexysA7/stream_characterization/stream_char_framework",
    "DDR2_CHAR_FRAMEWORK_ROOT": "projects/NexysA7/ddr2-characterization/ddr2_char_framework",
    "TIMING_CHAR_ROOT": "projects/NexysA7/timing_characterization",
}


def _expand(token: str) -> str:
    # Filelists use both $VAR and ${VAR}; substitute the braced form first so
    # the bare form does not leave a dangling "{...}" behind.
    for var, rel in ROOT_VARS.items():
        target = str(REPO_ROOT / rel) if rel else str(REPO_ROOT)
        token = token.replace(f"${{{var}}}", target).replace(f"${var}", target)
    return token


def resolve(filelist: Path, _seen: set[Path] | None = None) -> tuple[list[Path], list[str]]:
    """Return (sources, problems) for a filelist, following -f includes."""
    seen = _seen if _seen is not None else set()
    sources: list[Path] = []
    problems: list[str] = []
    # Lines that only resolve under a flow Makefile. Collected so they are
    # visibly skipped rather than silently dropped or wrongly reported broken.
    flow_scoped: list[str] = []

    filelist = filelist.resolve()
    if filelist in seen:
        return sources, problems
    seen.add(filelist)

    if not filelist.is_file():
        return sources, [f"missing filelist: {rel(filelist)}"]

    here = filelist.parent
    for raw in filelist.read_text(errors="ignore").splitlines():
        line = raw.strip()
        if not line or line.startswith("#") or line.startswith("//"):
            continue
        line = _expand(line)
        if line.startswith("+"):  # +incdir+ and friends
            continue

        if line.startswith("-f"):
            target = line[2:].strip()
            if not target:
                problems.append(f"{rel(filelist)}: empty -f directive")
                continue
            path = Path(target)
            if not path.is_absolute():
                cand = (here / target).resolve()
                path = cand if cand.exists() else (REPO_ROOT / target).resolve()
            if not path.is_file():
                problems.append(f"{rel(filelist)}: -f target not found: {rel(path)}")
                continue
            sub_sources, sub_problems = resolve(path, seen)
            sources.extend(sub_sources)
            problems.extend(sub_problems)
            continue

        if line.startswith("-"):  # other tool switches
            continue

        if UNRESOLVED_VAR.search(line):
            # FRAMEWORK_ROOT / STREAM_CHAR_ROOT are exported by the per-flow
            # Makefiles, not by filelist_utils, and FRAMEWORK_ROOT's value
            # depends on which flow is driving. Such a line is resolvable under
            # `make` but not standalone -- report it as flow-scoped rather than
            # as a broken reference, or every board filelist looks broken.
            flow_scoped.append(f"{rel(filelist)}: flow-scoped variable: {line}")
            continue

        path = Path(line)
        if not path.is_absolute():
            cand = (here / line).resolve()
            path = cand if cand.exists() else (REPO_ROOT / line).resolve()
        if not path.is_file():
            problems.append(f"{rel(filelist)}: source not found: {rel(path)}")
            continue
        sources.append(path)

    # de-duplicate, preserving order
    return list(dict.fromkeys(sources)), problems


def rel(path: Path) -> str:
    try:
        return str(Path(path).resolve().relative_to(REPO_ROOT))
    except ValueError:
        return str(path)


def modules_in(path: Path) -> set[str]:
    try:
        return set(MODULE_RE.findall(path.read_text(errors="ignore")))
    except OSError:
        return set()


def load_registry() -> dict:
    if not REGISTRY.is_file():
        sys.exit(f"registry not found: {rel(REGISTRY)}")
    return tomllib.loads(REGISTRY.read_text())


def area_filelists(area: dict) -> list[Path]:
    out: list[Path] = []
    for d in area.get("filelist_dirs", []):
        out.extend(sorted((REPO_ROOT / d).rglob("*.f")))
    return out


# --------------------------------------------------------------------------- #
# Commands
# --------------------------------------------------------------------------- #

def cmd_list(reg: dict) -> int:
    print(f"{'AREA':<32} {'KIND':<11} {'LISTS':>5}  LOCATION")
    print("-" * 96)
    total = 0
    for area in reg.get("area", []):
        lists = area_filelists(area)
        total += len(lists)
        tag = area["kind"] + ("*" if area.get("generated") else "")
        first = area.get("filelist_dirs", ["-"])[0]
        print(f"{area['name']:<32} {tag:<11} {len(lists):>5}  {first}")
        for extra in area.get("filelist_dirs", [])[1:]:
            print(f"{'':<32} {'':<11} {'':>5}  {extra}")
    print("-" * 96)
    print(f"{'TOTAL':<32} {'':<11} {total:>5}")
    print("\n* = generated area: never hand-edit, re-run its regen command:")
    for area in reg.get("area", []):
        if area.get("generated"):
            print(f"    {area['name']:<30} {area.get('regen', '(no regen command recorded!)')}")
    return 0


def cmd_check(reg: dict) -> int:
    exempt = reg.get("exempt", {})
    failures = 0

    for area in reg.get("area", []):
        roots = area.get("rtl_roots", [])
        if not roots:
            continue

        covered: set[str] = set()
        problems: list[str] = []
        for fl in area_filelists(area):
            srcs, probs = resolve(fl)
            problems.extend(probs)
            for s in srcs:
                covered |= modules_in(s)

        declared: set[str] = set()
        for root in roots:
            for sv in (REPO_ROOT / root).rglob("*.sv"):
                if "/filelists/" in str(sv):
                    continue
                declared |= modules_in(sv)

        missing = sorted(m for m in declared - covered if m not in exempt)
        status = "OK  " if not missing and not problems else "FAIL"
        if missing or problems:
            failures += 1
        print(f"[{status}] {area['name']:<28} {len(declared):>4} modules, "
              f"{len(declared & covered):>4} covered, {len(missing):>3} uncovered, "
              f"{len(problems):>3} broken refs")
        for m in missing:
            print(f"         uncovered module: {m}")
        for p in dict.fromkeys(problems):
            print(f"         {p}")

    print()
    print("PASS" if not failures else f"FAIL ({failures} area(s) with gaps)")
    return 1 if failures else 0


def cmd_find(reg: dict, module: str) -> int:
    hits = []
    for area in reg.get("area", []):
        for fl in area_filelists(area):
            srcs, _ = resolve(fl)
            for s in srcs:
                if module in modules_in(s):
                    hits.append((area["name"], rel(fl), rel(s)))
                    break
    if not hits:
        print(f"no filelist provides module '{module}'")
        return 1
    for area_name, fl, src in hits:
        print(f"{area_name:<24} {fl}\n{'':<24}   -> {src}")
    return 0


def _owner_of(reg: dict, path: Path) -> str | None:
    """Which area owns this source file, by rtl_roots. None if unowned."""
    try:
        rp = str(Path(path).resolve().relative_to(REPO_ROOT))
    except ValueError:
        return None
    best, best_len = None, -1
    for area in reg.get("area", []):
        for root in area.get("rtl_roots", []):
            # longest matching root wins, so dmas/stream beats a broader prefix
            if (rp == root or rp.startswith(root.rstrip("/") + "/")) and len(root) > best_len:
                best, best_len = area["name"], len(root)
    return best


def cmd_audit(reg: dict) -> int:
    """Flag any filelist that directly lists a .sv owned by a DIFFERENT area.

    The rule is general: a component owns its own compile closure, so a consumer
    -f includes that component's filelist and never names its sources. An earlier
    version of this check hardcoded `rtl/(common|amba)` and therefore could not
    see cross-COMPONENT violations at all -- the bridge generator was hand-listing
    six converters sources and the audit reported zero. Ownership now comes from
    each area's rtl_roots in filelists.toml, so any new area is covered for free.
    """
    bad = 0
    for area in reg.get("area", []):
        owner_self = area["name"]
        for fl in area_filelists(area):
            offenders: list[tuple[str, str]] = []
            for raw in fl.read_text(errors="ignore").splitlines():
                line = raw.strip()
                if not line or line.startswith("#") or line.startswith("//"):
                    continue
                if line.startswith("-") or line.startswith("+"):
                    continue
                expanded = _expand(line)
                if not expanded.endswith(".sv"):
                    continue
                if UNRESOLVED_VAR.search(expanded):
                    continue  # flow-scoped; resolved only under a Makefile
                owner = _owner_of(reg, Path(expanded))
                if owner is not None and owner != owner_self:
                    offenders.append((line, owner))
            if offenders:
                bad += len(offenders)
                gen = "  [GENERATED - fix the generator, not this file]" if area.get("generated") else ""
                print(f"{rel(fl)}: {len(offenders)} source(s) owned by another area{gen}")
                for o, own in offenders[:4]:
                    print(f"    [{own}] {o}")
                if len(offenders) > 4:
                    print(f"    ... +{len(offenders) - 4} more")
    print()
    if bad:
        print(f"FAIL: {bad} cross-area hand-listed source(s); -f the owning area's filelist")
        return 1
    print("PASS: no filelist hand-lists another area's sources")
    return 0


def direct_sources(filelist: Path) -> tuple[set[Path], set[Path]]:
    """Return (sources listed directly in this file, filelists it -f includes).

    Deliberately NOT recursive: this is about what the file itself spells out,
    which is what distinguishes "unrolled" from "included".
    """
    srcs: set[Path] = set()
    incs: set[Path] = set()
    if not filelist.is_file():
        return srcs, incs
    here = filelist.parent
    for raw in filelist.read_text(errors="ignore").splitlines():
        line = raw.strip()
        if not line or line.startswith("#") or line.startswith("//") or line.startswith("+"):
            continue
        line = _expand(line)
        if UNRESOLVED_VAR.search(line):
            continue
        if line.startswith("-f"):
            t = line[2:].strip()
            p = Path(t) if Path(t).is_absolute() else (here / t)
            p = p if p.exists() else (REPO_ROOT / t)
            if p.is_file():
                incs.add(p.resolve())
            continue
        if line.startswith("-"):
            continue
        p = Path(line) if Path(line).is_absolute() else (here / line)
        p = p if p.exists() else (REPO_ROOT / line)
        if p.is_file():
            srcs.add(p.resolve())
    return srcs, incs


def cmd_unrolled(reg: dict, min_sources: int = 2) -> int:
    """Find filelists that INLINE another filelist's contents instead of -f'ing it.

    Ownership-based auditing (--audit) only catches a consumer naming a foreign
    *path*. It cannot see the subtler and more common failure: copying the body
    of another filelist verbatim. Those copies look self-contained and pass every
    build, then silently rot the moment the copied component gains a dependency
    -- which is exactly how the axi4_to_apb4_shim's gaxi_fifo_async CDC dependency
    went missing.

    A filelist B is "unrolled" into A when B's full resolved source set is a
    subset of what A lists directly, and A does not -f B. Single-source filelists
    are ignored by default (min_sources): one shared line is coincidence, not a
    copied body.
    """
    # Resolve every known filelist once.
    catalog: dict[Path, set[Path]] = {}
    for area in reg.get("area", []):
        for fl in area_filelists(area):
            s, _ = resolve(fl)
            if s:
                catalog[fl.resolve()] = set(s)

    findings: list[tuple[Path, Path, int]] = []
    for area in reg.get("area", []):
        for fl in area_filelists(area):
            fl = fl.resolve()
            direct, includes = direct_sources(fl)
            if not direct:
                continue
            for other, other_srcs in catalog.items():
                if other == fl or other in includes:
                    continue
                if len(other_srcs) < min_sources:
                    continue
                if other_srcs <= direct:
                    findings.append((fl, other, len(other_srcs)))

    # Drop a finding when a broader filelist already covers it, so one inlined
    # body is not reported once per sub-filelist it happens to contain.
    by_consumer: dict[Path, list[tuple[Path, int]]] = {}
    for consumer, other, n in findings:
        by_consumer.setdefault(consumer, []).append((other, n))

    total = 0
    for consumer in sorted(by_consumer):
        hits = sorted(by_consumer[consumer], key=lambda x: -x[1])
        kept = []
        for other, n in hits:
            if any(catalog[other] < catalog[k] for k, _ in kept):
                continue
            kept.append((other, n))
        total += len(kept)
        print(f"{rel(consumer)}")
        for other, n in kept:
            print(f"    unrolled: {rel(other)}  ({n} sources inlined)")
            print(f"      -> replace those lines with: -f $REPO_ROOT/{rel(other)}")
    print()
    if total:
        print(f"FAIL: {total} unrolled filelist body/bodies; -f the filelist instead")
        return 1
    print("PASS: no filelist inlines another filelist's body")
    return 0


def cmd_blindspots(reg: dict, ratchet: bool = False,
                   update_baseline: bool = False) -> int:
    """Find the things --check and --audit structurally CANNOT see.

    Both of those walk the filelist graph, so anything outside it is invisible:
    a filelist nobody registered, a test that builds its own source array, a
    formal harness that hand-lists. Each of those hid a real defect in the week
    of 2026-07-25:

      * rtl/cdc and flows-stream-monitor were unregistered, so their modules
        were exempt from coverage without anyone deciding they should be
      * three wavedrom tests hand-listed rtl/common paths and stayed broken for
        a day behind a green --check
      * four apb*_slave_cdc .sby harnesses were missing gaxi_fifo_async and its
        whole dependency tree

    This is the check for that class. Exit 1 if anything is found.
    """
    findings = 0
    detail = not ratchet   # ratchet mode reports deltas, not the whole backlog

    # 1. Filelists that no registered area covers.
    registered: set[Path] = set()
    for area in reg.get("area", []):
        registered.update(area_filelists(area))
    # Tracked files only. rglob("*.f") also finds Fortran under venv/, which is
    # noise: if git does not track it, it is not ours to register.
    tracked = subprocess.run(["git", "ls-files", "*.f"], cwd=REPO_ROOT,
                             capture_output=True, text=True).stdout.split()
    on_disk = {REPO_ROOT / t for t in tracked}
    orphans = sorted(on_disk - registered)
    if orphans:
        findings += len(orphans)
        if detail:
            print(f"UNREGISTERED FILELISTS ({len(orphans)}) -- invisible to --check/--find:")
            for o in orphans:
                print(f"    {rel(o)}")
            print("    fix: add the containing dir to an area's filelist_dirs in filelists.toml")
            print()
    # 2. Tests that build their own source array instead of taking a filelist.
    hand: list[tuple[str, str]] = []
    for t in sorted(REPO_ROOT.glob("val/*/test_*.py")) + sorted(REPO_ROOT.glob("projects/**/dv/tests/test_*.py")):
        body = t.read_text(errors="ignore")
        if re.search(r"^\s*verilog_sources\s*=\s*\[", body, re.M):
            hand.append((rel(t), "hand-listed verilog_sources"))
        elif "verilog_sources.append" in body:
            hand.append((rel(t), "appends to a filelist's sources"))
    if hand:
        findings += len(hand)
        if detail:
            print(f"TESTS NOT TAKING A FILELIST ({len(hand)}) -- a stale path here passes --check:")
            for f, why in hand:
                print(f"    {f}  ({why})")
            print("    fix: get_sources_from_filelist(repo_root=..., filelist_path=...)")
            print()
    # 3. Formal harnesses whose [files] entries do not resolve.
    dangling: list[tuple[str, str]] = []
    for sby in sorted(REPO_ROOT.rglob("*.sby")):
        base = sby.parent
        for raw in sby.read_text(errors="ignore").splitlines():
            for tok in re.findall(r"(\.\./[\w./-]+\.svh?)", raw):
                if not (base / tok).resolve().exists():
                    dangling.append((rel(sby), tok))
    if dangling:
        findings += len(dangling)
        by_file: dict[str, int] = {}
        for f, _ in dangling:
            by_file[f] = by_file.get(f, 0) + 1
        if detail:
            print(f"FORMAL HARNESSES WITH DEAD SOURCE PATHS ({len(dangling)} refs in {len(by_file)} files):")
            for f, n in sorted(by_file.items(), key=lambda kv: -kv[1])[:12]:
                print(f"    {n:4d}  {f}")
            if len(by_file) > 12:
                print(f"    ... and {len(by_file) - 12} more")
            print("    fix: generate [script]/[files] from the area's filelist")
            print()
    counts = {
        "unregistered_filelists": len(orphans),
        "hand_listed_tests": len(hand),
        "dead_harness_paths": len(dangling),
    }

    if update_baseline:
        BASELINE.write_text(json.dumps(counts, indent=2, sort_keys=True) + "\n")
        print(f"baseline written to {rel(BASELINE)}:")
        for k, v in sorted(counts.items()):
            print(f"    {k:<24} {v}")
        return 0

    if not ratchet:
        if findings:
            print(f"FAIL: {findings} blind-spot finding(s)")
            return 1
        print("PASS: no unregistered filelists, hand-listed tests, or dead harness paths")
        return 0

    # Ratchet: a number may fall, never rise. Lets a gate go in TODAY against a
    # real backlog -- a NEW violation fails immediately while the existing ones
    # block nobody. Gating on zero when the count is in the hundreds just
    # teaches people to pass --no-verify.
    if not BASELINE.is_file():
        print(f"no baseline at {rel(BASELINE)}; write one with --update-baseline")
        return 1
    base = json.loads(BASELINE.read_text())
    worse, better = [], []
    for k, now in sorted(counts.items()):
        was = base.get(k, 0)
        if now > was:
            worse.append(f"    {k:<24} {was} -> {now}   (+{now - was})")
        elif now < was:
            better.append(f"    {k:<24} {was} -> {now}   ({now - was})")
    if better:
        print("IMPROVED since the baseline:")
        print("\n".join(better))
        print(f"    lower it: python3 {rel(Path(__file__))} --blindspots --update-baseline")
        print()
    if worse:
        print("REGRESSED -- a new blind spot was introduced:")
        print("\n".join(worse))
        print()
        print("FAIL: the fix is to use a filelist, not to raise the baseline.")
        return 1
    print(f"PASS (ratchet): no class grew. {findings} known finding(s) outstanding; see TOOL-012.")
    return 0


def cmd_resolve(path: str) -> int:
    fl = Path(path)
    if not fl.is_absolute():
        fl = REPO_ROOT / path
    srcs, problems = resolve(fl)
    for s in srcs:
        print(rel(s))
    for p in problems:
        print(f"PROBLEM: {p}", file=sys.stderr)
    return 1 if problems else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--list", action="store_true", help="show every filelist area and where it lives")
    g.add_argument("--check", action="store_true", help="verify module coverage in library areas")
    g.add_argument("--audit", action="store_true", help="find consumers hand-listing another area's sources")
    g.add_argument("--unrolled", action="store_true",
                   help="find filelists that inline another filelist's body instead of -f'ing it")
    g.add_argument("--blindspots", action="store_true",
                   help="find what --check/--audit cannot see: unregistered filelists, "
                        "hand-listed tests, dead formal-harness paths")
    g.add_argument("--find", metavar="MODULE", help="show which filelist provides a module")
    g.add_argument("--resolve", metavar="FILELIST", help="expand a filelist to its source list")
    ap.add_argument("--ratchet", action="store_true",
                    help="with --blindspots: fail only if a class GREW vs the baseline")
    ap.add_argument("--update-baseline", action="store_true",
                    help="with --blindspots: rewrite the baseline from the current counts")
    args = ap.parse_args()

    if args.resolve:
        return cmd_resolve(args.resolve)

    reg = load_registry()
    if args.list:
        return cmd_list(reg)
    if args.check:
        return cmd_check(reg)
    if args.audit:
        return cmd_audit(reg)
    if args.unrolled:
        return cmd_unrolled(reg)
    if args.blindspots:
        return cmd_blindspots(reg, args.ratchet, args.update_baseline)
    if args.find:
        return cmd_find(reg, args.find)
    return 0


if __name__ == "__main__":
    sys.exit(main())
