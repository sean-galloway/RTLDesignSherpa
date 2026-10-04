#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Measure the formal suite and report what actually runs.

FORMAL_PRIORITY.md's Status column was hand-maintained and was wrong in both
directions: modules listed PASSING whose task directory held no proof at all,
and modules listed PASSING whose proof had never once elaborated. A status
that is typed rather than measured drifts silently, because a stale row looks
exactly like a current one.

    python3 bin/formal_status.py                    # every area, discovered
    python3 bin/formal_status.py --areas pumice cdc  # just these
    python3 bin/formal_status.py --inventory        # no runs: what EXISTS
    python3 bin/formal_status.py --check-flats      # no runs: is each
                                                    # committed *_flat.v still
                                                    # what its sources flatten to?
    python3 bin/formal_status.py --markdown         # table for the tracker

Exit status is non-zero if any task fails, so this can gate CI.
"""
from __future__ import annotations

import argparse
import json
import os
import pathlib
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent


def default_areas() -> list[str]:
    """Every formal area that actually holds a proof -- DISCOVERED, not listed.

    This was a hand-kept list, ["amba", "cdc", "common", "integ_common"], and it
    had drifted exactly the way this file's docstring warns a typed status does:
    `integ_common` did not exist at all (discover() skipped it silently), and
    seven areas that DID exist were missing -- apbx_xbar, bridge, converters,
    pumice, rapids, retro_legacy_blocks and stream, 58 proofs between them. The
    suite reported ~297 task directories because that is all it was looking at.
    A tool whose job is to measure the suite must not be told where the suite is.
    """
    base = ROOT / "formal"
    if not base.is_dir():
        return []
    return sorted(d.name for d in base.iterdir()
                  if d.is_dir() and any(d.glob("*/*.sby")))


def sby_tasks(sby: pathlib.Path) -> list[str]:
    """The [tasks] section, or a single unnamed run."""
    body = sby.read_text(errors="replace")
    m = re.search(r"^\[tasks\]\s*$(.*?)(?=^\[|\Z)", body, re.M | re.S)
    if not m:
        return [""]
    names = [ln.split()[0] for ln in m.group(1).splitlines() if ln.strip()
             and not ln.strip().startswith("#")]
    return names or [""]


def discover(areas):
    """Every task directory, and how it reads its RTL."""
    out = []
    for area in areas:
        adir = ROOT / "formal" / area
        if not adir.is_dir():
            continue
        for d in sorted(p for p in adir.iterdir() if p.is_dir()):
            sbys = sorted(d.glob("*.sby"))
            out.append({
                "area": area,
                "name": d.name,
                "dir": d,
                "sby": sbys[0] if sbys else None,
                # A task with its own Makefile runs sv2v first (flatten flow).
                "flow": "flatten" if (d / "Makefile").exists() else "direct",
                "tasks": sby_tasks(sbys[0]) if sbys else [],
            })
    return out


def run_task(entry, task, timeout):
    d, sby = entry["dir"], entry["sby"]
    if entry["flow"] == "flatten":
        cmd = ["make", "-C", str(d), task or "all"]
    else:
        cmd = ["sby", "-f", sby.name] + ([task] if task else [])
    t0 = time.time()
    # Own a process GROUP, not just a child. sby spawns solver processes that
    # outlive it; killing only the direct child leaves them running, and they
    # then compete with every task after this one -- so one slow proof skews
    # the timings of the whole sweep and can starve it outright.
    proc = subprocess.Popen(cmd, cwd=str(d), stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True,
                            start_new_session=True)
    try:
        blob = proc.communicate(timeout=timeout)[0]
    except subprocess.TimeoutExpired:
        try:
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            proc.kill()
        proc.communicate()
        return "TIMEOUT", timeout
    m = re.findall(r"DONE \((PASS|FAIL|ERROR|UNKNOWN)", blob)
    if not m:
        return "NORESULT", time.time() - t0
    # a flatten `make all` runs several sby tasks; worst result wins
    for bad in ("ERROR", "FAIL", "UNKNOWN"):
        if bad in m:
            return bad, time.time() - t0
    return "PASS", time.time() - t0


# ---------------------------------------------------------------------------
# --check-flats: is the committed sv2v snapshot still what the sources say?
#
# A committed *_flat.v is only trustworthy while it matches the RTL. Two
# mechanisms, cheapest first:
#   (a) the proof's Makefile declares the house `check-flat` target
#       (formal/common/counter_freq_invariant is the reference) -- delegate;
#   (b) replay the flatten recipe captured by `make -nB <flat>` with the
#       flat's output redirect retargeted to a temp file, then compare
#       whitespace-normalized. Recipes that write anywhere in-tree besides
#       that one redirect are UNHANDLED rather than replayed -- silently
#       corrupting the tree is worse than asking for a check-flat target.
# ---------------------------------------------------------------------------

def find_sv2v() -> str | None:
    """sv2v on PATH, else the repo-dev-machine location. None if absent."""
    found = shutil.which("sv2v")
    if found:
        return found
    for cand in ("/mnt/data/tools/sv2v",):
        if pathlib.Path(cand).exists():
            return cand
    return None


def _recipe_lines(d: pathlib.Path, flat: pathlib.Path,
                  env: dict) -> list[str] | None:
    """The expanded flatten recipe from make -nB, or None if it cannot run."""
    dry = subprocess.run(
        ["make", "-C", str(d), "-nB", flat.name],
        capture_output=True, text=True, env=env, timeout=60)
    if dry.returncode != 0:
        return None
    lines = []
    for ln in dry.stdout.splitlines():
        s = ln.strip()
        if not s or s.startswith(("make:", "make[", "#")):
            continue
        lines.append(s)
    return lines


def _writes_in_tree(line: str, allowed: str) -> bool:
    """True if a recipe line writes anywhere but the allowed redirect target.

    This is an allowlist, not a sandbox: it names the writers seen in this
    repo's recipes (redirects, cp/mv/touch/mkdir/rm, -o). A recipe using an
    unlisted writer such as `sed -i`, `install`, or `dd` would slip through.
    That is a deliberate posture -- the proofs whose recipes write in-tree
    all delegate to their own check-flat target, so the replay path only
    reaches simple single-redirect recipes -- but extend the list if a new
    writer ever shows up in a formal Makefile.
    """
    for m in re.finditer(r"(?:^|[\s;|])(?:\d*)>(?!&)\s*(\S+)", line):
        if m.group(1).strip('"\'') != allowed:
            return True
    if re.search(r"(?:^|[\s;|])(?:cp|mv|touch|mkdir|rm)\s", line):
        return True
    m = re.search(r"(?:^|\s)-o\s+(\S+)", line)
    if m and not m.group(1).startswith("/tmp"):
        # -o output we cannot prove is outside the tree; a $(TMPDIR) make
        # variable may expand to a relative prep dir inside the proof.
        return True
    return False


def _norm_tokens(path: pathlib.Path) -> list[str]:
    return path.read_text(errors="replace").split()


def _first_diff(a: list[str], b: list[str]) -> str:
    for i, (x, y) in enumerate(zip(a, b)):
        if x != y:
            return f"first difference near token {i}: flat={x!r} regenerated={y!r}"
    return f"length differs ({len(a)} vs {len(b)} tokens)"


def find_flat(d: pathlib.Path, name: str) -> pathlib.Path | None:
    """The proof's committed flat: convention name, else a sole *_flat.v."""
    flat = d / f"{name}_flat.v"
    if flat.exists():
        return flat
    flats = sorted(p for p in d.glob("*_flat.v") if p.is_file())
    return flats[0] if len(flats) == 1 else None


def _gitignored(path: pathlib.Path) -> bool:
    """True if git ignores this path (an area that deliberately does not
    commit flats -- formal/pumice/.gitignore documents the pattern)."""
    try:
        rel = path.resolve().relative_to(ROOT.resolve())
    except ValueError:
        return False
    r = subprocess.run(["git", "check-ignore", "-q", rel.as_posix()],
                       cwd=str(ROOT), capture_output=True)
    return r.returncode == 0


def check_flat(entry, env) -> tuple[str, str]:
    """One flatten-flow proof: (CURRENT|STALE|UNHANDLED|ERROR, detail)."""
    d: pathlib.Path = entry["dir"]
    flat = find_flat(d, entry["name"])
    if flat is None:
        n = len(list(d.glob("*_flat.v")))
        if n == 0 and _gitignored(d / f"{entry['name']}_flat.v"):
            return ("SKIPPED",
                    "this area gitignores *_flat.v -- flats are built, not "
                    "committed (formal/pumice pattern); nothing to go stale")
        return "UNHANDLED", ("no committed *_flat.v" if n == 0
                             else "multiple committed *_flat.v; ambiguous")

    # (a) house check-flat target
    probe = subprocess.run(["make", "-C", str(d), "-n", "check-flat"],
                           capture_output=True, env=env, timeout=60)
    if probe.returncode == 0:
        r = subprocess.run(["make", "-C", str(d), "check-flat"],
                           capture_output=True, text=True, env=env, timeout=600)
        if r.returncode == 0:
            return "CURRENT", "check-flat target reports current"
        tail = " ".join((r.stdout + r.stderr).split())[:200]
        return "STALE", f"check-flat target failed: {tail}"

    # (b) recipe replay
    lines = _recipe_lines(d, flat, env)
    if not lines:
        return "UNHANDLED", "make -nB <flat> failed; needs a check-flat target"
    redirect_hits = [i for i, ln in enumerate(lines)
                     if re.search(r">\s*\"?" + re.escape(flat.name) + r"\s*$", ln)]
    if len(redirect_hits) != 1:
        return ("UNHANDLED",
                "recipe does not have exactly one '<sv2v ...> > <flat>' "
                "redirect; needs a check-flat target")
    for ln in lines:
        if _writes_in_tree(ln, flat.name):
            return ("UNHANDLED",
                    "recipe writes in-tree besides the flat; refusing to "
                    "replay -- add a check-flat target")
    fd, tmpname = tempfile.mkstemp(suffix=".flat.v")
    os.close(fd)
    tmp = pathlib.Path(tmpname)
    try:
        replay = [ln if i != redirect_hits[0]
                  else re.sub(r">\s*\"?" + re.escape(flat.name) + r"\s*$",
                              f"> {tmp}", ln)
                  for i, ln in enumerate(lines)]
        r = subprocess.run(["/bin/bash", "-c", " && ".join(replay)],
                           cwd=str(d), capture_output=True, text=True,
                           env=env, timeout=600)
        if r.returncode != 0:
            tail = " ".join((r.stdout + r.stderr).split())[:200]
            return "ERROR", f"replay failed: {tail}"
        if _norm_tokens(flat) == _norm_tokens(tmp):
            return "CURRENT", "regenerated output matches committed flat"
        return "STALE", _first_diff(_norm_tokens(flat), _norm_tokens(tmp))
    finally:
        tmp.unlink(missing_ok=True)


def _staged_paths() -> set[str]:
    r = subprocess.run(["git", "diff", "--cached", "--name-only"],
                       cwd=str(ROOT), capture_output=True, text=True)
    if r.returncode != 0:
        return set()
    return {ln.strip() for ln in r.stdout.splitlines() if ln.strip()}


def _recipe_source_tokens(entry, env) -> set[str]:
    """Repo-relative source paths the flatten recipe references (for --staged)."""
    d: pathlib.Path = entry["dir"]
    flat = find_flat(d, entry["name"])
    if flat is None:
        return set()
    lines = _recipe_lines(d, flat, env) or []
    out = set()
    for tok in " ".join(lines).split():
        tok = tok.strip(";|")
        if not (tok.endswith((".sv", ".svh", ".v", ".f", ".rdl")) or "/" in tok):
            continue
        if tok.startswith(("/tmp", "$")):
            continue
        p = (d / tok).resolve()
        try:
            out.add(p.relative_to(ROOT.resolve()).as_posix())
        except ValueError:
            pass
    return out


def check_flats(entries, args) -> int:
    """The --check-flats mode. Returns the exit status."""
    flatten = []
    for e in entries:
        if e["flow"] != "flatten":
            continue
        # Some task Makefiles are pure sby drivers despite existing -- see
        # formal/converters/uart_rx ("No sv2v needed"). Only a Makefile that
        # names a *_flat.v actually flattens; the rest are not this mode's.
        if "_flat.v" not in (e["dir"] / "Makefile").read_text(errors="replace"):
            continue
        flatten.append(e)
    env = dict(os.environ)
    sv2v = find_sv2v()
    if sv2v:
        env["PATH"] = str(pathlib.Path(sv2v).parent) + os.pathsep + env.get("PATH", "")

    if args.staged:
        staged = _staged_paths()
        root = ROOT.resolve()
        kept = []
        for e in flatten:
            flat = find_flat(e["dir"], e["name"])
            flat_rel = (flat.resolve().relative_to(root).as_posix()
                        if flat is not None else None)
            if ((flat_rel is not None and flat_rel in staged)
                    or (_recipe_source_tokens(e, env) & staged)):
                kept.append(e)
        flatten = kept

    if flatten and not sv2v:
        print("ERROR: sv2v not found (looked on PATH and /mnt/data/tools); "
              f"cannot check {len(flatten)} flatten proofs", file=sys.stderr)
        return 1

    rows = []
    for e in flatten:
        st, detail = check_flat(e, env)
        rows.append({"area": e["area"], "name": e["name"],
                     "status": st, "detail": detail})

    tally = {}
    for r in rows:
        if r["status"] == "SKIPPED":
            continue
        tally[r["status"]] = tally.get(r["status"], 0) + 1
        if r["status"] != "CURRENT":
            print(f"  {r['status']:10s} {r['area']}/{r['name']}: {r['detail']}")
    n_skip = sum(1 for r in rows if r["status"] == "SKIPPED")
    print("  ".join([f"checked={len(rows) - n_skip}"] +
                    ([f"skipped={n_skip}"] if n_skip else []) +
                    [f"{k}={v}" for k, v in sorted(tally.items())]))
    if any(r["status"] == "CURRENT" for r in rows):
        names = ", ".join(f"{r['area']}/{r['name']}" for r in rows
                          if r["status"] == "CURRENT")
        print(f"  CURRENT {len([r for r in rows if r['status'] == 'CURRENT'])}: "
              f"{names[:400]}{' ...' if len(names) > 400 else ''}")
    if args.json:
        pathlib.Path(args.json).write_text(json.dumps(rows, indent=1))
    return 1 if any(r["status"] in ("STALE", "UNHANDLED", "ERROR")
                    for r in rows) else 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--areas", nargs="+", default=None,
                    help="areas to measure (default: every formal/<area> holding a proof)")
    ap.add_argument("--inventory", action="store_true",
                    help="do not run anything; report what exists")
    ap.add_argument("--check-flats", action="store_true",
                    help="do not run proofs; re-flatten and diff each committed "
                         "*_flat.v against its sources (exit 1 on drift)")
    ap.add_argument("--staged", action="store_true",
                    help="with --check-flats: only proofs whose flat or sources "
                         "are staged in git")
    ap.add_argument("--markdown", action="store_true")
    ap.add_argument("--json", metavar="PATH")
    ap.add_argument("--timeout", type=int, default=1500)
    ap.add_argument("--only", nargs="*", default=None)
    # Skip named tasks -- e.g. one already running in its own directory from a
    # separate long-budget job. Two sby runs writing the same <task>_prove/ dir
    # corrupt each other, and nothing in sby prevents it.
    ap.add_argument("--exclude", nargs="*", default=None)
    args = ap.parse_args()

    args.areas = args.areas or default_areas()
    entries = discover(args.areas)
    if args.only:
        entries = [e for e in entries if e["name"] in args.only]
    if args.exclude:
        entries = [e for e in entries if e["name"] not in args.exclude]

    if args.inventory:
        print(f"{len(entries)} task directories under formal/{{{','.join(args.areas)}}}")
        for flow in ("flatten", "direct"):
            n = [e for e in entries if e["flow"] == flow and e["sby"]]
            print(f"  {flow:8s} {len(n)}")
        empty = [e for e in entries if not e["sby"]]
        if empty:
            print(f"  NO .sby  {len(empty)}: " + ", ".join(e["name"] for e in empty))
        return 0

    if args.check_flats:
        return check_flats(entries, args)

    rows, bad = [], 0
    for i, e in enumerate(entries, 1):
        if not e["sby"]:
            rows.append({**{k: e[k] for k in ("area", "name", "flow")},
                         "task": "-", "status": "NOSBY", "secs": 0.0})
            bad += 1
            print(f"[{i}/{len(entries)}] {e['area']}/{e['name']}: NOSBY", file=sys.stderr)
            continue
        for task in e["tasks"]:
            st, secs = run_task(e, task, args.timeout)
            rows.append({**{k: e[k] for k in ("area", "name", "flow")},
                         "task": task or "(default)", "status": st, "secs": round(secs, 1)})
            if st != "PASS":
                bad += 1
            print(f"[{i}/{len(entries)}] {e['area']}/{e['name']} {task or ''}: {st} "
                  f"({secs:.0f}s)", file=sys.stderr)

    if args.json:
        pathlib.Path(args.json).write_text(json.dumps(rows, indent=1))

    tally = {}
    for r in rows:
        tally[r["status"]] = tally.get(r["status"], 0) + 1
    if args.markdown:
        print(f"<!-- generated by bin/formal_status.py on "
              f"{time.strftime('%Y-%m-%d')} -- do not hand-edit the Status column -->")
        print()
        print("| Area | Task | Flow | Result |")
        print("|---|---|---|---|")
        seen = {}
        for r in rows:
            k = (r["area"], r["name"])
            seen.setdefault(k, []).append(r["status"])
        for (area, name), sts in sorted(seen.items()):
            worst = next((s for s in ("NOSBY", "ERROR", "FAIL", "TIMEOUT",
                                      "NORESULT", "UNKNOWN") if s in sts), "PASS")
            flow = next(r["flow"] for r in rows if (r["area"], r["name"]) == (area, name))
            print(f"| {area} | {name} | {flow} | {worst} |")
        print()
    print("  ".join(f"{k}={v}" for k, v in sorted(tally.items())), file=sys.stderr)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
