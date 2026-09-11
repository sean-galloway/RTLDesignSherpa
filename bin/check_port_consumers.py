#!/usr/bin/env python3
"""Adding a port to a module breaks every consumer that does not connect it.

On 2026-09-07 `ow_mant_interp` was added to `math_bf16_fast_reciprocal`.
Two of its three consumers were updated. The third,
`math_bf16_newton_raphson_recip`, was not, and Verilator's PINMISSING is an
ERROR under the flags cocotb passes -- so all five of that module's tests
failed to BUILD. They did not fail an assertion; they never simulated.

The FUNC subset never elaborated that module, so a raw `pytest math` run was
green. Only the FULL matrix built it. The gap between "the suite is green" and
"the design compiles" was fifteen minutes of wall clock and one changed port.

Verilator finds this in under a second, from a filelist that already exists.
So a script owns it, not a reviewer and not a full regression.

THE GAP IT HAD, 2026-09-11. It globbed only `rtl/*/lint_reports/verilator/*.f`
-- 385 filelists, every one in the repo-level rtl/ tree -- so NO COMPONENT
MODULE HAD EVER HAD A CONSUMER CHECKED. Four dangling pins went in that way
during the retro_legacy_blocks feature arc: pm_acpi's two reset-source inputs,
ioapic's destination mode, and uart's two DMA handshake pins were each added to
a block and never connected in rlb_top. Verilator reported all of them the
moment anybody linted rlb_top by hand, which nothing did.

Two things had to change. The glob now walks the components tree, and the
matcher follows `-f` includes: rlb_top.f does not name apb4_ioapic.sv at all,
it names that block's OWN filelist, so a matcher looking only at direct paths
found no consumer and printed "no consumer was checked" for every RLB block.
And the pre-commit hook captured this script's output into a variable that it
printed only on failure, so that note was invisible -- a warning shown only
when something else fails is not a warning.

Scope is deliberately narrow, to keep it free of false positives:

  * only .sv files whose module PORT SET changed against HEAD are considered
    (a body-only edit triggers nothing);
  * only filelists that actually pull in the changed file, directly or through
    a -f include, are linted -- these are that module's real consumers;
  * only PINMISSING / PINNOTFOUND are reported, and only for the pins THIS
    CHANGE TOUCHED (the symmetric difference of the port sets: an added port
    shows up as PINMISSING, a removed one as PINNOTFOUND). Areas carry
    pre-existing warnings -- misc had 48 across ten consumers when this was
    measured -- and a gate that fails a commit for somebody else's problem is
    one people learn to bypass, which is the same as not having one.

Usage:
    check_port_consumers.py            # staged .sv (pre-commit)
    check_port_consumers.py <file>...  # explicit files
"""
from __future__ import annotations

import os
import re
import subprocess
import sys
from pathlib import Path

# NOT PINCONNECTEMPTY. This gate's own guidance tells you to fix a missing pin
# with an explicit empty connection, `.port()`, when the consumer does not want
# the signal -- so flagging that same form would contradict the advice in the
# failure message. An explicit empty pin is deliberate and legible; an OMITTED
# pin is the accident. See silent-fallbacks rule 10.
PIN_ERRORS = ("PINMISSING", "PINNOTFOUND")

# `module foo #(...) ( ... );` -- we only need the port NAME set, so match the
# direction keyword and take the last identifier before , or ) or a comment.
PORT_RE = re.compile(
    r"^\s*(?:input|output|inout)\b[^;]*?([A-Za-z_]\w*)\s*(?:,|\)|$)", re.M
)
MODULE_RE = re.compile(r"^\s*module\s+([A-Za-z_]\w*)", re.M)


def repo_root() -> Path:
    return Path(subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        capture_output=True, text=True, check=True).stdout.strip())


def port_set(text: str) -> set[str]:
    """Port names in the module header (everything before the first
    `endmodule`; good enough, since we compare a file against ITSELF)."""
    head = text.split("endmodule", 1)[0]
    return set(PORT_RE.findall(head))


def head_blob(root: Path, rel: str) -> str | None:
    r = subprocess.run(["git", "show", f"HEAD:{rel}"],
                       cwd=root, capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None


def staged_sv(root: Path) -> list[str]:
    r = subprocess.run(["git", "diff", "--cached", "--name-only",
                        "--diff-filter=ACM"],
                       cwd=root, capture_output=True, text=True, check=True)
    return [f for f in r.stdout.splitlines() if f.endswith(".sv")]


# Where consumers live. The first glob is the repo-level rtl/ tree's flattened
# lint filelists. The second is the components tree, which has no flattened
# filelists at all -- it has hand-written ones, and until 2026-09-11 this check
# globbed only the first, so NO COMPONENT MODULE HAD EVER HAD A CONSUMER
# CHECKED. Four dangling pins went in that way during the RLB feature arc:
# pm_acpi's two reset-source inputs, ioapic's destination mode, and uart's two
# DMA handshake pins were all added to a block and not connected in rlb_top.
# Verilator reported every one of them the moment anybody linted rlb_top by
# hand, which nothing did.
CONSUMER_GLOBS = (
    "rtl/*/lint_reports/verilator/*.f",
    # Recursive, because the components tree has at least a dozen filelist
    # layouts -- rtl/<block>/filelists/, rtl/filelists/<tier>/, and
    # rtl/rlb_top/rlb_top.f sitting loose in its own directory. An enumerated
    # set of patterns missed that last one on the first attempt, which is the
    # same class of miss this whole check exists to stop.
    "projects/components/**/*.f",
)

# Build output, not sources. A filelist regenerated into a sim_build directory
# is a copy of one already covered, and linting it is wasted time.
CONSUMER_SKIP = ("local_sim_build", "sim_build", "/build/", "obj_dir")


def _lists_source(root: Path, filelist: Path, name: str,
                  seen: set[Path] | None = None) -> bool:
    """Does this filelist pull in <name>, directly or through a -f include?

    The include hop is the whole point for a component top. rlb_top.f does not
    name apb4_ioapic.sv at all -- it says
    `-f $REPO_ROOT/.../ioapic/filelists/apb4_ioapic.f`. A matcher that only
    looked at direct paths therefore found no consumer for any RLB block and
    reported "no consumer was checked" for every one of them, which is how
    four dangling pins reached the top level.
    """
    seen = seen if seen is not None else set()
    try:
        filelist = filelist.resolve()
    except OSError:
        return False
    if filelist in seen or not filelist.is_file():
        return False
    seen.add(filelist)

    for line in filelist.read_text(errors="ignore").splitlines():
        line = line.split("//")[0].strip()
        if not line or line.startswith("#"):
            continue
        if line.endswith("/" + name):
            return True
        if line.startswith("-f "):
            inc = expand_roots(root, line[3:].strip())
            if inc and _lists_source(root, Path(inc), name, seen):
                return True
    return False


def expand_roots(root: Path, token: str) -> str:
    """$REPO_ROOT / $<AREA>_ROOT -> a real path, using the registry's mapping."""
    env = lint_env(root)
    out = token
    for var in sorted(env, key=len, reverse=True):
        if "$" + var in out:
            out = out.replace("$" + var, env[var])
    return out if "$" not in out else ""


def consumers_of(root: Path, rel: str) -> list[Path]:
    """Filelists that pull in this source AND are not its own."""
    hits = []
    name = Path(rel).name
    for pattern in CONSUMER_GLOBS:
        for f in root.glob(pattern):
            if f.stem == Path(rel).stem:
                continue                  # the module's own filelist
            if any(skip in str(f) for skip in CONSUMER_SKIP):
                continue
            if _lists_source(root, f, name):
                hits.append(f)
    return sorted(set(hits))


def lint_env(root: Path) -> dict:
    """Component filelists reference $REPO_ROOT and $<AREA>_ROOT. Verilator
    expands those from the environment, so a filelist that uses them lints
    clean only if they are set -- and silently finds no files if they are not.

    The mapping is not duplicated here: bin/filelist_registry.py owns it, and a
    second copy is how the two drift.
    """
    env = dict(os.environ)
    env["REPO_ROOT"] = str(root)
    try:
        sys.path.insert(0, str(root / "bin"))
        from filelist_registry import ROOT_VARS          # noqa: PLC0415
        for var, rel in ROOT_VARS.items():
            env[var] = str(root / rel) if rel else str(root)
    except Exception:                                     # noqa: BLE001
        pass                                              # REPO_ROOT alone
    return env


def lint(root: Path, filelist: Path) -> list[str]:
    r = subprocess.run(
        ["verilator", "--lint-only", "-sv", "-f", str(filelist)],
        cwd=root, capture_output=True, text=True, env=lint_env(root))
    return [ln for ln in (r.stdout + r.stderr).splitlines()
            if any(e in ln for e in PIN_ERRORS)]


def main(argv: list[str]) -> int:
    root = repo_root()
    files = argv[1:] or staged_sv(root)
    if not files:
        return 0

    changed: list[str] = []
    for rel in files:
        path = root / rel
        if not path.is_file():
            continue
        old = head_blob(root, rel)
        if old is None:
            continue                      # new file: no consumers can be stale
        if port_set(old) != port_set(path.read_text(errors="ignore")):
            changed.append(rel)

    if not changed:
        return 0

    failures: dict[str, list[str]] = {}
    unchecked: list[str] = []
    for rel in changed:
        cons = consumers_of(root, rel)
        if not cons:
            unchecked.append(rel)
            continue
        # ONLY THE PINS THIS CHANGE TOUCHED. An area can carry pre-existing
        # pin warnings -- misc had 48 when this was measured on 2026-09-11 --
        # and a gate that fails a commit for somebody else's problem is a gate
        # people learn to bypass, which is the same as not having one. The
        # symmetric difference is the right filter both ways: an ADDED port
        # shows up as PINMISSING at a consumer, a REMOVED one as PINNOTFOUND.
        touched = port_set(head_blob(root, rel) or "") ^ \
            port_set((root / rel).read_text(errors="ignore"))
        for fl in cons:
            bad = [ln for ln in lint(root, fl)
                   if any(f"'{t}'" in ln for t in touched)]
            if bad:
                failures.setdefault(fl.stem, []).extend(bad)

    for rel in unchecked:
        mods = MODULE_RE.findall((root / rel).read_text(errors="ignore"))
        print(f"[port-consumers] note: {rel} changed its port list "
              f"({', '.join(mods) or 'module'}) but no OTHER lint filelist "
              f"lists it, so no consumer was checked.", file=sys.stderr)

    if failures:
        print("[port-consumers] a changed port list broke its consumers:",
              file=sys.stderr)
        for stem, lines in failures.items():
            print(f"\n  consumer: {stem}", file=sys.stderr)
            for ln in lines[:6]:
                print(f"    {ln.strip()}", file=sys.stderr)
        print("\n  Connect the port at every instantiation (an explicit empty"
              "\n  connection, `.port()`, is fine when the consumer does not"
              "\n  want it -- it says so on purpose). PINMISSING is an ERROR"
              "\n  under the flags cocotb passes, so these do not fail a test:"
              "\n  they fail the BUILD, and the test never runs.", file=sys.stderr)
        return 1

    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
