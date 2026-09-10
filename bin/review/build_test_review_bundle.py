#!/usr/bin/env python3
"""Build a test-review bundle for an area, per vault/handbook/dv/test-review.md.

Per test file in val/<area>:
  1. resolve the TBClasses.* import chain (this repo, bin/TBClasses/), recursing
     into their own TBClasses imports;
  2. resolve the CocoTBFramework.* chain from the test AND every collected
     TBClasses file into $RDS_DV_REPO/src/CocoTBFramework (the local clone is a
     convenience copy -- read it, never edit it), recursing;
  3. record the test's filelist for RTL ground truth.

Layout (off-repo, one dir per area, split into parts by size like the doc
bundler):

    <out>/<area>[/parts/part_NN]/
      MANIFEST.md       test -> TB chain -> framework chain -> filelist
      TESTS.py          the test_*.py, each behind a ===== path banner
      TB.py             collected bin/TBClasses files, path banners
      FRAMEWORK.py      CocoTBFramework chain -- GOLDEN, never a finding target
      RTL_IFACES.sv     module parameter/port headers of the RTL under test

Usage: build_test_review_bundle.py <area> [out_dir]
       area: cdc | common | math | amba ...  out_dir default ~/rtl-test-review
"""
import ast
import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DV = os.environ.get("RDS_DV_REPO", "/home/seang/github/RTLDesignSherpa-DV")
LIMIT = 120_000 * 4  # chars per unit, same as the doc bundler

# Three import roots, not two. A Pattern B area (projects/components/<c>/dv/
# tests) keeps its TB classes in its OWN dv/tbclasses, imported as
# `projects.components.<c>.dv.tbclasses.<x>` -- invisible to a pattern that
# only knew TBClasses, so a bundle for such an area shipped its tests with no
# testbenches and the reviewer could not see what the test actually drives.
# That, plus main() only looking under val/, is why no projects/components
# area has ever had a testqc round (BRIDGE-007, unrun since 2026-09-04).
IMPORT_RE = re.compile(
    r"^\s*(?:from|import)\s+(TBClasses[\w.]*|CocoTBFramework[\w.]*|projects\.[\w.]*)", re.M)
# Bare sibling imports, resolved against the area's own tests directory.
SIBLING_RE = re.compile(r"^\s*(?:from|import)\s+([a-z_][\w]*)\s*(?:import|$)", re.M)
FILELIST_RE = re.compile(r"['\"]([^'\"]*filelists/[^'\"]+\.f)['\"]")
MODULE_HDR_RE = re.compile(r"^module\b.*?^\s*\);", re.M | re.S)

GOLDEN_BANNER = """
# ============================================================================
# GOLDEN FRAMEWORK -- independently reviewed ground truth, NOT a review
# target. Present so claims about framework usage can be checked (BFM names,
# factory methods, scoreboard APIs). Do NOT file findings on these files;
# the framework is reviewed in its own repo, and this local clone is a
# convenience download (read-only).
#
# Reduced to its API SURFACE -- module/class/function signatures and
# docstrings, bodies elided -- which is what "so claims about framework usage
# can be checked" needs. Full bodies made this 74% of every unit and forced
# one test per unit. Read a signature here; read the body in the DV repo.
# ============================================================================
"""


def resolve(mod):
    """'TBClasses.a.b' -> bin/TBClasses; 'projects.a.b' -> repo-relative;
    'CocoTBFramework.a.b' -> the DV clone."""
    parts = mod.split(".")
    if parts[0] == "TBClasses":
        p = os.path.join(REPO, "bin", "TBClasses", *parts[1:]) + ".py"
    elif parts[0] == "projects":
        p = os.path.join(REPO, *parts) + ".py"
    else:
        p = os.path.join(DV, "src", "CocoTBFramework", *parts[1:]) + ".py"
    return p if os.path.exists(p) else None


def chain(roots, want):
    """Transitive import closure over the given namespace(s).

    `want` is a prefix or a tuple of prefixes -- a Pattern B area's TB side
    spans both `TBClasses` (shared) and `projects.` (its own)."""
    seen, out, queue = set(), [], list(roots)
    while queue:
        path = queue.pop(0)
        if path in seen:
            continue
        seen.add(path)
        out.append(path)
        text = open(path, encoding="utf-8", errors="replace").read()
        for m in IMPORT_RE.findall(text):
            if not m.startswith(want):
                continue
            r = resolve(m)
            if r and r not in seen:
                queue.append(r)
    return out


def api_digest(path):
    """A framework file reduced to its API surface: module docstring, classes,
    and every def's signature + docstring, bodies elided.

    FRAMEWORK.py is GOLDEN -- present so claims about framework usage can be
    CHECKED (BFM names, factory methods, scoreboard APIs), never a finding
    target. Shipping full bodies made it 364KB of a 490KB unit on the bridge
    (74%), which pushed every single test over the size limit: 45 tests became
    45 one-test units, i.e. 45 reviewer calls each dominated by code nobody is
    allowed to file against. The signatures answer the question the bundle
    exists to answer; the bodies do not.

    Falls back to the raw text if the file will not parse, because a silently
    empty digest would be worse than a big one."""
    text = open(path, encoding="utf-8", errors="replace").read()
    try:
        tree = ast.parse(text)
    except SyntaxError:
        return text
    lines = text.splitlines()
    out = []
    mod_doc = ast.get_docstring(tree)
    if mod_doc:
        out.append(f'"""{mod_doc.strip()[:800]}"""')
        out.append("")

    def emit(node, indent):
        pad = " " * indent
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            # The signature as written, however many lines it spans.
            sig_end = node.body[0].lineno - 1 if node.body else node.lineno
            sig = "\n".join(lines[node.lineno - 1:sig_end]).rstrip()
            for d in node.decorator_list:
                out.append(f"{pad}@{ast.unparse(d)}")
            out.append(sig if sig.rstrip().endswith(":") else sig + ":")
            doc = ast.get_docstring(node)
            if doc:
                one = " ".join(doc.split())[:300]
                out.append(f'{pad}    """{one}"""')
            out.append(f"{pad}    ...")
            out.append("")
        elif isinstance(node, ast.ClassDef):
            bases = ", ".join(ast.unparse(b) for b in node.bases)
            out.append(f"{pad}class {node.name}({bases}):" if bases else f"{pad}class {node.name}:")
            doc = ast.get_docstring(node)
            if doc:
                one = " ".join(doc.split())[:400]
                out.append(f'{pad}    """{one}"""')
            body = [n for n in node.body if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))]
            if not body:
                out.append(f"{pad}    ...")
            for n in body:
                emit(n, indent + 4)
            out.append("")

    for node in tree.body:
        if isinstance(node, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)):
            emit(node, 0)
        elif isinstance(node, ast.Assign):
            # Module-level constants are part of the API (profile tables,
            # signal-pattern maps); keep the short ones.
            src = ast.unparse(node)
            if len(src) <= 400:
                out.append(src)
    return "\n".join(out) + "\n"


def cat(paths, banner_comment, digest=False):
    out = []
    for p in paths:
        rel = os.path.relpath(p, REPO) if p.startswith(REPO) else p
        out.append(f"\n{banner_comment} {'=' * 60}\n{banner_comment} FILE: {rel}\n"
                   f"{banner_comment} {'=' * 60}\n")
        out.append(api_digest(p) if digest
                   else open(p, encoding="utf-8", errors="replace").read())
    return "".join(out)


def rtl_ifaces(filelists):
    """Module headers of the RTL a test builds, for port/parameter ground truth.

    Resolved by the repo's OWN filelist reader, not by re-parsing the .f here.
    The hand-rolled version read only bare paths and skipped any line starting
    with '-' or '+', so on a filelist written the normal way -- $REPO_ROOT
    paths, `-f` includes of other filelists -- it found nothing and wrote an
    EMPTY RTL_IFACES.sv. Measured on the bridge: 707 `-f` lines and 311
    $REPO_ROOT lines across its filelists, so a reviewer would have been asked
    to audit tests against RTL it could not see. Keeping one reader also means
    the bundle cannot drift from what the tests actually compile
    ([[filelists]])."""
    sys.path.insert(0, os.path.join(REPO, "bin"))
    try:
        from TBClasses.shared.filelist_utils import get_sources_from_filelist
    except ImportError:
        return "// RTL interfaces unavailable: TBClasses.shared.filelist_utils not importable\n"

    ifaces, seen = [], set()
    for fl in filelists:
        if not os.path.exists(os.path.join(REPO, fl)):
            continue
        try:
            srcs, _incs = get_sources_from_filelist(repo_root=REPO, filelist_path=fl)
        except Exception as e:                      # noqa: BLE001 - report, do not hide
            ifaces.append(f"// {fl}: could not resolve ({e})\n")
            continue
        for src in srcs:
            if not src.endswith(".sv") or src in seen or not os.path.exists(src):
                continue
            seen.add(src)
            text = open(src, encoding="utf-8", errors="replace").read()
            for hdr in MODULE_HDR_RE.findall(text):
                ifaces.append(f"// ---- {os.path.relpath(src, REPO)} ----\n{hdr}\n")
    return "\n".join(ifaces)


def write_part(d, manifest, tests, tb, fw, ifaces):
    os.makedirs(d, exist_ok=True)
    open(os.path.join(d, "MANIFEST.md"), "w").write(manifest)
    open(os.path.join(d, "TESTS.py"), "w").write(tests)
    open(os.path.join(d, "TB.py"), "w").write(tb)
    open(os.path.join(d, "FRAMEWORK.py"), "w").write(GOLDEN_BANNER + fw)
    open(os.path.join(d, "RTL_IFACES.sv"), "w").write(ifaces)


def main():
    # build_test_review_bundle.py <area> [out_root] [--tests LISTFILE]
    #
    # --tests restricts the bundle to the test basenames in LISTFILE, one per
    # line. A re-round after integrating findings only needs to cover what the
    # fixes touched -- re-auditing files byte-identical to ones just reviewed
    # clean costs a unit each and finds nothing. Compute the list from the
    # diff, and include a test whose TB CHAIN changed even when the runner
    # itself did not: the TB holds the scenario generators, so a test can be
    # entirely rewritten underneath an untouched wrapper.
    argv = list(sys.argv[1:])
    only = None
    if "--tests" in argv:
        i = argv.index("--tests")
        only = {l.strip() for l in open(argv[i + 1], encoding="utf-8") if l.strip()}
        del argv[i:i + 2]
    area_arg = argv[0].rstrip("/")
    out_root = argv[1] if len(argv) > 1 else os.path.expanduser("~/rtl-test-review")

    # A bare name means val/<name>; a path means itself, so a Pattern B area
    # (projects/components/bridge/dv/tests) can be bundled too. The output
    # directory is named for the component, not the whole path.
    if os.path.isdir(os.path.join(REPO, "val", area_arg)):
        test_dir, area = os.path.join(REPO, "val", area_arg), area_arg
    elif os.path.isdir(os.path.join(REPO, area_arg)):
        test_dir = os.path.join(REPO, area_arg)
        parts = area_arg.split("/")
        area = parts[2] if area_arg.startswith("projects/components/") and len(parts) > 2 \
            else parts[-1]
    else:
        sys.exit(f"no such area: val/{area_arg} and {area_arg} both missing")

    tests = sorted(
        os.path.join(test_dir, f)
        for f in os.listdir(test_dir)
        if re.match(r"test_.*\.py$", f) and (only is None or f in only)
    )
    if not tests:
        sys.exit(f"no test_*.py under {os.path.relpath(test_dir, REPO)}" +
                 (f" matching --tests ({len(only)} names)" if only else ""))
    if only:
        missing = only - {os.path.basename(t) for t in tests}
        if missing:
            sys.exit(f"--tests names not found under {os.path.relpath(test_dir, REPO)}: {sorted(missing)}")
        print(f"scoped to {len(tests)} of the area's tests")

    entries = []  # (rel, tp, tbc, fwc, fls)
    units, cur, cur_size = [], [], 0
    for tp in tests:
        text = open(tp, encoding="utf-8", errors="replace").read()
        mods = IMPORT_RE.findall(text)
        tb0 = [r for m in mods
               if m.startswith(("TBClasses", "projects.")) if (r := resolve(m))]
        # Sibling helpers in the tests directory itself. An area often keeps
        # its scenario generators next to the tests and imports them bare
        # (`from monitor_stress_common import run_comprehensive`), which is
        # neither a TBClasses nor a projects. import and so was invisible:
        # the bridge's monitor units shipped without the file that drives
        # every phase, and the reviewer said so -- "could not be audited, so
        # extra_env propagation and the per-phase monitor assertions rest on
        # an unshown file". Those helpers ARE audit targets.
        for m in SIBLING_RE.findall(text):
            cand = os.path.join(test_dir, m + ".py")
            if os.path.exists(cand) and cand not in tb0:
                tb0.append(cand)
        fw0 = [r for m in mods if m.startswith("CocoTBFramework") if (r := resolve(m))]
        tbc = chain(tb0, ("TBClasses", "projects."))
        fw_seeds = list(fw0)
        for p in tbc:
            for m in IMPORT_RE.findall(open(p).read()):
                if m.startswith("CocoTBFramework"):
                    r = resolve(m)
                    if r:
                        fw_seeds.append(r)
        fwc = chain(fw_seeds, "CocoTBFramework")
        fls = sorted(set(FILELIST_RE.findall(text)))
        rel = os.path.relpath(tp, REPO)
        blob = cat([tp], "#") + cat(tbc, "#") + cat(fwc, "#", digest=True) + rtl_ifaces(fls)
        if cur and cur_size + len(blob) > LIMIT:
            units.append(cur)
            cur, cur_size = [], 0
        entries.append((rel, tp, tbc, fwc, fls))
        cur.append(entries[-1])
        cur_size += len(blob)
    if cur:
        units.append(cur)

    multi = len(units) > 1
    for i, unit in enumerate(units, 1):
        d = os.path.join(out_root, area, "parts", f"part_{i:02d}") if multi \
            else os.path.join(out_root, area)
        mlines = ["# Test-review manifest -- " + os.path.relpath(test_dir, REPO), ""]
        for rel, _tp, tbc, fwc, fls in unit:
            mlines.append(f"- `{rel}`")
            mlines.append(f"  - TB: {', '.join(os.path.relpath(p, REPO) for p in tbc) or '(inline/none)'}")
            mlines.append(f"  - FW: {', '.join(os.path.basename(p) for p in fwc) or '(none)'}")
            mlines.append(f"  - filelist: {', '.join(fls) or '(NONE FOUND)'}")
        write_part(d, "\n".join(mlines) + "\n",
                   cat([t[1] for t in unit], "#"),
                   cat(sorted({p for t in unit for p in t[2]}), "#"),
                   cat(sorted({p for t in unit for p in t[3]}), "#", digest=True),
                   rtl_ifaces(sorted({f for t in unit for f in t[4]})))
        print(f"{d}: {len(unit)} tests")

    print(f"\n{len(tests)} tests -> {len(units)} unit(s) under {out_root}/{area}")


if __name__ == "__main__":
    main()
