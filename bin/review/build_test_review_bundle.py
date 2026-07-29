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
import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DV = os.environ.get("RDS_DV_REPO", "/home/seang/github/RTLDesignSherpa-DV")
LIMIT = 120_000 * 4  # chars per unit, same as the doc bundler

IMPORT_RE = re.compile(r"^\s*(?:from|import)\s+(TBClasses[\w.]*|CocoTBFramework[\w.]*)", re.M)
FILELIST_RE = re.compile(r"['\"]([^'\"]*filelists/[^'\"]+\.f)['\"]")
MODULE_HDR_RE = re.compile(r"^module\b.*?^\s*\);", re.M | re.S)

GOLDEN_BANNER = """
# ============================================================================
# GOLDEN FRAMEWORK -- independently reviewed ground truth, NOT a review
# target. Present so claims about framework usage can be checked (BFM names,
# factory methods, scoreboard APIs). Do NOT file findings on these files;
# the framework is reviewed in its own repo, and this local clone is a
# convenience download (read-only).
# ============================================================================
"""


def resolve(mod):
    """'TBClasses.a.b' -> repo path; 'CocoTBFramework.a.b' -> DV path."""
    parts = mod.split(".")
    if parts[0] == "TBClasses":
        p = os.path.join(REPO, "bin", "TBClasses", *parts[1:]) + ".py"
    else:
        p = os.path.join(DV, "src", "CocoTBFramework", *parts[1:]) + ".py"
    return p if os.path.exists(p) else None


def chain(roots, want):
    """Transitive import closure over the given namespaces."""
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


def cat(paths, banner_comment):
    out = []
    for p in paths:
        rel = os.path.relpath(p, REPO) if p.startswith(REPO) else p
        out.append(f"\n{banner_comment} {'=' * 60}\n{banner_comment} FILE: {rel}\n"
                   f"{banner_comment} {'=' * 60}\n")
        out.append(open(p, encoding="utf-8", errors="replace").read())
    return "".join(out)


def rtl_ifaces(filelists):
    ifaces, seen = [], set()
    for fl in filelists:
        fl_path = os.path.join(REPO, fl)
        if not os.path.exists(fl_path):
            continue
        for line in open(fl_path, encoding="utf-8", errors="replace"):
            line = line.strip()
            if not line or line.startswith(("//", "#", "-", "+")):
                continue
            src = os.path.normpath(os.path.join(REPO, line))
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
    area = sys.argv[1]
    out_root = sys.argv[2] if len(sys.argv) > 2 else os.path.expanduser("~/rtl-test-review")
    tests = sorted(
        os.path.join(REPO, "val", area, f)
        for f in os.listdir(os.path.join(REPO, "val", area))
        if re.match(r"test_.*\.py$", f)
    )
    if not tests:
        sys.exit(f"no test_*.py under val/{area}")

    entries = []  # (rel, tp, tbc, fwc, fls)
    units, cur, cur_size = [], [], 0
    for tp in tests:
        text = open(tp, encoding="utf-8", errors="replace").read()
        mods = IMPORT_RE.findall(text)
        tb0 = [r for m in mods if m.startswith("TBClasses") if (r := resolve(m))]
        fw0 = [r for m in mods if m.startswith("CocoTBFramework") if (r := resolve(m))]
        tbc = chain(tb0, "TBClasses")
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
        blob = cat([tp], "#") + cat(tbc, "#") + cat(fwc, "#") + rtl_ifaces(fls)
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
        mlines = ["# Test-review manifest -- val/" + area, ""]
        for rel, _tp, tbc, fwc, fls in unit:
            mlines.append(f"- `{rel}`")
            mlines.append(f"  - TB: {', '.join(os.path.relpath(p, REPO) for p in tbc) or '(inline/none)'}")
            mlines.append(f"  - FW: {', '.join(os.path.basename(p) for p in fwc) or '(none)'}")
            mlines.append(f"  - filelist: {', '.join(fls) or '(NONE FOUND)'}")
        write_part(d, "\n".join(mlines) + "\n",
                   cat([t[1] for t in unit], "#"),
                   cat(sorted({p for t in unit for p in t[2]}), "#"),
                   cat(sorted({p for t in unit for p in t[3]}), "#"),
                   rtl_ifaces(sorted({f for t in unit for f in t[4]})))
        print(f"{d}: {len(unit)} tests")

    print(f"\n{len(tests)} tests -> {len(units)} unit(s) under {out_root}/{area}")


if __name__ == "__main__":
    main()
