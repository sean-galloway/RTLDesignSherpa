#!/usr/bin/env python3
"""Convert val/math tests from hand-listed verilog_sources to filelists (MATH-003).

Per test: find `dut_name = "math_X"`, verify rtl/math/filelists/<dut_name>.f
exists, then:
  1. replace the `verilog_sources = [ ... ]` array with
     `verilog_sources, includes = get_sources_from_filelist(
         repo_root=repo_root, filelist_path='rtl/math/filelists/<dut>.f')`
  2. replace `includes=[]` with `includes=includes` in the run() call
  3. add the filelist_utils import if absent

Usage: convert_math_tests_to_filelists.py <file> [<file> ...]  (rewrites in place,
prints what it changed; skips with a reason when the shape is unfamiliar)
"""
import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

DUT_RE = re.compile(r'^\s*dut_name\s*=\s*["\'](math_\w+)["\']', re.M)
SOURCES_RE = re.compile(r"^\s*verilog_sources\s*=\s*\[\n(?:.*\n)*?\s*\]\n", re.M)
IMPORT_LINE = "from TBClasses.shared.filelist_utils import get_sources_from_filelist\n"


def convert(path):
    text = open(path).read()
    m = DUT_RE.search(text)
    if not m:
        return "skip (no dut_name match)"
    dut = m.group(1)
    fl = f"rtl/math/filelists/{dut}.f"
    if not os.path.exists(os.path.join(REPO, fl)):
        return f"skip (no {fl})"
    sm = SOURCES_RE.search(text)
    if not sm:
        return "skip (no verilog_sources array)"
    indent = re.match(r"\s*", text[sm.start():]).group(0)
    new_sources = (f"{indent}verilog_sources, includes = get_sources_from_filelist(\n"
                   f"{indent}    repo_root=repo_root,\n"
                   f"{indent}    filelist_path='{fl}'\n"
                   f"{indent})\n")
    text = text[:sm.start()] + new_sources + text[sm.end():]
    if "includes=[]" in text:
        text = text.replace("includes=[]", "includes=includes")
    elif "includes=includes" not in text:
        return "skip (includes already custom?)"
    if "get_sources_from_filelist" not in text.split("verilog_sources")[0]:
        # add import after the last TBClasses import, or after utilities import
        lines = text.split("\n")
        for i, line in enumerate(lines):
            if line.startswith("from TBClasses.shared.utilities import"):
                lines.insert(i + 1, IMPORT_LINE.rstrip())
                break
        else:
            for i, line in enumerate(lines):
                if line.startswith("from TBClasses"):
                    last = i
            lines.insert(last + 1, IMPORT_LINE.rstrip())
        text = "\n".join(lines)
    open(path, "w").write(text)
    return f"converted -> {fl}"


def main():
    for path in sys.argv[1:]:
        print(f"{os.path.basename(path):50s} {convert(path)}")


if __name__ == "__main__":
    main()
