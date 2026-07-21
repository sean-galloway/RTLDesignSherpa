#!/usr/bin/env python3
"""Regenerate a formal/amba/<top>/Makefile with the correct RTL dependency
closure and a single-source-of-truth flatten recipe.

The AMBA monitor RTL was refactored (moved to rtl/amba/monitor/, the reporter
split into six axi_monitor_reporter_* sub-modules, and the trans CAM extracted
into monitor_trans_cam).  The hand-maintained DEPS lists in the formal Makefiles
drifted -- they were missing the new sub-modules, so yosys failed to elaborate.

This tool computes the transitive module closure of each formal top (leaves
first, via the same scan as dep_resolver) and rewrites the Makefile from a
canonical template.  The PKGS and INC blocks and the DUT path are preserved
verbatim from the existing Makefile; only the DEPS list and the flatten recipe
are regenerated.  The flatten recipe derives its sv2v file list from $(DEPS) via
$(addprefix ...) so the two can never drift again.

Usage:
    tools/gen_formal_deps.py <formal-dir> [<formal-dir> ...]
    tools/gen_formal_deps.py --all        # every formal/amba/*/Makefile
"""
import os, re, sys

REPO = os.popen("git rev-parse --show-toplevel").read().strip()
RTL = os.path.join(REPO, "rtl")

# ---- module -> file map + instantiation scan (shared with dep_resolver) ----
mod_file, mod_body = {}, {}
module_re = re.compile(r'^\s*module\s+([A-Za-z_]\w*)\b', re.M)
for root, _, files in os.walk(RTL):
    for f in files:
        if f.endswith((".sv", ".v")):
            path = os.path.join(root, f)
            try:
                txt = open(path, errors="replace").read()
            except Exception:
                continue
            txt = re.sub(r'//[^\n]*', '', txt)
            txt = re.sub(r'/\*.*?\*/', '', txt, flags=re.S)
            for m in module_re.finditer(txt):
                name = m.group(1)
                mod_file.setdefault(name, path)
                mod_body[name] = txt

KEYWORDS = {
    'if','else','case','for','while','begin','end','assign','always','always_ff',
    'always_comb','always_latch','initial','function','task','generate','endgenerate',
    'typedef','logic','wire','reg','input','output','inout','parameter','localparam',
    'module','endmodule','struct','enum','union','packed','signed','unsigned','return',
    'posedge','negedge','and','or','not','xor','assert','assume','cover','property',
}
inst_re = re.compile(r'^\s*([A-Za-z_]\w*)\s+(?:#\s*\(|[A-Za-z_]\w*\s*\()', re.M)

def instantiated(mod):
    out = set()
    for m in inst_re.finditer(mod_body.get(mod, "")):
        n = m.group(1)
        if n not in KEYWORDS and n != mod and n in mod_file:
            out.add(n)
    return out

def closure(top):
    seen, order = set(), []
    def visit(mod):
        for child in sorted(instantiated(mod)):
            if child not in seen:
                seen.add(child); visit(child); order.append(child)
    visit(top)
    return order  # leaves first, excludes top

# ---- Makefile field extraction ----
def extract_block(text, var):
    """Return the full RHS (joined, backslash-continued) of `VAR := ...`."""
    m = re.search(rf'^{var}\s*:=(.*?)(?<!\\)\n', text, re.M | re.S)
    return m.group(1) if m else None

def extract_raw_block(text, var):
    """Return the literal `VAR := ...` assignment lines (with continuations)."""
    m = re.search(rf'^({var}\s*:=.*?)(?<!\\)\n', text, re.M | re.S)
    return m.group(1) if m else None

TEMPLATE = """# SPDX-License-Identifier: MIT
# Formal verification Makefile for {name}
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog
#
# DEPS is the transitive module closure of {name} (leaves first), regenerated
# by tools/gen_formal_deps.py after the rtl/amba/monitor/ move, the reporter
# split (axi_monitor_reporter_*), and the monitor_trans_cam extraction.  The
# sv2v file list is derived from $(DEPS) so the two cannot drift.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := /mnt/data/tools/sv2v

{inc}

{pkgs}

{deps}

{dut}

TMPDIR := /tmp/formal_{name}

.PHONY: prove cover clean

prove: {name}_flat.v
\tsby -f {name}.sby prove

cover: {name}_flat.v
\tsby -f {name}.sby cover

# Strip `import monitor_pkg::*;` and `monitor_pkg::` scope prefixes (monitor_pkg
# re-exports sub-package types and trips sv2v "ambiguous identifier"), then
# flatten DUT + closure into a single Verilog file.
{name}_flat.v: $(DUT) $(PKGS) $(DEPS)
\t@mkdir -p $(TMPDIR)
\t@for f in $(DEPS) $(DUT); do \\
\t\tsed -e 's/import monitor_pkg::\\*;//g' \\
\t\t    -e 's/monitor_pkg:://g' $$f > $(TMPDIR)/$$(basename $$f); \\
\tdone
\t$(SV2V) --define=FORMAL --exclude=Assert $(INC) $(PKGS) \\
\t\t$(addprefix $(TMPDIR)/,$(notdir $(DEPS) $(DUT))) > $@
\t@rm -rf $(TMPDIR)

clean:
\trm -rf *_flat.v *_prove *_cover
"""

def build_deps(top):
    deps = closure(top)
    if not deps:
        return "# RTL dependencies (leaf module -- no submodule instantiations)\nDEPS :="
    lines = ["# RTL dependencies (transitive closure of %s, leaves first)" % top,
             "DEPS := " + " \\\n        ".join(
                 "$(REPO_ROOT)/" + os.path.relpath(mod_file[d], REPO) for d in deps)]
    return "\n".join(lines)

def regen(formal_dir):
    mk = os.path.join(formal_dir, "Makefile")
    text = open(mk).read()
    dut_raw = extract_raw_block(text, r'DUT')
    inc_raw = extract_raw_block(text, r'INC')
    pkgs_raw = extract_raw_block(text, r'PKGS')
    if not (dut_raw and inc_raw and pkgs_raw):
        print(f"  SKIP {formal_dir}: missing DUT/INC/PKGS", file=sys.stderr); return False
    dut_path = extract_block(text, r'DUT').strip()
    m = re.search(r'/([A-Za-z0-9_]+)\.sv', dut_path)
    top = m.group(1)
    if top not in mod_file:
        print(f"  SKIP {formal_dir}: unknown top {top}", file=sys.stderr); return False
    out = TEMPLATE.format(name=top, inc=inc_raw.rstrip(), pkgs=pkgs_raw.rstrip(),
                          deps=build_deps(top), dut=dut_raw.rstrip())
    open(mk, "w").write(out)
    n = len(closure(top))
    print(f"  {top:24s} {n:2d} deps -> {mk}")
    return True

if __name__ == "__main__":
    args = sys.argv[1:]
    if args == ["--all"]:
        base = os.path.join(REPO, "formal", "amba")
        args = [os.path.join(base, d) for d in sorted(os.listdir(base))
                if os.path.isfile(os.path.join(base, d, "Makefile"))]
    for d in args:
        regen(d)
