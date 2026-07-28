#!/usr/bin/env python3
"""Append GOLDEN dependency sources to a unit's RTL.sv after a bundle rebuild.

The bundler's dependency closure follows INSTANTIATIONS in the area's RTL.
Modules the DOCS tell the reader to instantiate themselves (reset_sync and
friends) are never reached, so the reviewer cannot check doc examples against
them and files "unverifiable" findings -- or the verifier REFUTES a real
finding for lack of evidence (reset_sync, reset-corpus cdc round_2).

This scans the unit's DOCS.md for `<name>.sv` references, resolves each to
its RTL source, and appends any not already in the unit's RTL.sv under a
GOLDEN banner: independently reviewed ground truth, present as evidence for
claims the docs make ABOUT them, never a finding target themselves (Sean's
rule, 2026-07-28: a reset_sync-class primitive appears in ASICs everywhere;
treat it as reviewed).

Run after every bundle rebuild, before sending a round, on the book's PARTS
(never on a `<area>_meta` unit -- a meta unit's RTL.sv is deliberately a
module inventory, not source):

    python3 bin/review/augment_golden_deps.py ~/rtl-doc-review/books/cdc/parts/part_01 \\
                                            ~/rtl-doc-review/books/cdc/parts/part_02
"""
import glob
import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

BANNER = """
// ============================================================================
// GOLDEN DEPENDENCIES -- independently reviewed ground truth, NOT review
// targets. These modules are referenced by this unit's docs but not
// instantiated by its RTL, so the bundle's dependency closure missed them.
// Use them ONLY to verify claims the docs make about them (interfaces,
// parameter names, behaviour). Do NOT file findings on these modules
// themselves; they are reviewed elsewhere / come from golden sources.
// ============================================================================
"""


def sv_index():
    idx = {}
    for p in glob.glob(os.path.join(REPO, "rtl", "**", "*.sv"), recursive=True):
        stem = os.path.basename(p)[:-3]
        idx.setdefault(stem, p)
    return idx


def collect_refs(doctext, idx):
    # module refs appear as `name.sv`, as bare backticked `name`, and as
    # instantiations in doc examples (reset_sync #(...) u_inst (). Keep only
    # what resolves to an actual RTL file.
    return sorted((set(re.findall(r"\b([a-z_][a-z0-9_]{2,})\.sv\b", doctext)) |
                   set(re.findall(r"`([a-z_][a-z0-9_]{2,})`", doctext)) |
                   set(re.findall(r"^\s{0,8}([a-z_][a-z0-9_]{2,})\s*(?:#\s*\(|[A-Za-z_]\w*\s*\()",
                                  doctext, re.M)))
                  & set(idx.keys()))


def augment(unit, refs, idx):
    docs = os.path.join(unit, "DOCS.md")
    rtl = os.path.join(unit, "RTL.sv")
    if not os.path.exists(docs) or not os.path.exists(rtl):
        print(f"skip {unit} (no DOCS.md/RTL.sv)")
        return
    body = open(rtl, encoding="utf-8", errors="replace").read()
    if "GOLDEN DEPENDENCIES" in body:
        body = body[:body.index("\n// " + "=" * 76 + "\n// GOLDEN DEPENDENCIES")]
    present = set(re.findall(r"^module\s+(\w+)", body, re.M))
    added = []
    chunks = []
    for stem in refs:
        if stem in present or stem not in idx:
            continue
        src = os.path.relpath(idx[stem], REPO)
        chunks.append(f"\n// ---- GOLDEN: {src} ----\n")
        chunks.append(open(idx[stem], encoding="utf-8", errors="replace").read())
        added.append(src)
    if not added:
        print(f"{os.path.basename(unit):20s}  closure already complete")
        return
    # Re-augmenting an already-augmented unit must REPLACE the old golden
    # section, not append a second one (the strip above only truncated the
    # in-memory body; write it back, don't append to the file).
    with open(rtl, "w") as f:
        f.write(body + BANNER + "".join(chunks))
    print(f"{os.path.basename(unit):20s}  +{len(added)} golden: "
          + ", ".join(os.path.basename(a) for a in added))


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    idx = sv_index()
    # Refs are the UNION across all units given: a finding in part_02 may turn
    # on a module only part_01's docs name explicitly (round_3's "twice (APB,
    # ...)" finding needed apb_slave_cdc_cg.sv, absent from part_02's bundle).
    refs = []
    for unit in sys.argv[1:]:
        docs = os.path.join(unit, "DOCS.md")
        if os.path.exists(docs):
            refs += collect_refs(open(docs, encoding="utf-8", errors="replace").read(), idx)
    refs = sorted(set(refs))
    for unit in sys.argv[1:]:
        augment(unit, refs, idx)


if __name__ == "__main__":
    main()
