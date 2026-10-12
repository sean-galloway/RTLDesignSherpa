# DELTA-001: axis flavor richness — optional TSTRB + AMBA 5 sidebands

**Status:** CLOSED 2026-10-12. Owner asked whether delta supports the AXIS
flavors in `rtl/amba/axis4` + `rtl/amba/axis5`; answer was no (base 7-signal
set only), and the directive followed: "please fill out the richness of
delta."
**Priority:** P3
**Filed from:** owner review of delta vs. rtl/amba/axis* flavors.

## What changed

`bin/delta_generator.py` gained two default-off options:

- `--strb-width N` — emits `TSTRB` on every master/slave port
  (`parameter int STRB_WIDTH`), byte qualifiers routed with the data mux.
- `--amba5` — emits AMBA 5 sidebands: `TWAKEUP` (TDEST-decoded OR per slave;
  may assert before TVALID per the AMBA 5 hint semantics — no grant needed)
  and `TPARITY` (`--parity-width` override, default `DATA_WIDTH/8`).

With both off the generated RTL is **byte-identical** to pre-change output
(verified: old vs. new generator, same config, `diff` clean). With options on,
generated ports match the repo's `axis4_*` / `axis5_*` signal sets.

## Verification

- Default-config regression: byte-identical output vs. the pre-change
  generator (2×4 config).
- Rich variant (`--data-width 32 --strb-width 4 --amba5`): verilator
  `--lint-only` rc=0.
- CLI guards: `--parity-width` without `--amba5` errors.
- Checked-in example: `rtl_test/delta_axis_flat_2x4_strb_amba5.sv`.
- Docs: PRD REQ-GEN-003/004, README feature bullet, CLAUDE.md (map +
  behavior + tasks), QUICK_START flavor note.

## Known pre-existing drift (NOT caused by this item)

The checked-in reference RTL (`rtl/delta_axis_flat_4x16.sv`,
`rtl_test/delta_axis_flat_{2x4,3x8,2x16}.sv`) does **not** byte-match current
generator output: checked-in files carry the house file header +
`reset_defs.svh` + `` `ALWAYS_FF_RST ``/`` `RST_ASSERTED `` macros, while the
framework generator today emits none of those (and its per-file header lines
are inconsistent, e.g. the 4x16 file's mangled Documentation path). A
regenerate-with-current-generator pass (or a framework header/macro upgrade)
is its own decision — do not silently regenerate the checked-in artifacts.
