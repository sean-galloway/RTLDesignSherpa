# andesite DDR4/LPDDR4 kmap book

This directory holds the machine-generated kmap / signal-contract workbook for
the andesite memory controller MAS v0.1.

## What is generated

`gen_andesite_kmaps.py` writes, from scratch on every run:

* `andesite_cmd_kmaps.xlsx` -- one sheet per contract table / K-map
  1. `DDR4 command decode`
  2. `LPDDR4 CA commands`
  3. `Address decode maps`
  4. `MR0-MR6 programming maps`
  5. `ODT truth table`
  6. `FGR refresh select`
* `generated/01_ddr4_command_table.md`
* `generated/02_lpddr4_ca_command_table.md`
* `generated/03_addr_decode_maps.md`
* `generated/04_mr_programming_maps.md`
* `generated/05_odt_truth_table.md`
* `generated/06_fgr_refresh_map.md`

## How to rerun

From the repo root:

```
python3 projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/kmaps/gen_andesite_kmaps.py
```

The generator is idempotent: a second run with unchanged sources produces
byte-identical output.

## Never hand-edit the workbook

`andesite_cmd_kmaps.xlsx` is a build artifact. Edit the generator or the MAS
anchor pages, then rerun. Hand-edits are lost on the next run and break the
citation gate.

## Citation gate posture

At MAS v0.1 there is no RTL, so every sheet cites the MAS page where the
intended expression is written verbatim. The generator runs
`verify_citations()` first; if any cited `file:line` snippet drifts, the run
fails non-zero. When RTL lands, the citations are re-pointed at the
corresponding `.sv` file and line, and the gate then enforces agreement
between the workbook and the implementation.

## Per-table MAS anchor pointers

| Generated table | Defining MAS anchor |
|---|---|
| `01_ddr4_command_table.md` | `andesite_mas/ch02_blocks/01_cmd_formatter.md` Table 2.3 -- truth table fence |
| `02_lpddr4_ca_command_table.md` | `andesite_mas/ch02_blocks/01_cmd_formatter.md` Table 2.4 -- LPDDR4 CA placeholder fence |
| `03_addr_decode_maps.md` | `andesite_mas/ch02_blocks/04_addr_mapper.md` Figure 2.2 -- decode structure fence; `andesite_has/ch02_overview/04_design_point.md` Table 2.4 -- 4 bank groups x 4 banks |
| `04_mr_programming_maps.md` | `andesite_mas/ch02_blocks/03_mode_register.md` Table 2.7 -- DDR4 MR0-MR6 field semantics |
| `05_odt_truth_table.md` | `andesite_mas/ch02_blocks/08_odt_ctrl.md` -- policy-state fence |
| `06_fgr_refresh_map.md` | `andesite_mas/ch02_blocks/06_refresh_ctrl.md` -- FGR interval arithmetic fence |
