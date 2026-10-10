# mc_common_pkg — knob inventory (Phase 2, Task 1)

Measured 2026-10-09/10 from the three research pkgs. Binding design reference:
`common-ip/docs/01_mem_ctrl_pkg.md` (family doc 01, Table 1.0) — the family
memtype encoding and the migration conditions. Phase 2 IS the migration the
doc defers (condition: andesite RTL bring-up started — met).

## Move to `mc_common_pkg` (identical semantics across rocks)

| Item | Rock shapes | Family form in mc_common_pkg |
|---|---|---|
| `memtype_e` | pumice/scoria 1-bit {X, LPX}; andesite 3-bit family | andesite/doc-01 3-bit: bit[2]=LP axis, bits[1:0]=generation (2/3/4; 2'b11=gen5 reserved). 3'b011/3'b111 illegal, never alias. |
| `dram_op_e` | pumice/scoria 4-bit; andesite 5-bit | 5-bit superset = andesite's table. Values 0..F are IDENTICAL across all three rocks (verified table-by-table); `OP_MPC = 5'h10` added. |
| `bank_state_e` | identical 3-bit in all three | as-is |
| `page_policy_e` | identical 2-bit in all three | as-is (pumice's 2'h2 history comment rides along) |
| `decoded_addr_t` | identical packed struct (4/4/18/14) | as-is |
| `is_column_op`, `is_write_op`, `is_read_op`, `is_refresh_op`, `has_auto_pre`, `is_zq_op` | identical semantics; scoria/andesite write returns ONE LINE (yosys parses it; pumice's two-line is_column_op is why pumice formal must sv2v-flatten) | one-line form (scoria's), taking the family `dram_op_e` |

## Stays rock-specific

- `pumice_pkg`: `addr_map_scheme_e` (retired; only the old macro regression
  sentinels reference it), `odt_rule_e` (pumice-only ODT rule select).
- Anything timing-struct: doc 01 says LP-cal timing structs fold at migration
  "ratified against the structs; field layouts are migration-time work" — no
  rock pkg currently carries a shared timing struct, so there is nothing to
  move. Deferred by absence.

## Ruling: legacy CSR values are preserved (zero CSR-visible change)

`PHY_TIMING.memtype[16:16]` is a live rw CSR field with per-rock legacy
values (pumice: 0=DDR2/1=LPDDR2; scoria: 0=DDR3/1=LPDDR3 — note scoria's
DDR3=0 CONFLICTS with the family encoding where DDR3=3'b001). Widening the CSR
field to 3 bits is doc-01's migration plan, and it changes runtime-visible
values (scoria DDR3: 0→1; LP modes: 1→4/5) — board firmware and campaign
scripts write these values.

Decision: rocks keep the 1-bit CSR field and legacy values for Phase 2; each
rock maps legacy→family at the single hwif cast point
(`memtype_e'(hwif_out...)` in `<rock>_top.sv`, one site per rock) via a
per-rock mapping constant. The family `memtype_e` is used everywhere else
(build params, common layers). CSR widening is recorded here as a deliberate,
named deferral (doc 01 anticipates it; it is not required for layer
extraction, and the plan's zero-behavior-change constraint binds).

Cost if wrong: a later CSR-widening task re-touches the one cast site per
rock plus the RDL — small, localized, and already inventoried.

## Width-change consequences to expect during adoption (the RED steps)

- pumice/scoria signals declared `dram_op_e` re-width 4→5 transparently
  (typed); explicit `logic [3:0]` op wires and TB monitors sampling 4-bit op
  fields will fail lint/DV — fix sites until green, values unchanged.
- `memtype_e` re-widths 1→3 the same way; the hwif cast points get the
  legacy mapping (above).
- Verilator lint is strict about enum-width port connections; the suites are
  the pin.

## Deferral record (Task-2 relevant)

`dram_op_e` port typing on the nine mc_* FUBs: if pumice/scoria adoption
surfaces widespread explicit-width op wires that make the 5-bit family enum
impractical in this pass, the fallback is type-erased `logic [4:0]` op ports
with localparam op values on the FUBs — recorded here so Task 2's ruling gate
can cite it instead of re-deriving it.
