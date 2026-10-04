# andesite DDR4/LPDDR4 RTL bootstrap — design spec

**Date:** 2026-10-04
**Status:** brainstormed with the owner; approved to write the spec; awaits
owner spec review before the implementation plan
**Deliverable of this track:** working andesite RTL — `andesite_pkg`, the
FUB inventory, macros and top — verified model-first against the DFI 4.0
BFM, with the house gates green and the books re-cited at RTL lines.
**Design authority:** the andesite HAS v0.1 and MAS v0.1
(`projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/`). This spec
owns sequencing, toolchain, and gates only; where it and the books disagree,
the books win and this spec is corrected.

## 1. Goal and success criteria

Success looks like scoria's shape, one generation later:

- The complete planned inventory elaborates: `andesite_pkg`, 26 FUB files
  (12 carried unchanged from scoria, 11 modified, 3 new), the macro tier
  (`andesite_axi4_ifc`, `andesite_mem_cmd_scheduler`, `andesite_dfi_layer`,
  `andesite_csr.rdl` when it lands), and `andesite_top` /
  `andesite_top_geared`.
- Every FUB carries a model-first DV suite (Python golden, red→green) in
  `dv/`, mirroring scoria's apparatus.
- The top tier drives the DFI 4.0 BFM slave (RTLDesignSherpa-DV,
  `DFIVersion.V4_0`) through DDR4 init, training protocols, and demand
  traffic at the design point (DDR4-1600 x8; LPDDR4-1600 x16 breadth after
  the DDR4 path is green).
- Lint clean (Verilator + Verible, scoria's configuration as the template),
  `check_task_ids.py` green, and the kmap workbook's citations re-pointed
  from MAS lines to `.sv:line` so the derived-vs-RTL SOP verdicts turn real.

## 2. Scope decisions (owner answers, 2026-10-04)

| Question | Decision |
|---|---|
| Bootstrap shape | **Vertical slice first, then breadth.** P0 infra → P1 DDR4 init slice against the BFM → P2 unchanged FUBs → P3 modified/new FUBs → P4 macros/top/full sims. Each phase gates the next. |
| PHY boundary | DFI 4.0, per the books. The BFM's v4_0 behavior (incl. gear-down, CA-VREF, per-slice leveling) is the counterparty; gaps G1-G5 are closed (DV commit 61a27d8fee3b). |
| Design point | DDR4-1600 x8, 4 bank groups × 4 banks (MT40A1G8-class); LPDDR4-1600 x16, 8 banks per channel. Timings are runtime CSRs initialised from the BFM's jedec/ddr4-1600.csv. |
| DV method | Model-first, per FUB, red→green. Top tier against the BFM slave; DRAMsim3 as the cycle-accurate cross-check (HAS ch06 counterparties). |

## 3. Phase plan

**P0 — infrastructure (the de-risk).** `andesite_pkg`: the family memtype
enum taken from family doc 01 (3 bits, LP + generation), the carried 4-bit
`OP_*` set plus `OP_MPC`, the shared types the family doc names. Directory
and filelist scaffolding (`rtl/{fub,macro,top,includes,filelists}`, `dv/`
with tb/test layout mirroring scoria), the rtl/Makefile lint/test entry
points copied from scoria's flow, one trivial module through the whole
pipeline to prove it. Gate: lint and a smoke test green on the scaffolding.

**P1 — the init slice (the proof).** `init_sequencer`, `mode_register`, and
`dfi_cmd_formatter` built to the MAS pages, driven by a minimal init-only
command source (a testbench harness, not a product block) at the BFM slave.
First red→green test: the HAS ch06 item-1 init-order checker — RESET#
window, CKE discipline, the MR3-MR6-MR5-MR4-MR2-MR1-MR0 order, ZQCL close,
tDLLK/tZQinit wait — with timing values from the 1600 CSV. Gate: the BFM
walks init at the design point and the checker is green; gear-down entry
(BFM G3 support) exercised as a second configuration.

**P2 — the unchanged twelve.** The 12 inherited FUBs carried from scoria
with their model-first suites: `bank_timer`/`bank_timers`, `page_policy`,
`rd_cmd_cam`, `wr_data_cam`, `rd_intake`, `wr_intake`, `wr_splitter`,
`rd_return_ring`, `axi_burst_chopper`, `dfi_cdc`, `cmd_history_checker`
(growing DDR4's long/short spacing set per the MAS), and the dormant pair
`powerdown_ctrl`/`dfi_signal_pack` (carried uninstantiated, on the record).
Gate: each suite green; the inherited next-state fix in `global_timers` is
noted for P3 (it arrives with the modified set).

**P3 — the modified and new.** Dependency order: `addr_mapper` and
`global_timers` (the L/S pairs) → `cmd_arbiter`/`mem_cmd_scheduler`
(bank-group-aware admission) → `refresh_ctrl` (FGR on the inherited base;
per-bank for LPDDR4 deferred to the LPDDR4 breadth task) → `zq_ctrl` + MPC
submodule → `odt_ctrl` → training trio (`wrlvl_ifc` carried contract,
`rdlvl_ifc`, `ca_train_ifc`; firmware-search stubs only) → `dfi_cmd_path`,
`dfi_rd_aligner`, `dfi_wr_serializer` (DBI on `dfi_wrdata_mask` per the
TASK-005 study), `dfi_layer`. The parity/alert recovery sub-FSM (TASK-006)
rides in the sequencer here. Gate: per-FUB suites green; scheduler spacing
checks (`cmd_history_checker` + the timers) red→green against the kmap
qualifier SOPs.

**P4 — macros, top, full sims.** `andesite_axi4_ifc`, the scheduler macro,
`dfi_layer` integration, `andesite_core`, width-gearing wrapper, `top`.
Full-datapath BFM sims: demand traffic, refresh/ZQ interleave, training
protocols, ODT schedule observability. `formal/andesite/` opens with the
spacing properties (tCCD_L/S first — the family's formal home, no
assertions in RTL). Gate: top tier AXI-in/DFI-out with data through the
whole path; the books' revision histories record the reconciliation.

## 4. Toolchain and conventions

- **Lint/sim:** Verilator + Verible with scoria's configuration as the
  template; the rtl/Makefile entry points mirror scoria's.
- **CSR flow:** PeakRDL, when `andesite_csr.rdl` lands (P3/P4 boundary);
  registers name-based in books, offsets generated. No CSR map in prose.
- **BFM integration:** RTLDesignSherpa-DV, `DFIVersion.V4_0`; jedec
  timings from `ddr4-1600.csv`; DRAMsim3 cross-check wired at P4.
- **Naming/clocking:** `andesite_` prefix; `clk`/`rst_n` in the component
  tree (the `aclk`/`aresetn` convention rides at the AXI boundary per
  family doc 02); `r_`/`w_` internal prefixes; no assertions in RTL.
- **Citation migration:** when each FUB lands, the kmap generator's CITES
  for its MAS anchors are re-pointed at the `.sv:line` that implements the
  expression (the pre-RTL posture the generator already documents). The
  generator's gate then diffs `rtl_sop` against the derived covers — the
  verdicts turn from NOT CHECKED to real.

## 5. Deferred (named, not lost)

Per the books' deferred lists, unchanged here: write CRC, LPDDR4 DVFS/DSM,
the DARP family (TASK-001 model-only set), PB-REF (HAS ch06 Q7's named
condition), gear-down as an operating mode (built and protocol-checked at
P1, not the default), and the **LPDDR4 breadth** — the CA path, per-bank
refresh scheduling, MPC calibration, and inline-CKE behavior land as a
bounded follow-on track once the DDR4 path is green (its own plan addendum,
not scope creep here).

## 6. Out of scope

Board targets (none exist for DDR4 on 7-series); the `mem_ctrl_pkg` family
migration (family doc 01's conditions — deferred by design); basalt/DDR5.

## 7. Risks

- **BFM co-evolution:** andesite is the first v4_0 consumer; BFM bugs will
  masquerade as RTL bugs. Mitigation: protocol disputes get resolved
  against the spec PDF, and BFM fixes land as DV-repo commits, never as
  test loosening.
- **The `dfi_wrdata_mask` DBI sharing** (TASK-005 study): mask and DBI
  share a pin group; the write-path mux must arbitrate the two modes
  exactly as §3.2.1 describes. The P3 datapath tests pin this.
- **Timing-value provenance:** the 1600 CSV seeds CSR resets; JESD79-4D
  remains the authority (cold storage), and the HAS Q1 note closes when the
  CSR derivation is written.
