<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Document Information

## andesite DDR4/LPDDR4 Family Controller Micro-Architecture Specification

| Property | Value |
|----------|-------|
| Document Title | andesite DDR4/LPDDR4 Family Controller Micro-Architecture Specification |
| Version | 0.5 (draft) |
| Date | October 5, 2026 |
| Status | v0.5 with the integration pass landed (2026-10-05): the scheduler macro carries the P1 rewiring, `dfi_cmd_path` exists, and the training/DFI/AXI4 layer assemblies plus `andesite_core` are built and suite-green (248 tests at the DFI 4.0 boundary). This book expands the owner-reviewed HAS's changed and new blocks to signal level. Every claim is inherited from a named scoria source, cited to JESD79-4 / JESD209-4 / DFI 4.0 with the `§TBC(TASK-005)` discipline, or recorded as an open question in the HAS ch06 |
| Classification | Open Source - MIT License |

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 0.5 | 2026-10-05 | RTL Design Sherpa | TASK-016 integration pass, signal level. Scheduler macro: P1 rewiring (DDR4-only init, `cmd_ack` = valid&&ready qualified on MRS/ZQCL, `zq_cal_start_o`, retired `dfi_init_*`/`t_*_wait_i`/`mr_wr_o` ports); command stream widened to `{ap,col,row,bg,bank,rank,op}` with `cmd_bg_o` (`CMD_W` grew by `$clog2(NUM_BG)`); the init request's duplicate-accept fix is a combinational gate on the accept cycle. `dfi_cmd_path` (new): A10 case-split address routing (RD/RDA/WR/WRA merge `ap<<10`, PREA forces A10, PRE clears, MRS/ZQCL keep the row-field payload). `andesite_training_layer` (new): the three carried training interfaces behind a maintenance command channel mirroring the init-source ack-pulse pattern. `andesite_dfi_layer` (new): CDC word packings `WD_DW={last,strb,dbi,data}` and `RD_DW={last,resp,dbi,data}` so write-DBI and read-DBI cross registered with their data; `dfi_init_complete_i` drives `pinit_complete_i`. `andesite_axi4_layer` (carried-modified): scoria rename-carry, byte-parity + logic-parity gates green. `andesite_core` (new top): four-layer wiring per the ch03 wiring table. Suites: fub 225, macro 19, core top 4 (248 total); master lint 53 modules; registry PASS. DV-framework drift recorded: the BFM behavior dispatch samples `cs_n`/error/init/update unconditionally — the init-slice TB carries `phy_dfi_cs_n` + idle handshake pins. |
| 0.1 | 2026-10-03 | RTL Design Sherpa | First draft, written before any RTL exists. Carries the HAS's changed/new blocks one level down: per-block interface tables, FSM policy, mechanism detail, and the contract anchors the generated kmap book cites. Inherited-unchanged blocks are referenced to scoria's books, not rewritten. |
| 0.4 | 2026-10-04 | RTL Design Sherpa | P3 gate: the modified/new tier is landed. 30 design files: 15 carried-inherited rename-only (13 active + the `powerdown_ctrl`/`dfi_signal_pack` dormant pair), 8 carried-modified (`addr_mapper` +bg, `global_timers` +L/S, `cmd_arbiter` +L/S admission, `refresh_ctrl` +FGR, `zq_ctrl` +MPC submodule, `mem_cmd_scheduler` carrying the FGR/MPC/recovery consumer paths, `dfi_wr_serializer`/`dfi_rd_aligner` +DBI), 4 new (`odt_ctrl`, `rdlvl_ifc`, `ca_train_ifc`, `zq_mpc_lpddr4`), and the 3 P1 blocks (`dfi_cmd_formatter`, `init_sequencer` +TASK-006 recovery FSM, `mode_register`). The marking-pair gate (HAS reuse table vs this book's What-Changes table) is GREEN at 23=23. The kmap CITES for the address-decode and MR-semantics fences now point at RTL anchor blocks in `addr_mapper`/`mode_register` (drift gate live, byte-identical reruns). `dfi_cmd_path` + `dfi_layer` remain per the plan: cmd_path rides the T9 integration pass; the layer is P4. The scheduler macro's init/mode_register rewiring and its macro-level suite land with that same pass. |
| 0.3 | 2026-10-04 | RTL Design Sherpa | P2 carry reconciliation: the inheritance table's ten active blocks exist as `andesite_*` with scoria's port lists (carry-diff gates prove rename/import/header-only deltas); `cmd_history_checker` carries the DDR4 L/S growth named on the scheduler page. The dormant pair exists uninstantiated. `rd_intake`/`wr_intake` land with P3's `addr_mapper` (they instantiate it). |
| 0.2 | 2026-10-04 | RTL Design Sherpa | P1 RTL reconciliation: Tables 2.2/2.2.2 (formatter, init_sequencer) and the mode_register interface now match the landed modules — v4.0 `dfi_cs` naming, 5-bit `op_i` carrying `OP_MPC`, 3-bit MR index on `cmd_bank`, 6-bit MR addresses, `csr_mrN_image` init payloads. Deferred ports (`dfi_alert_n`, `ca_o`/`ca_valid_o`) are recorded as follow-ons (TASK-006 / LPDDR4 breadth), not stubs. The kmap book's command-decode citations re-pointed at the RTL (drift gate live); per-command boolean SOP verdicts land with P3. |

## Document Purpose

This Micro-Architecture Specification (MAS) is the implementation-level view
of the andesite controller — the HAS (`../andesite_has/`) taken one level
down. It is the document an RTL author reads before writing SystemVerilog and
a verification engineer reads before writing checkers.

It covers:

- each changed or new block's interface, parameters, and internal mechanism
- the FSM policy for every block: where a state machine is required, where
  one is forbidden (no training search loops, per the D2 precedent), and what
  replaces FSMs elsewhere
- the DFI 4.0 pin-level table the HAS's interface chapter promises
- the core signal contracts whose anchors the generated kmap book
  (`../kmaps/`) verifies by citation

## Intended Audience

- RTL implementers writing the changed and new blocks
- Verification engineers building the DFI 4.0 BFM checks and the formal
  spacing properties the HAS ch06 names
- Architects confirming that a block-level decision matches the HAS's
  marking and cause

## Related Documents

| Document | Location | Content |
|---|---|---|
| Hardware Architecture Specification | `../andesite_has/andesite_has_index.md` | the owner-reviewed v0.1 architecture this document expands; bindings between the two follow the HAS |
| Bootstrap design spec | `../../../../../../docs/superpowers/specs/2026-10-03-andesite-bootstrap-design.md` | the tranche's scope decisions (§6 is this book's plan) |
| Family docs | `../../../../docs/` | shared-core design (`mem_ctrl_pkg`) and family doctrine |
| scoria HAS | `../../../scoria-ddr3-lpddr3/docs/scoria_has/` | the reuse pool; authoritative for inherited-unchanged blocks |
| scoria design requirements | `../../../scoria-ddr3-lpddr3/docs/design-requirements.md` | the delta-analysis method; TASK-001 mode detail (§6) |
| Kmap generator + workbook | `../kmaps/` | generated command-encoding tables citing this book's anchors |
| Family README | `../../../../../README.md` | family overview and per-IP status |

: Table 0.1: Related documents
