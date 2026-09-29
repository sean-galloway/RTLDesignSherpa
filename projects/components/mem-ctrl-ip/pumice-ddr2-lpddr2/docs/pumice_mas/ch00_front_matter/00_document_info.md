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

## DDR2 / LPDDR2 Family Controller Micro-Architecture Specification

**Document Number:** DDR2-LPDDR2-MAS-001
**Version:** 0.7
**Status:** Draft - reconciled with rearchitected RTL
**Classification:** Open Source - MIT License

---

## Document Purpose

This Micro-Architecture Specification (MAS) is the implementation-level companion to the DDR2 / LPDDR2 Hardware Architecture Specification (HAS). Where the HAS answers "what is the architecture and why," this MAS answers "what is in the RTL and how does it work."

The MAS is the document RTL designers, verification engineers, and integrators consult when writing or reviewing SystemVerilog code, building testbenches, and stitching the controller into an SoC.

**Target Audience:**

- RTL designers implementing the FUBs described in this document
- Verification engineers writing per-FUB cocotb tests
- Integrators stitching the controller into an SoC
- Software engineers writing low-level memory configuration code (driver authors, bring-up engineers)

**Companion Documents:**

- DDR2/LPDDR2 Family Controller HAS (`../pumice_has/`) — high-level architecture and design rationale
- DDR2/LPDDR2 DFI BFM documentation (in `RTLDesignSherpa-DV`) — verification-side reference

---

## Document Scope

The MAS is the **micro-architecture** view: per-FUB inputs/outputs, internal state, FSM diagrams, datapath timing, register-level pipeline stages, and per-block timing budgets. It assumes the reader has read the HAS for context.

This document covers:

- Top-level integration wiring (`pumice_ctrl`)
- Each FUB's interface signal list, internal storage, datapath flow, FSM, and timing budget
- AXI4 and DFI v2.1 wire-level protocol details specific to this controller
- APB programming interface and the full CSR register map
- Programming sequences (init, refresh, power-down, multi-rank, error handling)
- Build-time and runtime configuration reference

This document does **not** cover:

- Higher-level architectural rationale (see HAS)
- Verification plans or coverage models (see the YAML testplans in `dv/testplans/`)
- Floorplan or layout guidance (project-specific)
- Bit-level CSR definitions — the PeakRDL source `rtl/macro/pumice_csr.rdl` is the source of truth for CSR generation (generated collateral in `regs/generated/`)

---

## Revision History

| Version | Date       | Author       | Notes                                                            |
|---------|------------|--------------|------------------------------------------------------------------|
| 0.1     | 2026-06-14 | RTL Design Sherpa | Initial skeleton — chapter outline, FUB list, port list scaffold |
| 0.2     | 2026-07-07 | RTL Design Sherpa | Narrow-device (x16) support: `DRAM_DEVICE_WIDTH` param; burst-length scaling to device-word units (§15); `addr_mapper` column granularity = device word via `BYTE_OFFSET_WIDTH` (§3); `DFI_PHASE` CSR (rd_phase/wr_phase). Fixes the on-silicon DDR2 read failure (Nexys A7 x16). |
| 0.3     | 2026-07-07 | RTL Design Sherpa | §20 mode_register: document burst length as a fixed-per-instance init constant, decoded (not hardcoded) so the same RTL retargets DDR2 BL4 / DDR3-DDR4 BL8; BC4/burst-chop declared out of scope (always issue full BL). |
| 0.4     | 2026-07-12 | RTL Design Sherpa | Full reconciliation with the rearchitected RTL. ch02 block chapters rewritten to the live FUBs: retired txn_queue/bank_machine/xbank_timers/cmd_encoder/odt_ctrl/standalone page_predictor -> CAMs / FSM-free bank_timer / global_timers / dfi_cmd_formatter / arbiter inline open-page. `addr_mapper` = single `ADDR_MAP.bank_lsb` knob (scheme mux retired). LPDDR2 fully functional (bit-exact JESD209-2F CA + JEDEC MR init). `pumice_top_geared` host-width gearing. CSR map reconciled to the RDL. All block diagrams regenerated. |
| 0.5     | 2026-09-xx | RTL Design Sherpa | (No revision-history row was recorded when v0.5 was cut; its content is whatever the 2026-07-22 build captured. Noted rather than reconstructed.) |
| 0.6     | 2026-09-26 | RTL Design Sherpa | Paging modes 6/7 (`rbl_static`/`rbl_dyn`) RETIRED and the `pumice_rbl_table` FUB removed — measured on silicon on a workload built to suit them, the mechanism worked (thrash 100% -> 57.8%) and still lost: mode 6 -26% bandwidth, mode 7 bit-identical to plain open page. `PAGE_RBL_CFG` @ 0x07C left a documented HOLE, not reused. Newly documented: the bank timers' advisory lookahead (`safe_*_la_o`), the arbiter's in-flight shadow and FINAL-STAGE timing authority, and the TASK-006 stall counters + `REF_STATS_REF_BUSY`, none of which appeared in any prior revision. |
| 0.7     | 2026-09-26 | RTL Design Sherpa | **Page-policy characterization; the default change is RECOMMENDED but BLOCKED (BUG-003).** Mode 3 (`fixed_open`) with `tr_init = 2` measured strictly dominant over open page on the board at txn_scale=1000: +41.2% `col_major_interleaved_bl4`, +8.6..11.6% `col_major`, exactly flat on `incremental`/`row_major`, no scenario regressing, zero integrity failures. The RDL resets were changed to mode 3 / TR=2 and REVERTED the same day: the component gate caught a read-return-ring assertion ("DFI return beat with NO ticket in flight") at `rd_gap >= 8`, proven by controlled A/B to be caused by the new reset -- a short timeout fires inside a read's DFI return latency and precharges under an in-flight read (BUG-003, P1). The mechanism finding stands regardless: auto-precharge costs 4.9x the activations and 2x the read latency on identical traffic (160,006 vs 32,400 ACT) because it is uncancellable, whereas a background precharge gated on bank idle is implicitly cancellable. Mode 4 (`adapt_time`) documented as SUBSUMED by mode 3 -- its TR decays to `tr_min` and it equals `fixed_open(tr_min)` exactly at three different floors -- and `policy_scope=0`'s "per-bank TR" documented as a fiction (`r_mc` is one global counter). Mode 5 (`adapt_access`) documented as unproven and mis-plumbed. Two CSR traps now documented: `tr_init = 0` DISABLES the timeout, and `PAGE_ADAPT_CFG.check_interval = 0` gates the entire mode-4 adjustment off -- which is why mode 4 measured inert on every campaign before this one. |
