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

## DDR2 / LPDDR2 Family Controller Hardware Architecture Specification

**Document Number:** DDR2-LPDDR2-HAS-001
**Version:** 0.7
**Status:** Draft - reconciled with rearchitected RTL
**Classification:** Open Source - MIT License

---

## Document Purpose

This Hardware Architecture Specification (HAS) provides a high-level architectural overview of the DDR2 / LPDDR2 unified memory controller family. It describes the system-level design, external interfaces, characterization parameters, and integration requirements without detailing internal implementation specifics.

**Target Audience:**

- System architects evaluating the controller for SoC integration
- Hardware engineers planning RTL implementation
- Verification engineers planning system-level testing
- Software engineers developing low-level memory configuration

**Companion Documents:**

- DDR2/LPDDR2 Family Controller Pre-Architecture Spec (`../pre-aspec.md`) — bullet-form architecture rationale
- DDR2/LPDDR2 Paging and Refresh Notes (`../paging-refresh-notes.md`) — research-derived parameter sources

---

## Revision History

| Version | Date       | Author       | Notes                                                            |
|---------|------------|--------------|------------------------------------------------------------------|
| 0.1     | 2026-06-13 | RTL Design Sherpa | First sketch — module decomposition                         |
| 0.2     | 2026-06-14 | RTL Design Sherpa | Top-level interface port list (§2.4), FUB SWAG (§2.5), family-wide config-bit registry (§5.4), multi-rank support across §2 / §3.3 / §3.4 / §3.6 / §5.2 / §6.3 |
| 0.3     | 2026-07-07 | RTL Design Sherpa | Narrow-device (x16) support: distinguish DRAM beat vs physical device word (`DRAM_DEVICE_WIDTH`); device-word column granularity + burst-length scaling; `DFI_PHASE` (rd/wr phase) CSR. Fixes on-silicon DDR2 read failure (Nexys A7 x16 bring-up). |
| 0.4     | 2026-07-12 | RTL Design Sherpa | Full reconciliation with the rearchitected RTL: three-layer core (`pumice_axi4_ifc` / `pumice_mem_cmd_scheduler` / `pumice_dfi_layer`); FSM-free `bank_timer`; de-FSM'd CAMs; single `ADDR_MAP.bank_lsb` address knob (scheme selector retired); fully-functional LPDDR2 (bit-exact JESD209-2F CA + JEDEC MR init); host-width `pumice_top_geared` gearing; block/hierarchy diagrams regenerated. |
| 0.5     | 2026-09-xx | RTL Design Sherpa | (No revision-history row was recorded when v0.5 was cut; its content is whatever the 2026-07-22 build captured. Noted rather than reconstructed.) |
| 0.6     | 2026-09-26 | RTL Design Sherpa | Paging modes 6/7 (`rbl_static`/`rbl_dyn`) RETIRED and the `pumice_rbl_table` FUB removed — measured on silicon on a workload built to suit them, the mechanism worked (thrash 100% -> 57.8%) and still lost: mode 6 -26% bandwidth, mode 7 bit-identical to plain open page. `PAGE_RBL_CFG` @ 0x07C left a documented HOLE, not reused. Newly documented: the bank timers' advisory lookahead (`safe_*_la_o`), the arbiter's in-flight shadow and FINAL-STAGE timing authority, and the TASK-006 stall counters + `REF_STATS_REF_BUSY`, none of which appeared in any prior revision. |
| 0.7     | 2026-09-26 | RTL Design Sherpa | **Page-policy characterization; the default change is RECOMMENDED but BLOCKED (BUG-003).** Mode 3 (`fixed_open`) with `tr_init = 2` measured strictly dominant over open page on the board at txn_scale=1000: +41.2% `col_major_interleaved_bl4`, +8.6..11.6% `col_major`, exactly flat on `incremental`/`row_major`, no scenario regressing, zero integrity failures. The RDL resets were changed to mode 3 / TR=2 and REVERTED the same day: the component gate caught a read-return-ring assertion ("DFI return beat with NO ticket in flight") at `rd_gap >= 8`, proven by controlled A/B to be caused by the new reset -- a short timeout fires inside a read's DFI return latency and precharges under an in-flight read (BUG-003, P1). The mechanism finding stands regardless: auto-precharge costs 4.9x the activations and 2x the read latency on identical traffic (160,006 vs 32,400 ACT) because it is uncancellable, whereas a background precharge gated on bank idle is implicitly cancellable. Mode 4 (`adapt_time`) documented as SUBSUMED by mode 3 -- its TR decays to `tr_min` and it equals `fixed_open(tr_min)` exactly at three different floors -- and `policy_scope=0`'s "per-bank TR" documented as a fiction (`r_mc` is one global counter). Mode 5 (`adapt_access`) documented as unproven and mis-plumbed. Two CSR traps now documented: `tr_init = 0` DISABLES the timeout, and `PAGE_ADAPT_CFG.check_interval = 0` gates the entire mode-4 adjustment off -- which is why mode 4 measured inert on every campaign before this one. |

---

## Scope of This Document

This HAS describes a single parameterized memory controller covering DDR2 and LPDDR2. It defines:

- External interfaces (AXI4 slave, DFI v2.1 master, APB CSR slave)
- Module-level decomposition and behavioral specification
- Build-time and run-time configuration parameters
- Initialization, power-state, and refresh policies
- Verification strategy and characterization plan

It does not define:

- Bit-level pin assignments (the SystemVerilog port list in `rtl/top/pumice_top.sv` is the canonical wire-level source)
- Detailed timing diagrams (deferred to v0.3)
- Verilog package skeletons or RTL stubs
- Floorplan or layout guidance

---

## Out of Scope

The following features are explicitly out of scope for this version of the controller and will be addressed in higher-generation family controllers or future revisions:

- Inline ECC
- DFI training, frequency-change, and low-power sub-interfaces
- AXI exclusive access semantics
- Bank groups (not present in DDR2 / LPDDR2)
- Command/Address parity, CRC, Data Bus Inversion (not present in DDR2 / LPDDR2)
