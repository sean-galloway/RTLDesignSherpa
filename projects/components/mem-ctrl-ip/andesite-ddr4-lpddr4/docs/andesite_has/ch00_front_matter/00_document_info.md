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

| Field | Value |
|-------|-------|
| Title | andesite DDR4/LPDDR4 Family Controller — Hardware Architecture Specification |
| Version | 0.1 |
| Date | 2026-10-03 |
| Status | First edition, written from the delta analysis against scoria before any andesite RTL exists. Every block is specified, not described; open questions are collected in Chapter 6 |
| Scope | Controller architecture to the DFI v4.0 boundary, for DDR4 and LPDDR4 |
| Not in scope | The PHY; board bring-up; the DDR5 features DFI v4.x also carries |

: Table 0.1: Document information

## Related documents

| Document | Where | Relationship |
|---|---|---|
| andesite bootstrap design spec | `../../../../../../docs/superpowers/specs/2026-10-03-andesite-bootstrap-design.md` | **binding foundation** — the scope decisions and settled filing |
| scoria HAS | `../../../scoria-ddr3-lpddr3/docs/scoria_has/` | the architecture andesite is derived from; the reuse pool |
| scoria design requirements | `../../../scoria-ddr3-lpddr3/docs/design-requirements.md` | its delta-analysis method and D1-D3 decisions apply here |
| family docs | `../../../../docs/` | shared-core design and doctrine — owned by no single controller (see Table 0.1 note) |
| JESD79-4 | outside the repo, cold storage | DDR4 device standard |
| JESD209-4 | outside the repo, cold storage | LPDDR4 device standard |
| DFI v4.0 | operator research storage `/mnt/data/github/dfi-specs/` (on disk 2026-10-04); study completed 2026-10-04 as andesite TASK-005 | the PHY boundary; clause citations are real DFI 4.0 section numbers; remaining `§TBC(TASK-005)` suffixes mark unconfirmed claims |

: Table 0.2: Related documents

## Terminology

**INHERITED / MODIFIED / NEW**
The marking every block in this document carries, relative to scoria.
*Inherited* means the scoria block is used as-is, and its correctness argument
transfers with it. *Modified* means a named, bounded change. *New* means no
scoria counterpart exists.

**nCK**
A DRAM clock cycle, the unit JESD79-4 states most command-spacing minimums in.

**Maintenance traffic**
Commands the controller must issue that no host requested — refresh and ZQ
calibration. It competes with demand traffic for the command bus, which makes
it a scheduling problem and not only a sequencing one.

**DFI 4.0 §TBC(TASK-005)**
Read "clause to be confirmed by andesite TASK-005 (DFI 4.0 spec acquisition
and BFM study)". The specification is now on disk and the study ran on
2026-10-04; remaining suffixes mark claims whose clause numbers could not be
confirmed, not claims whose substance is unverified.

## Revision History

| Version | Date | Change |
|---------|------|--------|
| 0.1 | 2026-10-03 | First edition, from the 2026-10-03 bootstrap spec. Written before RTL, the way scoria's 0.1 was: the delta analysis settles the markings, the design point, and the DFI 4.0 boundary; the MAS and the kmap book follow as separate books. |
| 0.3 | 2026-10-04 | P2 carried per this chapter's inheritance table: `bank_timer`/`bank_timers`, `page_policy`, the read/write CAMs, `wr_splitter` + `axi_burst_chopper`, `rd_return_ring`, `dfi_cdc`, and `cmd_history_checker` land as `andesite_*` with scoria's suites ported green (the checker grows the DDR4 long/short spacing set the MAS names — additive checks, mechanism untouched). `powerdown_ctrl`/`dfi_signal_pack` ride as the dormant pair, uninstantiated, waking condition unchanged. `rd_intake`/`wr_intake` re-sequence to the front of P3: they instantiate `addr_mapper`, a P3 block — dependency order over this book's idealized list, recorded in the P2 gate. |
| 0.2 | 2026-10-04 | P1 RTL landed per the RTL-bootstrap spec: `andesite_pkg`, `andesite_dfi_cmd_formatter`, `andesite_mode_register`, and `andesite_init_sequencer` exist with model-first DV. The init slice walks the DFI 4.0 BFM at DDR4-1600 (vendored jedec/ddr4-1600.csv timings) through JEDEC init with the anchored order proven at the pins and zero DRAM-state violations; gear-down entry exercised as a second configuration. The kmap book's command-decode citations now point at the RTL lines, so the drift gate is live; per-command boolean SOP verdicts land with the P3 maps. First-consumer BFM gaps the slice exposed and the DV repo fixed: the v4.0 `cs` rename in the receive path and wired roster, and presence-guarded optional wires. The MAS Table 2.2/2.2.2 port tables were reconciled with the landed interface (v4.0 names, 5-bit `op_i`, 3-bit MR index on `cmd_bank`); deferred ports (`dfi_alert_n`, `ca_o`/`ca_valid_o`) are recorded as follow-ons, not stubs. |

: Table 0.3: Revision history

## How to read this book

Chapter 1 fixes purpose and vocabulary. Chapter 2 is the shape of the
controller, with one figure in which every block is colour-marked against
scoria — read that figure and you know the size of this project. Chapter 3 is
the heart: the ten areas DDR4 and LPDDR4 actually change, and the dormant and
deferred lists. Chapter 4 is the DFI v4.0 boundary and what moved from v3.1.
Chapter 5 is the package and parameters. Chapter 6 is how it is verified, and
what separates this edition from a 1.0.

**The caution this document carries by construction.** v0.1 is written before
the RTL, and a specification written first can be *unbuildable* — that is the
risk it carries. The evidentiary rule is the mitigation. The DFI 4.0
specification is now on disk and was studied on 2026-10-04 as andesite
TASK-005; DFI 4.0 clause numbers in this edition are real citations, and the
study corrections for v3.1 → v4.0 chip-select renames, the missing
`dfi_wrdata_dbi` pin, and the `dfi_init`/`dfi_ca_capture` mismatches are
recorded in HAS ch04 and MAS ch03. Where implementation later corrects the
specification, the correction belongs in this revision history, not dropped
silently.
