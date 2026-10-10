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
| Title | scoria DDR3/LPDDR3 Family Controller — Hardware Architecture Specification |
| Version | 0.10 |
| Date | 2026-10-10 |
| Status | Advanced-modes edition. v0.8 reconciled this book with the landed RTL; v0.9 specifies TASK-001's bounded advanced modes (elastic refresh, TCR, ZQCS placement) in Ch 3.2/3.4 per that RTL; v0.10 restates the design-point clock at 75 MHz per the owner (2026-10-10: "100 MHz was never the target"), closing scoria BUG-003 — revision history below |
| Scope | Controller architecture to the DFI v3.1 boundary, for DDR3 and LPDDR3 |
| Not in scope | The PHY; board bring-up; the DDR4/LPDDR4 features DFI v3.1 also carries |

: Table 0.1: Document information

## Related documents

| Document | Where | Relationship |
|---|---|---|
| scoria design requirements | `../design-requirements.md` | **binding foundation** — the spec deltas and settled decisions |
| pumice HAS | `../../pumice-ddr2-lpddr2/docs/pumice_has/` | the architecture scoria is derived from |
| pumice design requirements | `../../pumice-ddr2-lpddr2/docs/design-requirements.md` | its coding guidelines and enforcement rules apply here unchanged |
| JESD79-3F | outside the repo, cold storage | DDR3 device standard |
| JESD209-3C | outside the repo, cold storage | LPDDR3 device standard |
| DFI v3.1 | `dfi-specs/` | the PHY boundary |

: Table 0.2: Related documents

## Terminology

**INHERITED / MODIFIED / NEW**
The marking every block in this document carries, relative to pumice.
*Inherited* means the pumice block is used as-is, and its correctness argument
transfers with it. *Modified* means a named, bounded change. *New* means no
pumice counterpart exists.

**nCK**
A DRAM clock cycle, the unit JESD79-3F states most command-spacing minimums in.

**Prime DQ bit**
In write leveling, the DQ bit (or bits) on which the DRAM returns the leveling
result.

**Maintenance traffic**
Commands the controller must issue that no host requested — refresh and ZQ
calibration. It competes with demand traffic for the command bus, which makes
it a scheduling problem and not only a sequencing one.

## Revision History

| Version | Date | Change |
|---------|------|--------|
| 0.10 | 2026-10-10 | Design-point clock restated at **75 MHz** per the owner (2026-10-10: "100 MHz was never the target"). Ch 2.4 Table 2.4 (`System clock` row and the `DRAM clock` derivation — the PHY clock comes from the 200 MHz board oscillator's PLL, not `4 x sys`) and the "still open" timing-closure bullet updated; scoria BUG-003 closed on the restatement (its OOC measurement, -2.022 ns at 10 ns, is ~+1.3 ns of slack at 13.33 ns). DRAM side unchanged: DDR3-800, 400 MHz CK, 3200 MB/s peak. |
| 0.9 | 2026-10-03 | TASK-001's bounded advanced-modes tranche specified from the landed RTL: Mode A (demand-aware elastic refresh) and Mode B (TCR) in Ch 3.4, Mode C (ZQCS placement policy) in Ch 3.2, with the mode-select CSRs and `REF_STATS` telemetry in Ch 5. `refresh_ctrl` marking INHERITED → MODIFIED; the Ch 2 block diagram (figure re-rendered), module hierarchy, and Ch 3.1 deltas table updated to match (inherited FUB count 21 → 20). The refresh/ZQ portion of the TASK-008 reconciliation is thereby done; the remainder — the other inherited blocks, `tWLMRD`'s policy value, and whole-map CSR finalization — stays open in Ch 6. |
| 0.8 | 2026-10-03 | Reconciled with the landed RTL and the first board work: verification status brought current (221 tests, 9 formal blocks, top tier AXI-in/DFI-out); `dfi_reset_n` recorded as presented under its DFI name and the two v3.1-only data-phase chip selects recorded as driven, constant `'0` at `NUM_RANKS=1` (scoria TASK-005); the board build flow and the BUG-003 100 MHz out-of-context timing result recorded. What remains for a 1.0 is restated in Chapter 6 and filed as a task. |
| 0.7 | 2026-09-30 | Ch 3.2: DDR3's init sequence needs no precharge-all, no double refresh, no OCD pair and no second MR0 load (the DLL-reset bit is self-clearing) -- the FSM drops seven of pumice's states and adds three. Found while implementing. |
| 0.6 | 2026-09-30 | Corrected during implementation: `dfi_signal_pack` is INHERITED, not MODIFIED -- it packs only signals DFI v3.1 leaves unchanged, and v3.1's new channels are driven at the layer above. Inherited FUBs 20 -> 21, modified 4 -> 3. |
| 0.5 | 2026-09-30 | Target design point named (Sean: "assume k7ddrphy on genesys2 if it helps"): Genesys 2, K7DDRPHY, 2 x MT41J256M16 on a 32-bit bus, DDR3-800, 3200 MB/s theoretical peak. Fixes DFI_RATE=4, NUM_BANKS=8, row 15, col 10, DQ 32, and gives the DDR3-800 JEDEC timing set. |
| 0.4 | 2026-09-30 | Q1 and Q4 answered rather than deferred: s7ddrphy is the PHY for every board here, it implements no DFI low-power interface, and it imposes no leveling timeout. `powerdown_ctrl` corrected to INHERITED in mechanism -- power-down is CKE and SRE/SRX, not the DFI low-power channel. No open questions remain. |
| 0.3 | 2026-09-30 | Q2 and D2 re-answered from a generated DDR3 LiteDRAM core instead of by analogy (Sean: "you might need to generate a ddr3 version of litedram"). ZQCS confirmed as request/grant sharing the refresher FSM; write leveling confirmed as CSR-only with no state machine. |
| 0.2 | 2026-09-29 | Q1-Q5 resolved or deferred with conditions. `refresh_ctrl` corrected from MODIFIED to INHERITED: pumice already implements `REFpb` and the device owns the sequence, so Q5 was malformed and is struck. |
| 0.1 | 2026-09-29 | First edition. Written from the delta analysis, with decisions D1-D3 settled. No RTL exists; every block is specified, not described. |

: Table 0.3: Revision history

## How to read this book

Chapter 1 fixes purpose and vocabulary. Chapter 2 is the shape of the
controller, with one figure in which every block is colour-marked against
pumice — read that figure and you know the size of this project. Chapter 3 is
the only chapter with substantial new engineering: the four blocks DDR3 and
LPDDR3 actually change. Chapter 4 is the DFI v3.1 boundary and what moved from
v2.1.1. Chapter 5 is the package and parameters. Chapter 6 is how it is
verified, and what separates this edition from a 1.0.

**A caution this document outgrew.** v0.1 was written before the RTL, and a
specification written first can be *unbuildable* — that was the risk it
carried. The RTL now exists, and this edition has been reconciled against it;
where implementation corrected the specification, the correction is in the
revision history above. What remains for a 1.0 is named in Chapter 6 and filed
as a task. The evidentiary rule is unchanged: where this edition states a
structure, it is inherited from a controller that is built and measured, or
built here and verified; where it states a timing, it is cited.
