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

# Verification Strategy, and the Open Questions

## The target is the DFI boundary, in simulation only

Verification is against a DFI v4.0 bus functional model, in simulation. No
board is named for this controller — the 7-series targets this repo's boards
carry do not support DDR4 — and that is a deliberate strengthening of the
rule, not a weakening: with no board even conceivable, nothing can be left
for bring-up to find.

**The in-house BFM is DFI 4.0-partial, not absent.** The DV repository's
CocoTBFramework DFI component exists and already carries a CA-parity
behavior; what it lacks is the LPDDR4 6-bit CA encoding (its `lpddr_ca.py`
covers LPDDR2/3). Acquisition is therefore not the problem — gap analysis
and extension are, and that is andesite TASK-005 (amended 2026-10-04, when
the DFI v4.0 spec PDF also surfaced in the operator's research storage at
`/mnt/data/github/dfi-specs/`). Until TASK-005 closes, every DFI 4.0 clause
citation in this book and the MAS carries `§TBC(TASK-005)`. The BFM is
configured to the design-point geometry of Chapter 2.4 — the bank-group
geometry on the DDR4 side, eight ungrouped banks per channel on the LPDDR4
side, x8 / x16 widths, four DFI phases — because verifying at the geometry
the design point uses is free, and verifying at a different one silently
weakens every result.

The boundary is chosen for the reason pumice chose it: it is the one
interface where the controller's obligations are fully specified by a
standard, so a model can be authoritative rather than approximate. pumice's
experience — BFM-passing code passes on hardware modulo PHY training — is
exactly the residue this family pushes into firmware.

## The inherited-bring-tests argument

The inherited blocks bring their verification with them. scoria's suites —
221 tests and 9 formal blocks at last measure — transfer with the blocks
they test, and pumice's board measurements sit upstream of those. The
obligation this controller adds is not to re-prove the front end; it is to
prove the deltas. That argument is load-bearing: it is why the marking table
is also the test-plan structure.

## What must be verified, beyond the inherited suites

Named now, because "new coverage" that isn't enumerated doesn't happen:

1. **The init sequences, in JEDEC's order, both memtypes.** A checker that
   asserts the order — RESET# held, the CKE waits, the MR3-MR6-MR5-MR4-MR2-
   MR1-MR0 order on the DDR4 side and JESD209-4's order on the LPDDR4 side,
   ZQ closing init — because order is what this family has historically
   gotten wrong (pumice's EMRS3-first sequence, benign but wrong).
2. **Gear-down as a mode switch.** Entry programmed, bus rate switched on
   both sides of the DFI boundary, and full-rate init still proven with
   gear-down disabled. The handshake's clause citations are §TBC(TASK-005)
   until the spec is on disk; the *behaviour* is verifiable the moment the
   BFM exists.
3. **CA parity and `alert_n` as a protocol.** The counting machinery
   exercised, an injected parity fault raising `alert_n`, and the error
   surfacing through `dfi_error` — including the firmware-assist split if Q4
   below lands there.
4. **ODT as a schedule.** The `odt_ctrl` policy states over time: RTT_WR
   confined to write bursts, PARK in the idle policy, the latency family
   enforced on the pin, and a trace that shows a policy that never leaves
   PARK (which is what "dynamic ODT off" looks like from outside).
5. **FGR retention, re-derived per factor.** The inherited proof covers 1x
   arithmetic; 2x and 4x change the interval arithmetic. Each factor gets
   its own property in `formal/andesite/refresh_ctrl`; none is carried
   forward green. Same rule for the LPDDR4 per-bank arithmetic with
   controller-named banks.
6. **The LPDDR4 CA bus as a two-cycle encoding.** Command-by-command checker
   against the truth table the kmap book pins — the tables in
   `docs/kmaps/generated/` are the checker's expected values, which is what
   the generated kmap book is *for*.
7. **Training as protocol, timeouts exercised deliberately.** Write leveling
   (inherited), read leveling, and CA/WDQ training: handshakes, windows, and
   every timeout path — a timeout that has never fired is an untested path
   on the only path that reports failure.
8. **The dormant pair stays on the record.** `powerdown_ctrl` and
   `dfi_signal_pack` verified uninstantiated-in-tree, so the dormant
   disposition of Chapter 3.1 can't silently rot into dead code or silently
   resurrect.

**The formal area is the right home for the spacing properties.** No
assertions go in the RTL — the family rule, tool-compatibility, quoted in
Chapter 1.2. `cmd_history_checker` grows DDR4's long/short parameters before
the RTL is trusted, exactly as scoria grew DDR3's; the spacing properties
that checker shadows — tCCD_L/S, tRRD_L/S, the ODT turn-arounds — are the
first candidates for `formal/andesite`.

## Status, 2026-10-04

No andesite RTL exists. This book is a v0.1 written from the delta analysis,
the same posture scoria's v0.1 had — and the evidentiary rule exists because
that posture can specify something unbuildable. What exists now: this book,
the vault lane, and the family docs. What is measured: the *predecessor's*
evidence, cited chapter by chapter where it transfers.

## Open questions

| # | Question | Named condition |
|---|---|---|
| Q1 | The numeric init constants (`tINIT*`, `tDLLK`, `tZQinit`, `tMRD`, `tMOD`) | Read from JESD79-4 / JESD209-4 in cold storage at CSR-derivation time (first RTL pass). Named, not invented, per the evidentiary rule |
| Q2 | Write CRC: un-defer? | A characterization or board campaign that needs end-to-end write protection; the addition is bounded to the write datapath (Ch 3.1, 3.5) |
| Q3 | Gear-down coverage scope in the first sims | Decided when the BFM's capabilities are known (TASK-005 close); full-rate-only is an acceptable first pass if the switch is protocol-checked |
| Q4 | CA parity: hardware counter vs firmware assist | A scope decision at MAS/RTL time; either way the protocol check of item 3 above must pass, and the split is recorded in the MAS |
| Q5 | LPDDR4 DVFS/DSM, and the dormant pair's waking | A low-power consumer and a target that can measure power; wakes `powerdown_ctrl`/`dfi_signal_pack` per Ch 3.1 |
| Q6 | DFI 4.0 clause confirmation and BFM provenance | **andesite TASK-005's close condition**: the spec is acquired, every `§TBC(TASK-005)` suffix in this book and the MAS is confirmed or corrected, and a BFM is selected with an integration note here |

: Table 6.1: The open questions, each with the condition that answers it

## What would make this a 1.0

Three things, in order — the same three scoria's book named, one generation
later:

1. **RTL exists, and this document is reconciled against it block by
   block.** Every INHERITED marking confirmed or corrected, every MODIFIED
   change verified bounded as named, every NEW block found where this book
   said it would be. A marking that turns out wrong is a defect in this
   document, and the correction goes in the revision history rather than
   being dropped silently.
2. **The exact CSR map, from the RDL.** The map cannot honestly precede the
   RDL; Chapter 5's groups become offsets when `andesite_csr.rdl` lands.
3. **andesite TASK-005 closed.** The DFI 4.0 clauses confirmed and the BFM
   selected — at which point every `§TBC(TASK-005)` suffix in this book is
   either a citation or a correction, and the verification strategy above
   has a counterparty.

Until then this is a 0.1: a specification that knows what it doesn't know,
and says so on the record.
