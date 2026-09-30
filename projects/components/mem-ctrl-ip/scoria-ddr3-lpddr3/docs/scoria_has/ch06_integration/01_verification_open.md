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

## The target is the DFI boundary

Verification is against the DV repository's DFI bus functional model, in cocotb.
No board (Sean, 2026-09-29: sim now, board decision later).

That boundary is chosen for the same reason pumice chose it: it is the one
interface where the controller's obligations are fully specified by a standard,
so a model can be authoritative rather than approximate. pumice's experience is
that code passing against the BFM passes on hardware modulo PHY training — which
is exactly the residue this specification pushes into firmware anyway.

## What must be verified, beyond inheriting pumice's suites

The inherited blocks bring their tests with them. The new and modified ones need
new coverage, and four items are specific enough to name now:

1. **The init sequence, in JEDEC's order.** Not "the DRAM came up" but
   step-by-step: `RESET#` held, the 500 us wait, clocks stable before CKE, CKE
   continuously high, `tXPR` before the first MRS, then MR2, MR3, MR1, MR0,
   then `ZQCL`, then `tDLLK` and `tZQinit`. A checker that asserts the *order*,
   because order is what pumice got wrong on its equivalent.
2. **ODT during init.** High-impedance while `RESET#` is asserted, and held
   statically — LOW if `RTT_NOM` is enabled in MR1 — until init completes.
3. **Write leveling as a protocol, not an outcome.** The handshake sequence and
   every timing window, with the `tWLMRD` timeout exercised deliberately. A
   leveling interface whose timeout path has never run is an untested path on the
   only path that reports failure.
4. **Per-bank refresh retention.** The inherited formal property proves retention
   headroom across all sixteen postpone values for all-bank refresh. `REFpb`
   changes that arithmetic — the per-bank interval is the all-bank interval times
   the bank count — so the property must be re-established, not carried forward.
   Carried forward unchanged it would prove the wrong thing and appear green.

**Important — the formal area is the right home for the spacing properties.**
No assertions go in the RTL. pumice's `formal/pumice` area proved nine modules
and found two real bugs, including the `global_timers` next-state defect this
specification tells scoria to inherit the fix for. scoria should open its own
formal area early, and the `cmd_history_checker` — which independently re-derives
JEDEC spacing from the issued command stream — should grow DDR3's parameters
before the RTL is trusted.

## Open questions this edition cannot close

Listed rather than guessed at. Each needs either a decision or an experiment.

| # | Question | Why it is open |
|---|---|---|
| Q1 | The DFI low-power handshake ordering on exit | Bringing the control and data paths back up independently is where a naive implementation deadlocks, and the correct ordering depends on PHY behaviour this document cannot fix |
| Q2 | Whether periodic `ZQCS` may preempt queued demand traffic, or only fill gaps | A characterization question. The baseline requirement is that it is issued at all, with the interval observable |
| Q3 | Whether `scoria_wrlvl_ifc` samples one prime DQ bit or several | If one, `tWLOE` is inert. Either is legal; the choice should be explicit rather than emergent |
| Q4 | The value of `tWLMRD`'s maximum | JESD79-3F declares it controller-dependent, so scoria must define it. Needs a PHY-informed number |
| Q5 | Whether LPDDR3's `REFpb` round-robin order should be strictly sequential or follow bank occupancy | Sequential is simplest and provable; occupancy-aware may be better under bank-parallel load. TASK-001 territory |

: Table 6.1: Open questions

## What would make this a 1.0

Three things, in order:

1. The five open questions above answered.
2. The RTL written, and this document reconciled against it — with every
   INHERITED marking either confirmed or corrected. A marking that turns out to
   be wrong is a defect in this document, and the correction goes here rather
   than being dropped silently.
3. The exact CSR map, which comes from the RDL and cannot honestly precede it.

Until then this is a 0.1: a specification good enough to implement against, and
explicit about where it is not yet a description of anything.
