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

# Init Sequencer: RESET#, MR0-MR3, ZQ Calibration

## The sequence is JEDEC's, verbatim

JESD79-3F specifies DDR3 power-up initialization as a numbered sequence. It is
reproduced here as *requirements on the sequencer*, in the spec's order, because
the order is not ours to choose:

| Step | Requirement |
|---|---|
| 1 | Power ramp, with the spec's VDD / VDDQ / VTT / Vref ordering constraints. Board-level, not controller-level |
| 2 | After `RESET#` is de-asserted, wait **500 us** before CKE becomes active. The DRAM initializes internally during this, independent of external clocks |
| 3 | Clocks stable for at least **10 ns or 5 tCK, whichever is larger**, before CKE goes active. A NOP or Deselect must be registered before CKE goes high, meeting tIS |
| 4 | CKE must be **continuously registered high** from that point until initialization finishes — including expiry of `tDLLK` and `tZQinit` |
| 5 | Wait `tXPR` = max(`tXS`, 5 x tCK) after CKE high before the first MRS |
| 6 | MRS to **MR2** |
| 7 | MRS to **MR3** |
| 8 | MRS to **MR1**, with DLL enabled |
| 9 | MRS to **MR0**, with DLL reset |
| 10 | **ZQCL** to start ZQ calibration |
| 11 | Wait for both `tDLLK` and `tZQinit` |
| 12 | Ready for normal operation |

: Table 3.2: DDR3 initialization requirements, from JESD79-3F

## Three consequences for the sequencer

**`RESET#` is a pin, not a command.** This is the structural change. pumice's
init sequencer issues commands; scoria's must additionally drive a reset output
and hold it through a timed window. That output has to reach the top level and
the PHY, and it is the first thing in the sequence rather than something the
command path can express.

**The MR order is MR2, MR3, MR1, MR0** — and it is not sorted. Steps 6 through 9
are explicit, and MR1 carries "DLL enable" while MR0 carries "DLL reset", so the
order encodes a dependency rather than a preference.

**Note:** pumice hit precisely this. Its init programmed EMRS3 before EMRS2; the
error was benign in practice but wrong, and it was corrected to JEDEC's order.
DDR3's MR2-MR3-MR1-MR0 is the same pattern extended to a four-register set, and
the same rule applies: the sequence is a citation, not a design choice.

**ODT is constrained during init.** The DRAM holds on-die termination in
high-impedance while `RESET#` is asserted and until CKE is registered high;
thereafter ODT must be held statically — and **statically LOW if `RTT_NOM` is to
be enabled in MR1** — until initialization completes. The sequencer therefore
owns ODT during init, not just during traffic.

## ZQ calibration

`ZQCL` closes initialization (step 10) and `tZQinit` gates readiness (step 11).
Outside init, DDR3 offers `ZQCS`, the short calibration, and `tZQoper` for a long
one. All three gate command issue alongside `tMRD`, `tMOD` and `tRFC`.

### Why ZQ gets its own block

`ZQCL` at init belongs to the sequencer. Periodic `ZQCS` does not, because it is
**maintenance traffic**: the controller must issue it on an interval no host
asked for, competing with demand traffic for the command bus. That is the same
shape as refresh, and refresh has its own controller for the same reason.

`scoria_zq_ctrl` therefore:

- holds the ZQCS interval as a **runtime CSR**, so it can be swept;
- raises a demand to the scheduler rather than seizing the bus;
- enforces `tZQCS` before releasing the bus back;
- reports a count of issued calibrations, so the interval can be confirmed from
  the host rather than assumed.

**The scheduler change is one input, not a rework.** `scoria_mem_cmd_scheduler`
already arbitrates refresh demand against demand traffic; ZQ adds a second
maintenance source with the same shape.

**Note:** whether ZQCS should ever *preempt* queued demand traffic, or only fill
gaps, is deliberately not fixed in this edition. The baseline requirement is that
periodic ZQCS is issued at all, with the interval observable and settable.
Cleverness about placement is a characterization question, and scoria TASK-001
already owns the survey of scheduling modes.
