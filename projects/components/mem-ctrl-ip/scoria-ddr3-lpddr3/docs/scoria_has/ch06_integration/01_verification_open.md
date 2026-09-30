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

## Question resolutions (v0.2)

Five questions were listed in v0.1. Two are answered, one is struck as
malformed, and two are deferred with a named condition.

| # | Question | Resolution |
|---|---|---|
| Q1 | DFI low-power handshake ordering on exit | **ANSWERED: the question does not arise on a Series-7 PHY.** See below |
| Q2 | May periodic `ZQCS` preempt queued demand traffic? | **ANSWERED: no. Request/grant, sharing the maintenance sequencer** |
| Q3 | Sample one prime DQ bit or several? | **ANSWERED: the prime bit only**, which makes `tWLOE` inert |
| Q4 | The value of `tWLMRD`'s controller-defined maximum | **ANSWERED in kind: no PHY supplies one.** It is a policy value, not a measurement. See below |
| Q5 | `REFpb` ordering: sequential or occupancy-aware? | **STRUCK — malformed.** The device owns the sequence (Ch 3.4) |

: Table 6.1: Question resolutions

### Q1 and Q4: I was wrong to call these PHY-blocked

Both were deferred in v0.2 and v0.3 "pending a PHY choice". Examining the PHY
shows that framing was wrong in both cases, and the correction matters because
it unblocks the last two questions in this document.

**The PHY choice is narrower than it looked.** LiteDRAM's Series-7 PHY is one
module, `s7ddrphy`, whose `A7DDRPHY` and `K7DDRPHY` classes differ by target
family, not by DFI behaviour, and it supports DDR2 and DDR3 with write leveling.
For any Xilinx 7-series target -- which is every board this repository owns --
the PHY is that module. There was no branch to wait on.

**Q4: no PHY supplies a `tWLMRD` maximum, because none can.** `s7ddrphy`
exposes exactly two leveling controls, `_wlevel_en` (a CSR storage field) and
`_wlevel_strobe` (a CSR pulse), and contains **no timeout of any kind**.
JESD79-3F declares the maximum controller-dependent and the PHY declines it too,
so the value is a *policy* decision — how long to wait before declaring a
leveling attempt failed — not a number to be measured off a PHY. scoria defines
it, as this document already specified: a CSR timeout with its own status bit.
Choosing the number is a one-line decision, not an experiment.

**Q1: the question does not arise on this PHY.** `s7ddrphy` implements **no DFI
low-power interface at all** — no `lp_req`, no `lp_ack`, nothing. Nor does
LiteDRAM's generated DDR3 controller: a search of the generated core for
`dfi_lp` returns zero hits, while `CKE` appears 92 times. Power-down on this
PHY family is achieved by **DRAM command** — CKE plus `SRE`/`SRX` — and not
through the DFI low-power channel.

So there is no exit-ordering handshake to get wrong, because there is no
counterparty to handshake with. The requirement changes accordingly:

- `powerdown_ctrl` achieves precharge-power-down, active-power-down and
  self-refresh through CKE and `SRE`/`SRX`, which is what pumice already does.
- scoria still *exposes* `dfi_lp_ctrl_req` and `dfi_lp_data_req`, because DFI
  v3.1 defines them and a future PHY may consume them. Their specified
  behaviour when no acknowledgement ever arrives is to **time out and report**,
  never to block power-down — an unacknowledged request must not be able to
  wedge the controller.
- The ordering question returns only with a PHY that implements the interface,
  and at that point it is answerable by reading that PHY rather than by
  speculation.

**Note on the correction.** This is the second framing error in this document's
short life: v0.1 asked Q5, which the DRAM standard had already settled, and
v0.2/v0.3 deferred Q1 and Q4 to a decision that turned out not to exist. Both
came from the same habit — treating something as an open choice without first
checking whether the thing it depends on had already answered it. The cheap
check is to read the artifact.

### Q2: ZQCS is a request, never a preemption

**Answered from a DDR3 LiteDRAM core, generated for this purpose.** v0.2
answered this by analogy, because the LiteDRAM core in the pumice flow is a
DDR2 configuration and contains no ZQ logic at all. Sean's suggestion was to
generate a DDR3 one; that core now exists and the analogy is no longer needed.

What the DDR3 core does (`bin/litedram_ddr3_ref.yml` regenerates it):

- **ZQCS shares the refresher's FSM.** There is one `refresher` state machine,
  and it starts the ZQCS executer from inside itself and waits for its done.
  Maintenance is not a separate agent competing for the bus; it is one
  sequencer issuing both kinds of maintenance command.
- **It requests, and waits.** `refresh_req` to every bank machine is driven
  from the maintenance command's valid. The bank machines must grant -- drain
  and precharge -- before the command issues. Nothing is preempted.
- **The executer is a timed sequence**, a trigger counter stepping to 19 and
  then asserting done, with the periodic timer held off (`zqcs_timer_wait`)
  until it completes. So `tZQCS` is enforced by holding the *next* interval,
  not by blocking traffic.

That is three independent controllers agreeing -- LiteDRAM DDR2 refresh,
LiteDRAM DDR3 ZQCS, and pumice refresh -- so the baseline is settled rather
than merely plausible: `scoria_zq_ctrl` raises a demand and waits for a grant.

**Design consequence worth taking from LiteDRAM:** it shares one sequencer
between refresh and ZQ rather than giving ZQ its own. scoria's Chapter 2.3
specifies `scoria_zq_ctrl` as a separate FUB, and that remains the plan --
pumice's `refresh_ctrl` is already substantial and adding a second maintenance
mode to it would couple two independently-verifiable things. But the *interface*
both present to the scheduler should be identical, so that the arbiter sees one
kind of maintenance demand with a source tag rather than two special cases.

**Condition to revisit unchanged:** if characterization shows `ZQCS` starved
under sustained demand -- the interval slipping materially past its CSR value --
placement becomes TASK-001's scheduling question. The issued-calibration counter
required in Chapter 3.2 is what makes that measurable rather than suspected.

### Q3: sample the prime DQ bit only

The write-leveling interface samples the prime DQ bit and not the full byte.
The consequence is explicit: **`tWLOE` is inert in this implementation.** It
exists in JESD79-3F to allow mismatch *across* DQ bits, which only matters to a
controller sampling several.

`tWLOE` remains a CSR field so that a later implementation can sample wider
without a register-map change, and it is documented as unused rather than
omitted — an absent register is a silent limitation, while a present one
documented as inert is a decision a reader can find.

### Q5: struck rather than deferred

v0.1 asked whether `REFpb` round-robin should be sequential or occupancy-aware.
There is nothing to choose: the `REFpb` command carries no bank address, the
sequence is fixed in the device, and the controller's rotor only mirrors the
device's counter. JESD209-3C states the sequence is fixed sequential
round-robin; pumice's implementation already cites JESD209-2 §6.6 for the same
property in LPDDR2.

It is struck rather than deferred because deferring implies a decision still
exists. This one never did, and the correction also moved `refresh_ctrl` from
MODIFIED to INHERITED — see Chapter 3.4.

## What would make this a 1.0

Three things, in order:

1. A value chosen for `tWLMRD`'s maximum (Q4 reduced this to a one-line policy decision) and, if a board is selected, its PHY's DFI low-power behaviour confirmed against Q1's assumption.
2. The RTL written, and this document reconciled against it — with every
   INHERITED marking either confirmed or corrected. A marking that turns out to
   be wrong is a defect in this document, and the correction goes here rather
   than being dropped silently.
3. The exact CSR map, which comes from the RDL and cannot honestly precede it.

Until then this is a 0.1: a specification good enough to implement against, and
explicit about where it is not yet a description of anything.
