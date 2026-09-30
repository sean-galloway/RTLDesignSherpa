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

# Write Leveling: the Interface, Not the Search

## What write leveling is for

On a fly-by command/address topology, DQS arrives at each DRAM at a different
time relative to CK. Write leveling lets the controller discover that skew per
device: the DRAM is put into a leveling mode via MR1, the controller drives a
DQS edge, and the DRAM reports on its prime DQ bit whether that edge arrived
before or after the CK rising edge. The controller walks its DQS delay until the
reported value flips. That flip is the answer.

## The decision: scoria provides the interface, firmware runs the search

This was settled as decision D2. `scoria_wrlvl_ifc` contains **no search loop**.

The reasoning is the family's standing architectural boundary. A delay-line walk
is PHY calibration: the step size, the number of taps, their monotonicity and
their temperature behaviour are all properties of the PHY, not of DDR3. pumice
made the same call and levels its board from firmware over a CSR passthrough,
with no hardware state machine — thirteen PHY knobs reached indirectly, the
search in a host program, the settled result cached.

The alternative — a hardware FSM — buys independence from a host at the cost of
importing PHY-specific search logic into a portable controller, and of a
calibration bug being a silicon respin instead of a script edit.

**Important:** this is a boundary decision, not an efficiency one. A future
system that needs autonomous leveling should add an external calibration engine
driving this interface, not a search loop inside the controller.

## What the block owes the system

| Responsibility | Detail |
|---|---|
| DFI leveling handshake | drive `dfi_phylvl_req_cs_n` and observe `dfi_phylvl_ack_cs_n`, with `dfi_phy_wrlvl_cs_n` selecting write leveling; per chip select, per DFI v3.1 |
| MR1 path | enter and leave the DRAM's write-leveling mode by MRS to MR1, sequenced against the handshake |
| Timing windows | enforce `tWLMRD`, `tWLDQSEN`, `tWLO` and `tWLOE` as **runtime CSRs** |
| Result capture | present the prime DQ bit's reported value to the host, per chip select |
| Telemetry | `*_STATS`: attempts, flips observed, current window, and whether a leveling pass has ever completed |

: Table 3.3: `scoria_wrlvl_ifc` responsibilities

## The timing windows

From JESD79-3F:

| Parameter | Value | What the controller must do |
|---|---|---|
| `tWLDQSEN` | 25 nCK minimum | wait this long after entering leveling mode before driving DQS low / DQS# high; by its expiry the DRAM has applied ODT to those signals |
| `tWLMRD` | 40 nCK minimum | wait this long before the first DQS pulse. **The maximum is controller-dependent** — the spec explicitly declines to bound it |
| `tWLO` | per speed bin | the DRAM returns the result on the prime DQ bit(s) asynchronously, this long after the DQS edge |
| `tWLOE` | per speed bin | DQ output uncertainty, defined to permit mismatch across DQ bits |

: Table 3.4: Write-leveling timing windows

**Note on `tWLMRD`'s open maximum.** Because JESD79-3F leaves the maximum to the
controller, scoria must *define* one rather than inherit it, and the definition
belongs in the CSR: a host that waits forever for a result it will never get is
indistinguishable from a broken link. The requirement is a CSR-settable timeout
with a distinct status bit, so a leveling attempt that never reports is
reported as a timeout and not as a flip that failed to arrive.

**Note on `tWLOE`.** It exists to allow mismatch *across DQ bits*, which only
matters if the controller samples more than the prime bit. If the
implementation samples one bit, `tWLOE` is inert — and that should be an
explicit, documented choice rather than an accident.

## The telemetry requirement, and why it is not optional

The `*_STATS` surface is a requirement rather than a nicety, and the reason is a
lesson paid for on pumice's board: a detector that has never fired is not
evidence of anything. pumice's data-integrity CRC checker had never once fired,
and proving it worked required deliberately corrupting the analog eye until it
reported every beat mismatched.

A leveling interface that reports "converged" without exposing the attempts and
the observed flips is the same trap. The requirement is therefore that a host can
distinguish four states: never attempted, attempted and converged, attempted and
timed out, and attempted with no flip found across the whole window.
