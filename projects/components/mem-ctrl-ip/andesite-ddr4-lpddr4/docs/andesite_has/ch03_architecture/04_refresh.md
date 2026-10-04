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

# Refresh: FGR and Controller-Directed Per-Bank

## Marking: MODIFIED — inherited mechanism, FGR density on top

`refresh_ctrl` is modified for a named, bounded change: DDR4's
fine-granularity refresh adds a density dimension, and LPDDR4's per-bank
refresh changes who picks the bank. Both changes sit on top of the mechanism
scoria landed and verified — the retention interval, all-bank refresh, the
JEDEC ±8 postpone/pull-in credit window, the `REFpb` machinery, and TASK-001's
Modes A (elastic refresh), B (TCR) and C's sibling scheduling discipline —
which andesite inherits as the policy base. The credit ceiling is untouched
by every mode this block carries.

## What scoria already has, and what andesite keeps

The inherited block carries: the tREFI interval counter; all-bank `REF` with
JEDEC's ±8 postpone/pull-in scheduling; the elastic pull-in/postpone streaks
of Mode A behind CSRs; Mode B's temperature-compensated tREFI derate; the
bank rotor that mirrors the device's internal per-bank counter; and the
`REF_STATS` telemetry. The formal evidence transfers with the mechanism:
retention and accounting properties proven in `formal/scoria/refresh_ctrl`,
with the per-bank retention arithmetic re-derived for LPDDR3 as scoria's book
records.

One inherited subtlety rides with the block and deserves the same explicit
passing-on scoria gave it: demand-aware pull-in must not treat CAM
micro-gaps as idle. The sixteen-cycle (CSR-sweepable) idle confirmation
exists because demand occupancy blinks off between bursts; releasing
postponed refreshes into those gaps would fire pull-ins mid-stream. Copy the
constant with its reason.

## The DDR4 delta: FGR

DDR4's MR3 selects the refresh granularity — **1x, 2x or 4x** — trading
refresh frequency against per-refresh length inside the same tREFI budget
(JESD79-4). The controller's obligations:

1. **Hold the FGR select as a runtime CSR** (it programs MR3), so every
   density can be measured from one bitstream — the config-not-param rule
   again, and the only genuinely new surface on the DDR4 side.
2. **Scale the interval arithmetic by the FGR factor.** 2x refreshes twice as
   often at roughly half the length; 4x four times. The tREFI counter, the
   credit window's bookkeeping and the `REF_STATS` denominators all take the
   factor into account.
3. **Re-derive the retention property per factor.** The inherited proof
   covers the 1x arithmetic; each FGR factor changes the interval arithmetic
   the proof checks. Carrying the 1x proof forward unchanged would prove the
   wrong thing while appearing green — the failure mode this family has been
   bitten by before, and the rule is the same one scoria applied to `REFpb`:
   a changed interval changes the proof, and the proof is never carried
   forward green.
4. **tRFC tracks the selected density.** The per-refresh busy window differs
   by granularity and is a runtime CSR like every other timing.

## The LPDDR4 delta: the controller names the bank

This is the refresh change worth understanding, because it inverts the
constraint scoria designed around. For LPDDR2/3, the `REFpb` command carries
**no bank address** — the device's internal counter picks the bank, in a
fixed round-robin, and scoria's rotor exists solely to *mirror* that counter
so the bank timers know which bank is about to go busy. Occupancy-aware
ordering was not available at any price; scoria's book struck the question as
malformed.

JESD209-4 changes that: LPDDR4's per-bank refresh **does** carry the bank on
the CA bus. The controller picks. Consequences:

1. **The rotor is replaced by explicit bank scheduling** on the LPDDR4 path —
   a real mechanism change, and the heart of why this block is MODIFIED.
2. **Sequential round-robins still work** (the rotor's old mirror image is
   one legal policy), so the DDR4-style default is available; but the
   scheduler now has the information to do better, and the policy hook belongs
   in the block.
3. **The advanced schemes become implementable** — out-of-order per-bank
   refresh, write-refresh parallelisation and the rest of the DARP family
   surveyed in andesite TASK-001. This book implements the commodity
   round-robin and leaves the survey's schemes where they are; the
   scheduling-policy layering that scoria's TASK-001 built (CSR-select,
   reset-off, telemetry-instrumented) is exactly the hook they'd hang on.

## Requirements

1. Offer all-bank `REF` at the MR3-selected FGR density for DDR4, with the
   JEDEC credit window (inherited), and per-bank refresh for LPDDR4 with
   controller-selected banks (new scheduling, inherited credit discipline).
2. All-bank versus per-bank, and the FGR factor, are **runtime CSRs**; every
   combination is measurable from one bitstream.
3. Retention is re-derived per FGR factor and for the per-bank arithmetic, in
   `formal/andesite/refresh_ctrl` when RTL exists; until then the obligation
   is recorded here and in Chapter 6.
4. A refresh of either kind is an ordinary occupant of the banks it touches:
   the bank timers own the banks, and the request/grant discipline with the
   scheduler is inherited — maintenance requests, never preempts.
5. `REFpb`-equivalent traffic must respect per-bank timing as any operation
   on that bank would.

## Telemetry

`REF_STATS` and the Mode A/B instruments carry over, and the FGR factor plus
the per-bank policy state join them — so a refresh sweep (density, policy,
workload) is measurable in-system rather than inferred. A detector that has
never fired is not evidence of anything; this block's telemetry exists so
"refresh is fine" is a measurement, not a hope.
