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

# Refresh: DDR3 All-Bank and LPDDR3 Per-Bank

## Marking: MODIFIED (v0.9) — inherited mechanism, TASK-001 modes on top

This chapter's marking has now changed twice. v0.1 marked `refresh_ctrl`
MODIFIED on the assumption that LPDDR3 per-bank refresh was new work. v0.2
corrected it to INHERITED, because **pumice already implements it**, for
LPDDR2, and the mechanism LPDDR3 specifies is the same one. v0.9 corrects it
once more, to MODIFIED: the inherited mechanism described below is unchanged,
but TASK-001's Modes A and B — demand-aware elastic refresh and
temperature-compensated refresh — are a named, bounded change layered on top
of it. They are scheduling policy only; the JEDEC ±8 credit ceiling is
untouched. The modes are specified at the end of this chapter.

## What pumice already has

`refresh_ctrl` carries the retention interval, all-bank refresh, JEDEC's
plus-or-minus-eight postpone and pull-in scheduling — proven in formal across
all sixteen postpone values — **and a REFpb bank rotor**.

The rotor is the part worth understanding, because it is not a scheduler:

```
r_bank_rotor advances exactly when a REFpb COMMAND is granted onto the wire,
and HOLDS through REFab mode.
```

It mirrors the **device's** internal bank counter. pumice's own comment cites
JESD209-2 §6.6 for why: the REFpb command *carries no bank address*. The
controller cannot nominate a bank. It can only track which bank the device will
refresh next, so that the bank timers know which bank is about to become busy.

The rotor also deliberately holds across a mode change rather than resetting,
because the device's counter persists — and clearing the mirror would
desynchronise it from the device.

## LPDDR3 keeps the same mechanism

JESD209-3C specifies a bank counter in the memory device, and states that the
bank sequence for per-bank refresh is **fixed to be a sequential round-robin**.
During a REFpb operation, banks other than the one being refreshed remain
accessible.

That is the LPDDR2 mechanism unchanged, so the pumice implementation transfers.

**Important — this retires an open question.** v0.1 of this document asked
(as Q5) whether the REFpb round-robin order should be strictly sequential or
follow bank occupancy. **The question was malformed.** Occupancy-aware ordering
is not available at any price: the command carries no bank address and the
device's sequence is fixed. There is nothing to choose. The question is struck
rather than deferred, because deferring it would imply a decision still exists.

## Refresh by memtype

| Memtype | Refresh available |
|---|---|
| DDR3 | all-bank `REF` only, with the JEDEC postpone window. DDR3 adds no controller-directed per-bank refresh |
| LPDDR3 | all-bank `REF`, plus `REFpb` in the device's fixed sequential order |

: Table 3.5: Refresh by memtype

Per-bank refresh matters because an all-bank refresh blocks every bank at once
while `REFpb` leaves the others accessible. On a workload with bank
parallelism that is the difference between a refresh being a stall and being
nearly free.

The cleverer schemes — out-of-order per-bank refresh, write-refresh
parallelisation, refresh pausing, SARP and DSARP — are LPDDR4/DDR5 or research,
and scoria TASK-001 assigns them to the DDR4 area rather than here. That split
stands.

## Requirements

1. Offer all-bank refresh with the JEDEC postpone/pull-in window (inherited),
   and for LPDDR3 additionally `REFpb` with the rotor mirroring the device's
   counter (inherited).
2. The all-bank versus per-bank choice on LPDDR3 is a **runtime CSR**, so both
   can be measured from one bitstream. This is the only genuinely new surface in
   this block, and it is a mode select rather than a mechanism.
3. **Re-establish the retention property for the per-bank path.** The inherited
   formal proof covers retention headroom across every postpone value for
   all-bank refresh. `REFpb` changes the arithmetic that proof checks — the
   interval seen by any one bank is the all-bank interval multiplied by the bank
   count — so the property must be re-derived for the per-bank mode.
4. `REFpb` must respect per-bank timing as an ordinary occupant of that bank:
   a per-bank refresh is an operation on a bank and the bank timer owns it.

**Important:** requirement 3 is the one most likely to be skipped, and it is
the reason refresh can be trusted at all. Carrying the all-bank property forward
unchanged would prove the wrong thing while appearing green — the failure mode
this family has been bitten by before.

**Note:** pumice's idle detection is inherited with the block and is worth
knowing about, because it looks like an arbitrary constant. Demand is CAM
occupancy, which blinks off for a few cycles between bursts; treating those
micro-gaps as idle would release postponed refreshes mid-stream and trigger
pull-ins. Only a sustained gap counts — confirmed over sixteen cycles in the
inherited baseline, and over the CSR-configurable `pullin_idle_streak`
(reset 16, the same value) once Mode A below is enabled.

## What TASK-001 adds: Modes A and B

Both modes are CSR-selected, reset to off, and bit-identical to the baseline
above when disabled — the same "config not param" rule the rest of the
controller runs on. Per-mode design detail lives in
`design-requirements.md` §6; only the architecture-relevant contract is
restated here.

### Mode A — demand-aware elastic refresh

`REF_CTRL.elastic_en` (reset 0 = baseline), with two threshold fields in the
same register: `pullin_idle_streak` (reset 16 — the inherited constant, now
sweepable) and `postpone_demand_streak` (reset 1).

- **Pull-in** fires only after demand has been idle for `pullin_idle_streak`
  MC cycles, generalizing the inherited sixteen-cycle confirmation into a
  host-sweepable threshold.
- **Postpone** engages only under a sustained demand streak of
  `postpone_demand_streak` cycles. Below that, demand counts as sporadic and
  the strict baseline stands: a refresh is requested on every interval expiry
  while anything is pending.
- The JEDEC ±8 postpone/pull-in credits remain the hard ceiling in every
  configuration; Mode A never touches the credit arithmetic.
- Telemetry: `REF_STATS_POSTPONE` / `REF_STATS_PULLIN` count the events, so
  an elastic-refresh sweep is measurable in-system rather than inferred.

### Mode B — temperature-compensated refresh (TCR)

`REF_CTRL.tcr_en` (reset 0) + `trefi_derate` (reset 0 = 1x; 1 = 2x, 2 = 4x;
the illegal encoding 3 clamps to 4x). Firmware writes the JESD79-3F §7.3.3
refresh-rate class and the tREFI tick scales with it — a cheaper refresh rate
where temperature allows, at a retention margin the temperature guarantees.
Three properties matter:

- Derate applies to the **counter reload only**: a mid-interval CSR change
  takes effect on the next reload; the running counter is not rescaled.
- `TEMP_DERATE_RANK0` keeps its LPDDR3-MR4 hardware-written path untouched
  for the future LPDDR3 build; the DDR3 path is this software-written select.
- The retention property is **re-derived with the derate factor in the
  interval arithmetic** — the same rule as `REFpb` above: a changed interval
  changes the proof, and the proof is never carried forward green.

Formal status: with both modes present, the retention and accounting
properties remain green in `formal/scoria/refresh_ctrl`, with cover points at
the configured pull-in streak boundary (evidence: scoria TASK-001 close,
2026-10-03).
