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

# What the K-maps Prove

## Methodology

The kmap workbook ([`gen_amber_contracts_kmaps.py`](../../gen_amber_contracts_kmaps.py)) applies the STREAM-derived methodology:

1. Identify every important combinational decision signal.
2. List axes as `(name, expression, cite)` triples.
3. State `depends_only_on` evidence that justifies the axis list.
4. Add checked `relations` that mark unreachable input combos as don't-cares.
5. Derive the minimal SOP mechanically with Quine-McCluskey.
6. Diff the derived cover against the RTL SOP when RTL exists.

Because amber has no RTL yet, the workbook is a **pre-RTL contract**. The derived SOP is the logic the future RTL must implement. `rtl_sop` is intentionally absent in the workbook; when RTL lands the diff step produces one of three verdicts.

## The Three Verdicts

The verdict logic is implemented in `bin/kmaps/minimize.py`:

| Verdict | Meaning | Action |
|---------|---------|--------|
| **IDENTICAL** | The RTL SOP matches the derived minimal cover. | No change needed; the RTL is already minimal. |
| **RTL-REDUNDANT** | The RTL SOP includes extra literals or terms but produces the same truth table. | Document why the redundancy exists (timing, readability, defensive coding). |
| **RTL-DIFFERS** | The RTL SOP produces a different truth table than the derived cover. | Investigate: bug, unstated invariant, or missing relation. |

## Control-Sheet Verdict (2026-10-07, updated Task 4)

`amber_control` landed (Task 3, CPU path; Task 4, snoop service). Verdict
for the `K-maps amber control` miss-path sheet (axes
`{hit, victim_dirty, pending_bypass_match}`, outputs
`{start_drain, start_fill, replay_now}`):

- **Truth-table equivalence: PASS at gate/func/full, both geometries**
  (tiny s16w2 + default s128w4). The RTL implements the workbook's PROPOSED
  cover literally, evaluated in `CTRL_MISS_VICTIM` where `hit == 0` by
  construction:
  `start_drain = victim_dirty & !pending_bypass_match`,
  `start_fill = !victim_dirty & !pending_bypass_match`,
  `replay_now = pending_bypass_match`.
  The two reachable cells are exercised by directed dirty/clean-victim
  misses and by the 10k-transaction randomized oracle-lockstep suite
  (`dv/tests/test_amber_control.py`).
- **`pending_bypass_match` axis (2026-10-07 Task 4 update): now
  stimulus-reachable — driven on the snoop decision path.** With
  `CTRL_SNOOP` service live, the same pf registers feed the snoop
  reference-state resolution (bypass match → post-fill `pf_state` +
  `pf_data_valid`-gated CD beats). Directed classes
  `SnoopPendingFillBypass` (pre-RLAST snoop, CD stall until a late beat),
  `SnoopOtherLineMidFill` / `SnoopPostCommitApplies` (pf no-match →
  port-B installed-state decode), `ImStepPendingClearCorner` (repeat
  snoop with the invalidation pending), and `UpgradeNoBypassArm` (upgrade
  in flight: pf unarmed, snoop answered from the installed S entry)
  exercise both polarities of the axis plus the every-cycle
  `BypassNeverAnswersInvalid` invariant. On the miss path itself the axis
  remains constant-0 **by construction** — the pf register's lifetime is
  exactly `CTRL_MISS_FILL..CTRL_FILL_WRITE` of the single outstanding
  transaction and fills re-arm only after `CTRL_FILL_WRITE` clears it, so
  `CTRL_MISS_VICTIM` entry is exclusive with an armed bypass; the
  killed-upgrade re-fetch (`ImStepPendingClearCorner`,
  `UpgradeKilledByInvalidatingSnoop`) drives the full
  LOOKUP→MISS_VICTIM→MISS_FILL→FILL_WRITE→REPLAY re-lookup sequence with
  the axis at its constant-0 value. `replay_now` stays defensive-only.
- **SOP-literal diff against the QM-derived covers: NOT CHECKED**, same
  rationale as the snoop sheets (the RTL expresses the cover as named
  decision wires, not minimized literals; the meaningful diff is the
  truth-table one).

## First-Verdict Status (2026-10-06)

The first RTL slice landed: `amber_pkg` (the Table 3.0 decode functions
`amber_snoop_crresp` / `amber_snoop_next_state`) and its module wrapper
`amber_snoop_kmap`. Verdicts for the six snoop sheets (the four CRRESP maps
and the two next-state maps):

- **Truth-table equivalence: PASS at gate/func/full.** The TB
  (`dv/tests/fub/test_amber_snoop_kmap.py`) carries an independent copy of
  HAS Table 3.0 and exhausts the reachable space at gate, adds the reserved
  encodings at func, and the whole 3-bit x 3-bit space at full. One real
  discrepancy was caught and resolved in the TB's favor of the documentation:
  Modified + CleanInvalid carries `IsShared=1` per Table 3.0.
- **SOP-literal diff against the QM-derived covers: NOT CHECKED, deferred.**
  The RTL implements the table as a case decode, not minimal SOP literals;
  the meaningful diff is the truth-table one above. Supplying `rtl_sop=` and
  re-deriving is deferred until `amber_snoop_resp` integrates this decode —
  if the integration restructures the logic, the literal diff would be
  repeated work.

All other sheets (address decode, MonBus events) remain pre-RTL contracts
with `VERDICT: NOT CHECKED`.

---

**Last Updated:** 2026-10-07 (Task 4 snoop-service update)
