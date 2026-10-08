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

## Control-Sheet Verdict (2026-10-07)

`amber_control` landed (Task 3). Verdict for the `K-maps amber control`
miss-path sheet (axes `{hit, victim_dirty, pending_bypass_match}`, outputs
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
- **`pending_bypass_match` axis: logic-complete, stimulus-unreachable this
  task.** In the blocking pipeline a CPU lookup never coincides with an
  armed pending-fill bypass register (single outstanding transaction), and
  snoop service (the axis's real consumer) is Task 4 with the snoop inputs
  stub-tied — so the axis is structurally constant-0 on the CPU path and
  `replay_now` is defensive-only. Re-visited when Task 4 wires snoop
  service.
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

**Last Updated:** 2026-10-07
