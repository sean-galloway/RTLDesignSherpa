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

## Task 14 K-map Verdict Sweep (2026-10-11)

All RTL for the amber MESI L1 control plane has landed. The workbook contains three K-map sheets; there is no MonBus K-map sheet (MonBus appears only as the `MonBus out` contract sheet). Verdicts below are evaluated against the landed RTL in `projects/components/cache-ip/amber-mesi-l1/rtl/`.

### Verdict summary

| Sheet | Rows | IDENTICAL | RTL-REDUNDANT | RTL-DIFFERS |
|-------|------|-----------|---------------|-------------|
| `K-maps snoop CRRESP` | DT, PD, IS, WU | 0 | 4 | 0 |
| `K-maps snoop next-state` | next_state[1], next_state[0] | 0 | 2 | 0 |
| `K-maps amber control` | start_drain, start_fill, replay_now | 3 | 0 | 0 |
| **Total** | **9** | **3** | **6** | **0** |

No NEW differences were found that are not already covered by the known errata pinned in the plan and recorded in [`02_rtl_diff.md`](02_rtl_diff.md).

### `K-maps snoop CRRESP` (l1_snoop_kmap_test / l1_pkg)

Authority: HAS Table 3.0, implemented in `cache-ip/common-ip/rtl/includes/l1_pkg.sv` function `amber_snoop_crresp` and wrapped by `cache-ip/common-ip/rtl/fub/l1_snoop_kmap_test.sv` (validation-harness boundary, not instantiated in the design).

| Row | Verdict | Rationale / Review Focus |
|-----|---------|--------------------------|
| DT (DataTransfer) | **RTL-REDUNDANT** | Truth table matches the HAS Table 3.0 1-cells exactly for all reachable {state,snoop} combinations. The RTL expresses the map as a readable `case` decode over `{state,snoop}` rather than the QM-derived minimal SOP; reserved snoop codes (6/7) and the reserved `STATE_O` code are folded to the safe default `0` instead of being exploited as don't-cares. This is defensive coding: the adapter (`l1_snoop_resp`) routes illegal 4-bit ACSNOOP encodings to the reserved 3-bit code `3'b110`, and the kmap safe default prevents spurious data transfer on those paths (Review Focus 10: recorded gaps stay recorded). |
| PD (PassDirty) | **RTL-REDUNDANT** | Same case-decode implementation and truth-table match as DT. The RTL produces PD=1 only for M-state snoops that transfer data, matching Table 3.0. |
| IS (IsShared) | **RTL-REDUNDANT** | Same case-decode implementation and truth-table match as DT. Notably, M + CleanInvalid returns IS=1 per the corrected Table 3.0 (this was the discrepancy caught and fixed during the first-verdict TB bring-up). |
| WU (WasUnique) | **RTL-REDUNDANT** | Same case-decode implementation and truth-table match as DT. WU=1 only for E-state data-transfer snoops. |

### `K-maps snoop next-state` (l1_snoop_kmap_test / l1_pkg)

Authority: HAS Table 3.0 next-state column, implemented in `cache-ip/common-ip/rtl/includes/l1_pkg.sv` function `amber_snoop_next_state` and wrapped by `cache-ip/common-ip/rtl/fub/l1_snoop_kmap_test.sv` (validation-harness boundary, not instantiated in the design).

| Row | Verdict | Rationale / Review Focus |
|-----|---------|--------------------------|
| next_state[1] | **RTL-REDUNDANT** | Truth table matches Table 3.0 for all reachable {state,snoop} combinations. The RTL uses the same case decode as `amber_snoop_crresp`; reserved encodings fold to `STATE_I`. |
| next_state[0] | **RTL-REDUNDANT** | Same as next_state[1]. |

### `K-maps amber control` miss-path decision (l1_control)

Authority: MAS ch02_blocks/01, implemented in `cache-ip/common-ip/rtl/fub/l1_control.sv` (victim-drain / fill-start arbitration).

| Row | Verdict | Rationale / Review Focus |
|-----|---------|--------------------------|
| start_drain | **IDENTICAL** | RTL implements `kmap_start_drain = kmap_victim_dirty && !bypass_match`, which is exactly the workbook's proposed cover evaluated in `CTRL_MISS_VICTIM` where `hit == 0` by construction. The dirty-victim path gathers the line over `FILL_BEATS` port-A cycles and stages it into `l1_victim` (Review Focus 2: victim-buffer overflow is avoided by the single-outstanding invariant plus the leaf's `!victim_valid_q` guard; Review Focus 3: PassDirty/WB ordering is preserved because the victim buffer owns the line until `drain_done`). |
| start_fill | **IDENTICAL** | RTL implements `kmap_start_fill = !kmap_victim_dirty && !bypass_match`, exactly the proposed cover. |
| replay_now | **IDENTICAL** | RTL implements `kmap_replay_now = bypass_match`, exactly the proposed cover. On the CPU miss path `bypass_match` is constant-0 by construction (the pending-fill bypass lifetime is exactly `CTRL_MISS_FILL..CTRL_FILL_WRITE` of the single outstanding transaction), so this term is defensive; it is reachable on the snoop decision path when a snoop matches a pending fill (Review Focus 1: snoop-during-fill race resolved by answering from the bypass at the post-fill `pf_state`, with CD beats gated by `pf_data_valid`). |

### MonBus / address-decode sheets

The workbook does not contain K-map sheets for MonBus events or address decode. `MonBus out` is a contract sheet, not a K-map. The MonBus event map is verified by `cache-ip/common-ip/dv/tests/test_l1_monlite.py` against `l1_pkg` event codes and the MAS ch04 Table 4.1.1 emit points; Review Focus 5 (monlite perturbation) is embodied by `cache-ip/common-ip/rtl/fub/l1_monlite.sv`'s drop-and-count path, which never stalls the observed signals.

## Historical Verdicts

### Control-Sheet Verdict (2026-10-07, updated Task 4)

`l1_control` landed (Task 3, CPU path; Task 4, snoop service). Verdict for the `K-maps amber control` miss-path sheet (axes `{hit, victim_dirty, pending_bypass_match}`, outputs `{start_drain, start_fill, replay_now}`):

- **Truth-table equivalence: PASS at gate/func/full, both geometries** (tiny s16w2 + default s128w4). The RTL implements the workbook's PROPOSED cover literally, evaluated in `CTRL_MISS_VICTIM` where `hit == 0` by construction: `start_drain = victim_dirty & !pending_bypass_match`, `start_fill = !victim_dirty & !pending_bypass_match`, `replay_now = pending_bypass_match`. The two reachable cells are exercised by directed dirty/clean-victim misses and by the 10k-transaction randomized oracle-lockstep suite (`cache-ip/common-ip/dv/tests/test_l1_control.py`).
- **`pending_bypass_match` axis (2026-10-07 Task 4 update): now stimulus-reachable — driven on the snoop decision path.** With `CTRL_SNOOP` service live, the same pf registers feed the snoop reference-state resolution (bypass match → post-fill `pf_state` + `pf_data_valid`-gated CD beats). Directed classes `SnoopPendingFillBypass` (pre-RLAST snoop, CD stall until a late beat), `SnoopOtherLineMidFill` / `SnoopPostCommitApplies` (pf no-match → port-B installed-state decode), `ImStepPendingClearCorner` (repeat snoop with the invalidation pending), and `UpgradeNoBypassArm` (upgrade in flight: pf unarmed, snoop answered from the installed S entry) exercise both polarities of the axis plus the every-cycle `BypassNeverAnswersInvalid` invariant. On the miss path itself the axis remains constant-0 **by construction** — the pf register's lifetime is exactly `CTRL_MISS_FILL..CTRL_FILL_WRITE` of the single outstanding transaction and fills re-arm only after `CTRL_FILL_WRITE` clears it, so `CTRL_MISS_VICTIM` entry is exclusive with an armed bypass; the killed-upgrade re-fetch (`ImStepPendingClearCorner`, `UpgradeKilledByInvalidatingSnoop`) drives the full LOOKUP→MISS_VICTIM→MISS_FILL→FILL_WRITE→REPLAY re-lookup sequence with the axis at its constant-0 value. `replay_now` stays defensive-only.
- **SOP-literal diff against the QM-derived covers: NOT CHECKED**, same rationale as the snoop sheets (the RTL expresses the cover as named decision wires, not minimized literals; the meaningful diff is the truth-table one).

### First-Verdict Status (2026-10-06)

The first RTL slice landed: `l1_pkg` (the Table 3.0 decode functions `amber_snoop_crresp` / `amber_snoop_next_state`) and its module wrapper `l1_snoop_kmap_test`. Verdicts for the six snoop sheets (the four CRRESP maps and the two next-state maps):

- **Truth-table equivalence: PASS at gate/func/full.** The TB (`cache-ip/common-ip/dv/tests/test_l1_snoop_kmap.py`) carries an independent copy of HAS Table 3.0 and exhausts the reachable space at gate, adds the reserved encodings at func, and the whole 3-bit x 3-bit space at full. One real discrepancy was caught and resolved in the TB's favor of the documentation: Modified + CleanInvalid carries `IsShared=1` per Table 3.0.
- **SOP-literal diff against the QM-derived covers: NOT CHECKED, deferred.** The RTL implements the table as a case decode, not minimal SOP literals; the meaningful diff is the truth-table one above. Supplying `rtl_sop=` and re-deriving is deferred until `l1_snoop_resp` integrates this decode — if the integration restructures the logic, the literal diff would be repeated work.

---

**Last Updated:** 2026-10-11 (Task 14 verdict sweep)
