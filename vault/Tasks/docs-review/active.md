<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# docs-review — Active (in progress)

## DOCREV-001 — Integrate the outstanding Kimi accuracy findings

### Progress by area

| Area | Units | State |
|---|---|---|
| **common** | `common_part_01..05` (r1+r2) + the `rtl/common` findings inside `cdc_part_01` | ✅ **DONE 2026-07-23** — measured, not assumed |
| math | `math_part_01/02/03` (r2) | ⬜ not started — 13 CONFIRMED cite `rtl/*.sv` |
| shared | `shared_part_01..04` (r2) | ⬜ not started — 13 CONFIRMED in part_02 alone |
| monitor | `monitor_part_01..06` (r3) | ⬜ not started — 70 CONFIRMED, largest block |
| apb / apb5 | `apb`, `apb5` (r2) | ⬜ not started — 6 CONFIRMED cite `rtl/*.sv` |
| axi4 / axi5 / axil4 | (r2) | ⬜ not started |
| axis4 / axis5 | (r2) | ⬜ not started |
| **cdc** | `cdc_part_01/02` (r2) | ✅ **DONE 2026-07-23** — all 13 findings |

**cdc, 2026-07-23.** All 13 findings across both units worked. `cdc_part_01`:
six `RTLCommon` findings (five already covered, the phantom `synchronizer`
fixed) plus three on `RTLAmba/cdc/cdc.md` — `johnson2bin` was documented as
"registered" when it is purely combinational (the three `always_ff` in its
source are all inside comments), which made both flop-cost walkthroughs wrong:
512-bit 144 -> **132** flops (+96 -> **+84**), depth-36 244 -> **230** (+188 ->
**+174**), and the ratios 64:1 -> 73:1 and 76:1 -> 82:1. The 4-phase latency
figures were tied to `SYNC_STAGES` instead of asserting fixed clock counts.

One finding was **inverted** — it claimed the doc's `test_fifo_buffer_async.py`
pointer was wrong because the RTL headers say `test_fifo_async.py`. The
filesystem settles it: `test_fifo_buffer_async.py` exists, `test_fifo_async.py`
does not. The doc was right and `fifo_async.sv`'s header was stale; fixed the
RTL comment. Reviewers state the direction confidently and can have it
backwards — check the tree, not the two texts against each other.

`cdc_part_02` (all four on the apb5 CDC pages). The DEPTH=6 one turned into an
**RTL fix, not a doc fix** — and the first attempt at it was wrong in an
instructive way. The finding said "DEPTH=6 is documented legal but fails
elaboration", so the obvious move was to narrow the documented range to
{2,4,8}. That makes the doc agree with the RTL by promoting a limitation to a
specification. Sean's call: DEPTH=6 should *work*. The constraint was never
DEPTH — it was `apb5_slave_cdc` hardcoding an encoding. It derives
`CDC_FIFO_DEPTH = max(DEPTH,4)` into two Gray-mode `gaxi_fifo_async` instances,
and Gray only closes on a power of 2; `gaxi_fifo_async`'s own `$error` even
says "Set USE_JOHNSON=1 for arbitrary depths". The wrapper never plumbed the
parameter. Now exposed (`0` Gray / `1` Johnson / `-1` auto, default auto) on
both the cmd and rsp FIFOs, so power-of-2 builds keep Gray unchanged and 6
auto-selects Johnson. `USE_JOHNSON=0` with `DEPTH=6` remains an elaboration
error by design — the default resolves an unexpressed choice, it never
overrides an expressed one. See commit `bfa905db`.

Also in `cdc_part_02`: the one-sided-reset section claimed safety that
does not exist (the crossed pointer copy is a LIVE synchronizer, so a one-sided
reset re-presents commands and can fabricate responses rather than discarding
cleanly); `parity_error_wdata/ctrl` were grouped with the aclk backend but are
combinational pclk-domain pulses (stale RTL port comment corrected too); and
`CG idle=16` is unreachable at the default `CG_IDLE_COUNT_WIDTH=4`, where 16
truncates to 0.

An area is DONE only when its findings have been checked against the tree, not
when a commit says so. See the common entry below for what that involved.

**Status:** 🟡 active 2026-07-23 — **`common` is DONE and verified across ALL rounds**
(see "Common: measured complete" below); AMBA/monitor, math, shared, apb/axi*,
cdc remain. Previously read: all 5 round_2 `common_part_*` units integrated;
the AMBA/monitor and math units of round_2, plus round_3 (monitor), remain.

**Integrated so far — round_2 common (all five parts), 2026-07-23:**
- `common_part_01` (14 confirmed + 2 suspected): the
  `arbiter_round_robin_simple` starvation bug (RTL, see COMMON-012) plus doc
  fixes to bin_to_bcd (latency formula + two worked examples), arbiter_round_robin
  (rotation direction, dead-logic LUT), arbiter_round_robin_weighted (consecutive-
  grant myth, deadlock-prone masking snippet, MAX_LEVELS range), cam_tag
  (lowest-not-highest alloc, phantom debug block), clock_divider (constraint,
  baud example), overview (broken adder example, unsourced power claims).
- `common_part_02` (8 confirmed) + **RTL**: clock_pulse counter re-sized to
  $clog2(WIDTH) (was WIDTH bits -> unsynthesizable heartbeat), clock_gate_ctrl
  port de-referenced the body localparam N; doc fixes to counter_johnson
  (NOT self-starting), clock_pulse (registered-pulse phase, formal props,
  pipelined variant), clock_gate_ctrl (N is derived), counter_bin (MAX range),
  counter_load_clear (load-during-count diagram, count_bounds caveat).
- `common_part_03` (14 confirmed; F15 was a FALSE POSITIVE — file exists at the
  documented path): dataint_crc (phantom ALGO_NAME, broken basic example,
  CRC-64/ECMA recipe), fifo_control (truncating cast), fifo_sync/fifo_async
  (phantom INSTANCE_NAME + sim checks, MEM_STYLE/USE_JOHNSON, write guard),
  counter_ring, debounce, decoder, ECC DEBUG no-ops; plus stale fifo RTL header
  comments.
- `common_part_04` (11 confirmed + 1 suspected) + **RTL**: pwm repeat-count
  off-by-one (emitted N+1 periods); doc fixes to johnson2bin (two decode
  examples + all-ones case + fill direction), pwm sync_rst_n, three phantom
  INSTANCE_NAME params, shifter_lfsr + shifter_lfsr_galois worked sequences,
  glitch_free_n_dff_arn (async reset, MTBF direction), leading_one_trailing_one
  (deterministic-0 indices), icg (unsourced power %).
- `common_part_05` (4 confirmed + 2 suspected): sort (reset polarity ×2,
  NUM_VALS range, gate-delay claim, O(1)->O(n^2) hardware area), sync_pulse
  (latency over-count, MTBF constant); plus sort.sv/sync_pulse.sv RTL header
  comments (wrong sort direction; phantom ready-feedback path).

The RTL-side fixes above were verified with clean-rebuild tests
(test_clock_pulse, test_clock_gate_ctrl, test_pwm all green) and lint; see
vault/Tasks/common/closed.md (COMMON-013).

The remaining round_2 units (AMBA/monitor, math, shared, apb/axi*, cdc) and
round_3 (75 findings, 70 CONFIRMED, monitor) are un-integrated. Verified by
measurement, not commit history: `axi4_master_rd_mon_cg.md` still documents five
clock-gating parameters that do not exist.

Critiques and a checkbox index: `docs/review/kimi/` (`FINDINGS.md` leads with a
most-implicated-files table, which is the work-planning view).

**Trap to avoid:** `92fbd051 docs(amba/monitor): reconcile all monitor
documentation with the RTL` landed 06:55 on 2026-07-22 and reads like an
integration pass. round_3 was sent at 13:06 the same day, reviewed the
post-reconcile docs, and still returned 70 confirmed defects. A reconcile
commit is not evidence a round was applied.

**Not all of these are doc bugs.** Several are RTL defects surfaced by
documentation review (the arbiter rotate direction is the clearest). Triage
into doc-fix vs RTL-fix before batching the work, and file the RTL ones in the
owning area's task page.

Per handbook rule 5 ([[kimi-review-rounds]]): verify each finding against the
RTL before acting. Reviewers report wrong things confidently when a unit was
mis-packaged.

round_1 (68 findings) is pre-reorg and superseded by round_2 — do not work it.
**This was verified 2026-07-23, not assumed** — see below.

### Common: measured complete (2026-07-23)

Measured against the tree per [[kimi-review-rounds]] rule 2, not inferred from
commit history. Every finding in every `common_part_*` unit in **all three
rounds** was parsed and its disputed claim checked against the live docs:

| Round | Units | Findings | Disputed text still present |
|---|---|---|---|
| round_1 | common_part_01/02/03/05 | 38 | 0 (4 flagged, all false positives) |
| round_2 | common_part_01..05 | 54 (48 CONFIRMED, 6 SUSPECTED) | 0 (4 flagged, all false positives) |
| round_3 | — | no common units | — |

The false positives all share one shape worth remembering: the flagged token
appears in the **correction**, not the error. `fifo_sync.md` and `fifo_async.md`
both contain the string `INSTANCE_NAME` — inside the sentence "there is no
`INSTANCE_NAME` parameter". A naive presence check calls that unintegrated.
Confirm by reading the surrounding text before reopening a finding.

Also re-verified independently rather than trusting the closure note:
`arbiter_round_robin_simple` (COMMON-012) is genuinely fixed AND its test
genuinely catches the bug — mutating the rotation back to the pre-fix form
makes the suite go RED (1 failed), restoring makes it GREEN (5 passed).

**Common-area findings that do NOT live in a `common_part_*` unit.** The review
bundles were assembled BY TOPIC, not by directory, so ~19 CONFIRMED findings
landing on `rtl/common` sit under other unit names — which is exactly why they
were missed:

- `cdc_part_01` (6 CONFIRMED, 3 SUSPECTED) cites `rtl/common/`
  **clock_pulse, fifo_async, glitch_free_n_dff_arn, johnson2bin** plus
  `bin2gray` / `counter_bingray` docs. Note `rtl/amba/cdc/` also exists
  (the 2-/4-phase handshakes, open-loop, synchronizer) — the unit spans both
  areas.
- `shared_part_02` (13 CONFIRMED) cites `rtl/common/`
  **clock_gate_ctrl, dataint_crc**.
- `cdc_part_02` (3 CONFIRMED, 1 SUSPECTED) touches no `rtl/common`.

**Their common-touching findings were then worked and are DONE (2026-07-23).**
Checked each of `cdc_part_01`'s six `RTLCommon` findings against the tree; five
were already covered by the `common_part_*` integration and needed nothing:

- glitch_free_n_dff_arn "synchronous" reset -> already reads **Asynchronous**
- glitch_free_n_dff_arn "further reduces MTBF" -> already reads **increases**
- clock_pulse resource table -> already `$clog2(WIDTH)`, with an explicit
  "NOT WIDTH bits" note (the RTL fix in COMMON-013 made the doc correct)
- clock_pulse formal properties -> already `|=>` with a comment explaining the
  registered pulse, and `$past()` on the converse property
- johnson2bin worked examples -> already corrected

One was real and is now fixed: the **phantom `synchronizer` module**. No module
of that name exists in `rtl/` — the library has `cdc_synchronizer`
(`async_in`/`sync_out`, in `rtl/amba/cdc/`) and `glitch_free_n_dff_arn`
(`d`/`q`, in `rtl/common/`). Four instantiations across `bin2gray.md` and
`counter_bingray.md` used the phantom name with invented `data_in`/`data_out`
ports, so none of those examples compiled. Repointed all four at
`glitch_free_n_dff_arn` (kept in `rtl/common` so a common-library example does
not reach into amba) with correct ports and `FLOP_COUNT(2)`.

Verified by lint, not by inspection: a wrapper instantiating the corrected form
elaborates clean under `verilator --lint-only -Wall`. The one remaining warning
(`flat_r_q` unused) is pre-existing inside `glitch_free_n_dff_arn.sv` itself.

`shared_part_02`'s findings all target **RTLAmba** docs (`amba_clock_gate_ctrl`,
the master characterization blocks) and merely cite `rtl/common` modules as
evidence — they are shared-pass work, not common.
