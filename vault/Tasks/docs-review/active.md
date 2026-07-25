<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# docs-review — Active (in progress)


### DONE 2026-07-25: common qc round_2 sent AND integrated

`round_1` was the shutdown-interrupted trial. It completed **two** units before
dying — not zero as the earlier note assumed. Rather than resume it, the round
was **abandoned in place** and all 6 units re-sent as `round_2`, because the CDC
move (`c0daf18a`) changed `rtl/common` *after* the round_1 bundle was built —
resuming would have mixed pre- and post-move ground truth inside one round.
round_1's two critiques are kept, superseded.

**round_2:** 6 units, 95 min, kimi-k3 direct, from a bundle rebuilt against the
post-CDC-move tree with a hand-regenerated `common_meta`. Results in
`~/rtl-doc-review/results/qc-kimi-k3/round_2/`. **32 findings** (27 CONFIRMED +
7 SUSPECTED, after the part_04 re-send).

**One unit came back truncated and was nearly missed.** `common_part_04` returned
2,586 chars against 10-12k for its siblings, cut off mid-expression, with
`finish_reason=length` and `budget_escalations: 0` — the ladder only escalated on
an *empty* body, so a truncated one was filed as success. Fixed in
`bin/review/kimi_client.py` (escalate on `finish=length` regardless of content,
mutation-checked); part_04 re-sent and returned 9,129 chars with **5** findings
instead of 2. See [[kimi-review-rounds]] rule 4.

**Integration measured, not assumed** (rule 6): of the 22 doc files round_2
implicates, 21 have been touched since the round was sent. The one untouched
(`dataint_crc.md`) is the single finding **rejected as a false positive** — the
reviewer claimed CRC-64/ECMA-182 needs init/xorout = FF..; computed, the doc's
init=0/xorout=0 yields 0x6C40DF5F0B497347, which IS the published ECMA-182 check
value (0x62EC59E3F1A4F00A is CRC-64/WE). Commits: `2a9b4524`, `61d291da`,
`c1ee2240`, `12a4a1fa`.

**The one that mattered most.** `shifter_lfsr_fibonacci.md`'s entire polynomial
table was wrong — tap sets copied from the XNOR/left-shift table in
`shifter_lfsr.sv`, which encodes the same polynomials differently for this
module's XOR/right-shift structure. Every row drove the register to zero, where
the `|r_lfsr` guard freezes it. Measured: WIDTH=4 taps [4,3] locks in ONE step.
Both LFSR modules now carry their own 168-width table in the RTL header, so
neither invites a copy from the other. No follow-up outstanding.

**Next:** the `humanize` pass on common is now unblocked (correctness integrated
first, per the rule). Not started.

## DOCREV-001 — Integrate the outstanding Kimi accuracy findings

### Progress by area

| Area | Units | State |
|---|---|---|
| **common** | `common_part_01..05` + `common_meta` (re-reviewed 2026-07-25 after the CDC move) | ✅ **DONE 2026-07-25** — 21/22 implicated files touched; the 22nd is a rejected false positive |
| **math** | `math_part_01/02/03` (r2) | ✅ **DONE 2026-07-24** — 16 CONFIRMED fixed, 5 SUSPECTED all bundle-scope false positives; docs live in RTLMath now |
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

### math — DONE (2026-07-24)

**Where the files are.** The RTL moved to `rtl/math/` (171) and tests to
`val/math/` (119) before this review; the docs moved to
`docs/markdown/RTLMath/` on 2026-07-23 (DOCREV-006, closed). **The findings
still cite the pre-split paths** — `rtl/common/math_*.sv` and
`docs/markdown/RTLCommon/math_*.md` — and that is deliberate: they are reviewer
evidence and must not be rewritten. Both are 1:1 renames, so translate as you
read: `RTLCommon/math_X.md` -> `RTLMath/math_X.md`.

**Counts:** 23 findings — `math_part_01` 9 (8 CONFIRMED), `math_part_02` 8
(6 CONFIRMED), `math_part_03` 6 (4 CONFIRMED). 16 docs implicated, all present.

**DONE (2):** both `math_part_03` subtractor findings. `math_subtractor.md`
documented `i_b_in`/`ow_d`/`ow_b` for `math_subtractor_ripple_carry`, whose RTL
declares `i_borrow_in`/`ow_difference`/`ow_carry_out` — all six instantiations
on the page were uncompilable. `math_subtractor_carry_lookahead` shares the
wrong input name and exposes each output twice (`ow_d`/`ow_b` are aliases of
`ow_difference`/`ow_borrow_out`), which the page documented nowhere. Fixed,
split into two port tables, and verified by compiling both corrected port lists
under `verilator --lint-only`. `math_subtractor_half`/`_full` were checked and
are correct — not "fixed" to match the others.

**REMAINING (21), by doc:**

| Doc | Findings |
|---|---|
| `math_bf16_multiplier.md` | 3 CONFIRMED — special-case priority order contradicts RTL; "RNE rounding" claimed but logic does not do it; NaN prose says sign=0 while RTL and the page's own code block preserve it |
| `math_library.md` | 2 CONFIRMED — overgeneralised integer-core reuse claim; incomplete Brent-Kung module list |
| `math_adder_basic.md` | 1 CONFIRMED (half-adder "Parity Generator" example is structurally illegal SV) + 1 SUSPECTED (modules documented with full tables that may be absent) |
| `math_multiplier_wallace_tree.md` | 1 CONFIRMED (csa variant: final CPA cell is not `math_adder_full`) + 1 SUSPECTED (speed column) |
| `math_prefix_cell_gray.md` | 1 CONFIRMED (Brent-Kung reverse-tree gray cells "never" claim) + 1 SUSPECTED (cites `math_adder_brent_kung_grouppg_008.sv`) |
| `math_adder_carry_save.md` | 1 CONFIRMED — says CSA carry must NOT be shifted |
| `math_adder_brent_kung.md` | 1 CONFIRMED — three different forward/reverse depth formulas |
| `math_addsub.md` | 1 CONFIRMED — "2N+2 levels" vs its own 17-level total for N=8 |
| `math_adder_pg_chain.md` | 1 CONFIRMED — width guideline wrong at the minimum |
| `math_bf16_adder.md` | 1 CONFIRMED — special-case priority code is an incomplete quote |
| `math_bf16_fma.md` | 1 CONFIRMED — pseudocode omits RTL branches, yields -0 |
| `math_fp8_modules.md` | 1 CONFIRMED — E5M2 "~6e-8" unattainable in the format |
| `math_multiplier_dadda_4to2.md` | 1 CONFIRMED — component counts, stage-savings, worked example |
| `math_bf16_extended.md` | 1 SUSPECTED — five catalog pages document ~117 modules vs the bundle |
| `math_multiplier_basic.md` | 1 SUSPECTED — `math_multiplier_carry_save` documented, no RTL in bundle |

**Method reminder:** the token-presence heuristic that worked for common gives
false readings here (it called 20 of 23 "likely integrated" when none were).
Read each finding and check it against `rtl/math/` directly. Several SUSPECTED
ones are "not in the RTL bundle" claims — the reviewer could not see the
filesystem, so check whether the module exists in `rtl/math/` before acting.

**Math follow-ups surfaced during integration (both potential RTL, not doc):**
- **carry_save reduction, multi-level tree examples.** The single-stage doc
  taught the reduction backwards (carry NOT shifted); fixed. The multi-level
  CSA-tree examples on the same page chain carries unshifted too, which is also
  wrong, but correcting the tree wiring needs sim-verified width/shift
  bookkeeping. Flagged in the doc; needs a verified rewrite.
- **BF16 multiplier rounding.** Documented as RNE, but the implemented boolean
  is `R & (G|S|LSB)` (mantissa_mult folds guard into sticky), not textbook RNE
  `G & (R|S|LSB)`. Documented the actual boolean; whether this is an RTL
  rounding defect or intended needs an owner decision — triage before the final
  round.
