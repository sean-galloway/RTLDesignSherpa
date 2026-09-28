# TASK-015: test the DUT across configurations — a 4-layer plan with a coverage number

**Status:** CLOSED 2026-09-28  **Priority:** P2 — this is the systemic answer to
[[BUG-003]]; without it the next default change is the next excavation

Sean, 2026-09-26, after BUG-003 was found by accident: *"Are there another 50
bugs laying dormant in the rtl right now??? How do I tell????"* and *"come up
with a solid plan to test the dut under many different configurations"*.

## Diagnosis: why the existing suites could not have caught BUG-003

Two good suites with complementary blind spots, and the bug lived in the seam.

**`dv/tests/top/test_pumice_top.py` is STIMULUS-rich and CONFIG-poor.** It
parametrizes 17 stimulus axes -- `gap` {0,8,13,15}, `rd_gap` {0,4,8,15}, `blen`,
`geom`, `rdlat`, `trefi`, `depth`, `offset`, `nbeats`, strobe patterns, producer
profiles, engine counts, id modes -- and **zero config fields**. Every run takes
the CSR reset values for the whole page/scheduling/refresh surface.

**`build-perf/host/pumice_char.py` is CONFIG-rich and ORACLE-poor.** ~40 named
configs cross the three mode axes, but it runs against the DFI loopback, which
models no DDR2 page timing, so it cannot rank anything on performance; its checks
are data integrity plus command telemetry. It also sweeps only gap=0 and gap=8.

**So no suite ever crossed a config axis with a hazard stimulus axis.** BUG-003
is exactly that crossing: `policy_mode=3` x `rd_gap>=8`. Note `policy_mode` was
already exercised with 3 distinct values -- single-field config coverage would
have reported it GREEN.

**And the reset was never the tested config.** That is the systemic hole: the
top suite runs resets, the char suite programs everything, and the values the top
suite actually runs were never a deliberate choice.

## The space, measured

| | count | note |
|---|---|---|
| software-writable CSR fields | 67 | from `pumice_csr.rdl` |
| mode selectors (<= 3 bits) | 15 | `policy_mode`, `order_mode`, `prio_sub`, `row_sel`, `col_sel`, `access_pref`, `qos_en`, `policy_scope`, `page_policy_or`, `hash_en`, refresh `mode`, `gear_ratio`, `rd_phase`, `wr_phase`, `memtype` |
| value fields (> 3 bits) | 49 | timings, thresholds, intervals |
| naive cross product of mode selectors alone | **536,870,912** | why it was tested at one point instead |
| fields never mentioned in any DV or host code | 4 | `pasr_banks`, `pasr_segs`, `init_timeout_ms`, `zq_retries` |
| fields with <= 1 distinct value ever written | 30 | ~half the surface exercised at one point |

Exhaustive is impossible; that is not the goal. **2-way coverage is the goal**,
because every defect of this class on record in pumice is a 2-way interaction.

## The hazard axis, from history

Three independent defects, one stimulus knob:

| defect | trigger |
|---|---|
| PUMICE-037 | concurrent R/W corruption at **gap >= 8**, clean 0-7 |
| PUMICE-042 / [[TASK-007]] | write-watermark stalls at **gap 1, 3, 4, 11, 15** |
| [[BUG-003]] | read-return ring loses a ticket at **rd_gap >= 8** |

3 for 3. A non-zero gap deasserts RREADY mid-return and creates stall/idle
windows, and those windows are where accounting races live. **Gap is a mandatory
axis in every layer below**, not one option among many.

## HARD REQUIREMENT (Sean, 2026-09-26): every config tested in sim is ALSO tested on the board

Not a nice-to-have. Two independent reasons, both learned the hard way in
[[TASK-013]] and [[BUG-003]]:

1. **Sim cannot rank performance.** The DFI loopback models no DDR2 page timing,
   so no paging or scheduling policy can be ordered by bandwidth there.
2. **Sim and board DISAGREE ABOUT MECHANISM.** `adapt_access` converted ~54% of
   activations in sim and ~3% on the board on nominally identical stimulus. A
   sim-only result about a config is therefore not evidence about that config.

**The cost objection does not survive measurement -- the board is CHEAPER:**

| | per cell | ~384 cells |
|---|---|---|
| sim (`adapt_rowmix_2x2`, 4 configs, 215 s) | ~54 s | ~5.8 h at -n 16 |
| **board** (same profile, 16.3 s) | **~4 s** | **~26 min** |

The board is ~13x faster per cell because there is no elaboration or compile.
So board parity costs minutes, not days. It is nearly free and it is mandatory.

This is already structurally possible: `pumice_char.run_profile()` is THE SAME
CODE in both environments ([[project_ddr2_char_sim_equivalence]]) -- the only
intended difference is `txn_scale`. The covering array must therefore be defined
once and run through both harnesses, and a cell is not "covered" until both have
run it.

**Oracle asymmetry, and why both are needed:**

| | assertions | integrity | telemetry | bandwidth |
|---|---|---|---|---|
| sim | YES (`ifndef SYNTHESIS`) | yes | yes | meaningless |
| board | **NO** | yes | yes | YES |

Sim is the only place the accounting assertions fire (BUG-003 was caught there
while the board data check PASSED). The board is the only place bandwidth means
anything. Neither is sufficient; a config needs both.

## COROLLARY, and it may explain the 54%/3% divergence: make the two configs MATCH

The requirement above is "run everywhere". This is the stronger sibling: **the
DUT configuration must be IDENTICAL in both**, and today it is not.

    ddr2_char_framework/dv/tests/test_ddr2_char_char.py:  FPGA_CLK_HZ = 100_000_000
    board:                                                75 MHz (BUILD_CLK_HZ)

JEDEC timings are specified in ns and converted to CYCLES, so at 100 MHz every
timing is **1.33x more cycles** than at 75 MHz. That changes arbiter behaviour
directly: longer gaps in cycles -> more idle windows -> rows evicted after fewer
column ops -> mode 5's counter (which keys on exactly "<=1 column op per
activation") sees the close-friendly condition far more often.

**So the "54% in sim vs 3% on board" comparison in [[TASK-013]] was never
apples-to-apples** -- it compared a 100 MHz DUT against a 75 MHz DUT and
attributed the difference to simulation-versus-silicon. This is the exact failure
[[feedback_sim_match_fpga_exactly]] warns about.

UNVERIFIED but cheap to settle: run the char sim at 75 MHz and re-measure
`adapt_access` conversion. If it falls toward 3%, the divergence is explained and
mode 5 is simply clock-sensitive, not mis-plumbed. **Do this before any further
work on [[TASK-014]]'s mode-5 rework**, because the rework's premise
("close_pred_o does not assert on hardware") may be an artefact of the clock
mismatch rather than a defect.

Action: add an env override for `FPGA_CLK_HZ` in the char sim, default it to the
board's 75 MHz, and make the reset-parity gate (Layer 0) cover clock and derived
timings too -- not just CSR fields.

## Layer 0 — reset parity gate (do this first; it is the cheapest and it closes the class at source)

A checker, in the pre-commit gate, that asserts for every `sw=rw` field one of:

1. the field's reset value is what the top suite actually runs, **or**
2. the field is explicitly named in a sweep list with >= 2 values, **or**
3. the field is on a written waiver list with a reason.

Then **change the reset to the configuration you actually want to ship**, and the
tests follow automatically. BUG-003 existed only because those two diverged.

Deliverable: `bin/check_csr_reset_parity.py`, reading `pumice_csr.rdl` for resets
and the sweep manifest from Layer 1. Cost: a day. Catches: the whole "field
resets to a disabling value and nothing ever writes it" family -- which is 5 of
the 6 defects in this class already on record ([[TASK-011]] RBL
`reset_interval=0`, [[TASK-013]] `check_interval=0` and the missing
`tr_min/max/step` accessors, [[TASK-007]] watermarks reset to disabled, board
tCCD unprogrammed).

## Layer 1 — pairwise config covering array x hazard axes (the main new capability)

**Not** the cross product. A pairwise covering array over the 15 mode selectors
needs roughly `max(domain)^2` vectors -- order **40-64 config vectors**, not
536 million -- and every 2-way combination appears in at least one of them.

    configs:   ~48 covering-array vectors over the 15 mode selectors
    x gap:     {0, 4, 8, 15}          <- mandatory, see hazard axis
    x direction: {read-only, concurrent R/W}
    = ~384 cells

At the observed ~1-3 min per cell that is 6-19 h serial, or **under 2 h at
`-n 16`** -- a nightly run, not a gate.

Build it on what exists, do NOT fork a new TB
([[feedback_use_existing_cocotb_infra_only]]):

* the config vector programs through `ControllerConfig.apply()` in
  `pumice_char.py`, which already writes every mode field on every config
* the stimulus comes from the top suite's existing generators and its `gap` /
  `rd_gap` parametrization
* the runner is a new `RUN_PROFILES` entry plus a pytest parametrization over the
  covering array, generated by a small script so the array is reproducible

Report the coverage as a NUMBER: *"N of 105 mode-selector pairs exercised at
each of 4 gaps"*. That is what replaces "are there another 50?" with an answer.

## Layer 2 — invariant oracles, so a sweep can FAIL and not merely run

A config sweep is worthless without an oracle, and on the loopback there is no
performance oracle. Two sources, both cheap:

**(a) Accounting assertions.** BUG-003 was caught by an RTL assertion
(`pumice_rd_return_ring.sv:273`) -- **the board data check PASSED on the same
stimulus.** There are only 15 assertions across 6 of ~40 RTL files, and they sit
exactly where they pay: rings, CAMs, the history checker. Extend them to the
remaining accounting sites: write-data CAM occupancy, the DFI CDC FIFO
level, refresh credit counters, bank-timer `r_ap_pending`.

> **DECIDED 2026-09-27 (Sean): no assertions in RTL. Layer 2a is DROPPED.**
> The standing rule stands without exception -- `vault/handbook` records *"No
> assertions in RTL -- they break some tools; properties go in external formal/
> blocks, never in the module."* No new accounting assertions are to be added to
> any pumice FUB. The `ifndef SYNTHESIS` carve-out proposed above was declined.
>
> What this costs, recorded so nobody re-argues it from the benefit side alone:
> the detector that caught BUG-003 (`pumice_rd_return_ring.sv:273`) is the kind
> of check this rule forbids, and it cannot move to formal --
> `reference_formal_internal_visibility` records that binds on PeakRDL blocks see
> **only ports**, so an internal invariant like "issue_q must be non-empty when a
> return beat lands" is not checkable there. The detection burden therefore falls
> entirely on **Layer 2b**, which is sim-side arithmetic on already-exported
> counters and breaks no tool. 2b is no longer merely "what makes the rest
> meaningful" -- it is the only oracle this plan gets.
>
> OPEN: the 15 assertions already present in 6 RTL files predate this ruling.
> Whether they are grandfathered or removed is not decided here.

**(b) Telemetry invariants**, checkable in sim with no performance model. These
hold for EVERY config and are pure arithmetic on counters already exported:

    ACT                 <= col_ops
    hit + miss + empty  == ACT
    PRE                 <= ACT + PREA           (cannot close more than opened)
    ring occupancy      <= RD_RET_DEPTH at all times
    returned beats      == issued read beats    (the BUG-003 invariant, at the host)
    stall buckets       sum to <= window cycles

Any config that violates one is a bug regardless of bandwidth. This is the layer
that turns the sweep from "it ran" into "it passed".

## Layer 3 — seeded random config soak (the long tail)

Random legal config vectors x random stimulus, replayable via the existing
`RDS_SEED_BASE` mechanism ([[project_seed_rerun_masks_failures]]). Nightly or
on-demand, never in the gate. Its job is the 3-way-and-beyond interactions that
the covering array cannot reach by construction. Log every failing seed as a new
pinned regression cell.

## Order, cost, and what each layer buys

| layer | cost | buys |
|---|---|---|
| 0 reset parity gate | ~1 day | the whole "disabling reset nobody writes" family, permanently, at commit time |
| 2b telemetry invariants | ~1 day | an oracle, without which layers 1 and 3 cannot fail |
| 1 pairwise array | ~3 days | all 105 2-way mode interactions x 4 gaps, with a coverage number |
| ~~2a more assertions~~ | **DROPPED 2026-09-27** | no assertions in RTL; the rule stands without exception |
| 3 random soak | ~2 days | 3-way and deeper; a growing corpus of pinned seeds |

**Do 0 and 2b first**, and with 2a dropped they are the whole detection story.
Layer 0 is the highest value per hour and needs no decision from anyone; 2b is
the only oracle the plan has left.

**Layer 1 is partly built already.** `dv/tests/macro/test_pumice_sched_matrix.py`
crosses the 12 named operating points in `dv/tbclasses/pumice_dram_configs.py`
against 7 paging arms x 8 patterns -- 672 arms, 1,376,256 requests, 3,151,054
commands, 0 violations at FULL. That covers the config x hazard crossing AT THE
SCHEDULER LAYER with the JEDEC command-stream checker as its oracle. What Layer 1
still owes: the same crossing at `top` with a covering array and a stated
coverage number, and the value fields (the 49 non-mode CSRs) which the matrix
does not vary.

## What this plan will NOT catch, stated plainly

* **Performance regressions.** The loopback models no page timing, so no sim
  layer can rank paging or scheduling policies. Every bandwidth claim still needs
  the board ([[TASK-013]] is the worked example -- 60% of activations converted in
  sim, 3% on hardware, on identical stimulus).
* **Silicon-timing-dependent behaviour.** BUG-003's board run returned clean data
  at gap=8 where sim asserts. The board has no `ifndef SYNTHESIS` check, so
  hardware "passing" is weaker evidence than a sim assertion.
* **Anything gated on a value field's magnitude** (tRCD, TR, watermarks) unless
  that field is added to the array as a small enumerated set. The array covers
  mode SELECTORS; value fields need chosen representative points, and BUG-003 was
  TR-magnitude sensitive, so pick those points deliberately.

Related: [[BUG-003]] (the defect that motivated this), [[TASK-013]] (the campaign
that surfaced it), [[TASK-011]] and [[TASK-007]] (two more of the same class),
[[feedback_parameter_off_state_needs_its_own_test]] (a parameter's OFF state
needs its own test -- this plan is that rule made systematic).

---

## Delivered 2026-09-27: layers 0 and 2b

**Layer 0 -- reset parity.** `bin/check_csr_reset_parity.py` (213 lines) plus the
manifest `dv/csr_reset_parity.py`. All **73** `sw=rw` fields are now a written
decision: 3 `swept` (with `by=` the artifact, `drives=` the RTL port it moves,
and `oracle=` what fails if a value is wrong), 55 `ships` (the reset IS the
shipping value), 15 `waived` (7 CTRL command strobes, 8 `OBS_ROW_HIT` counters
that are `rw` only because a write clears them). Registered in
`bin/hooks/pre-commit` on `.rdl` / manifest / regmap edits. Tested by
`bin/tests/test_check_csr_reset_parity.py` -- 15 tests, one per rule, each
proven by mutating a fixture until the rule fires, plus a guard that the real
pumice manifest passes and covers every writable field.

The `oracle=` requirement is the load-bearing one. A CSR read/write walk touches
every field with two values and proves nothing about behaviour, so a `swept`
claim that cannot name what breaks is not a sweep.

**What the gate found on its first run**, which is the whole return on it:

* `PHY_TIMING.t_phy_wrlat` reset to **0** while BOTH board host paths program
  **1**. Reset changed to 1.
* `PHY_TIMING.t_rddata_en` reset to 6, and the two host paths disagree --
  `init` (`pumice_master.SimpleTest`) programs 6 with `rddata_delay=7`, the
  ILA-validated tuple, while `pumice_char.ControllerConfig` programs 1 with
  `rddata_delay=2`. Both sit on the measured clean diagonal
  `rddata_delay = t_rddata_en + 1`. Filed as [[ISSUE-015]]; the reset follows
  `init`. **I changed this reset to 1 first, on ControllerConfig alone, before
  reading what `init` actually programs** -- one host default is not evidence of
  the shipping value, and the gate cannot tell you which of two callers is
  authoritative.
* Two false alarms from the checker itself, both fixed: a textual `sw = rw`
  count does not equal the elaborated field count (`OBS_ROW_HIT` is one reg
  definition instantiated 8 times, so 66 declarations become 73 fields) -- that
  miscount failed the gate against a perfectly current regmap, and staleness is
  now left to `bin/check_rdl_regen.py`, which already owns it. And a sweep that
  drives an RTL port rather than the CSR field name needs `drives=`.

Clock parity is in the manifest (`CLOCK`: 75 MHz, the env var and the file that
declares it), closing the TASK-013 hole where a 100 MHz sim was compared against
a 75 MHz board and the difference blamed on silicon.

**Layer 2b -- telemetry invariants.**
`dv/tbclasses/pumice_telemetry_invariants.py`: five relations over the exported
counters, family-neutral, with `arming()` so a rule that never had its counters
cannot contribute to a clean verdict and `assert_clean(require=...)` refusing a
vacuous pass. Nothing in sim read these counters before this -- the telemetry was
exported and only the board host ever looked at it.

Consumers: `dv/tests/fub/test_pumice_telemetry_invariants.py` (15 unit tests),
`dv/tests/top/test_pumice_top.py::cocotb_test_telemetry_invariants` (real
counters over three per-pattern windows at proven quiescence), and on the board
`projects/fpga-systems/NexysA7/pumice/bin/seq_telemetry.py` -- the SAME module
in both places. Layer 0 gets a board sequence too, `seq_reset_parity.py`, which
reads every `ships` field back over UART before `init` touches anything: the
file-level gate cannot speak for what the flops in the part come up holding.

**TASK-015's drafted invariant was wrong and correct hardware disproved it.**
The draft says `hit + miss + empty == ACT`. `PAGE_STATS_HIT` does not count hits
-- the RTL bumps it on every column op and the RDL says so at the field -- so the
relation that holds is `miss + empty == ACT`, and it held EXACTLY in every
measured window (1+47=48, 0+64=64, 1+48=49). Two further drafted relations,
`ACT <= col_ops` and `col_ops - ACT >= 0`, are violated by correct hardware:
under a background-close mode a row can be opened, timed out and reopened before
its column command issues. Measured -- a bank-spreading pattern gave 49 ACTs for
48 column ops while two other patterns gave exactly 48/48 and 64/64. Replaced
with the bounds that hold, and the consequence for the RDL's documented
`hits = col_ops - ACT` derivation is [[ISSUE-014]].

Layer 2a is DROPPED (no assertions in RTL). Layer 1 is partly built. Layer 3
untouched.

---

## Delivered 2026-09-28: layers 1 and 3 (task COMPLETE)

**Layer 1 -- pairwise covering array x hazard axes.**
`dv/tbclasses/pumice_config_array.py` builds a deterministic 2-way covering
array over 15 runtime mode selectors: **39 vectors, 105 of 105 pairs**, against
a full cross product of ~5.9e8. Crossed with the mandatory hazard axes it is
**39 x gap{0,4,8,15} x direction{sequential, concurrent} = 312 cells** at FULL,
one pytest cell each so the run distributes; GATE takes 2 and FUNC 16, STRIDED
rather than a prefix (a prefix runs the early rows at every gap and the vertical
growth at none, which reads as coverage and is not).

The coverage number is CHECKED, not claimed:
`test_pumice_config_sweep_coverage` asserts 105/105 **at each of the four
gaps** -- covering the pairs only in aggregate would leave a gap-specific
interaction unreached, which is exactly BUG-003's shape.

Each cell carries two oracles: golden data through the DFI slave's MemoryModel,
and the five layer-2b telemetry invariants. Built on the existing TB
(`PumiceTopCsrTB`, `_bringup`, `_wr_rd_check`) with one new helper,
`set_read_gap()`, which pins the R-channel RREADY gap instead of randomising it
-- a covering-array cell that cannot be reproduced is not a regression.

**Layer 3 -- seeded random config soak.** `random_vector()` / `random_vectors()`
plus `cocotb_test_config_soak`, seeded from the suite's `SEED`/`RDS_SEED_BASE`
plumbing. A failure prints the round, the gap, the full vector id and the exact
replay command. 12 rounds at FULL; green on seeds 1, 7, 42 and 99.

### The selector set differs from this task's list, deliberately

Dropped: `policy_scope` (made reserved when the adaptive modes were retired, so
not software-writable at all) and `gear_ratio` / `rd_phase` / `wr_phase` /
`memtype` (BUILD geometry -- changing them at runtime mis-describes the
hardware rather than exploring a legal config; [[ISSUE-016]] is what that costs).

Also dropped, and this one is about the ORACLE rather than the DUT: `bank_lsb`
and `hash_en`. The top TB builds its golden `AddressMapping` once at
construction assuming `bank_lsb == col_width`. Sweeping `bank_lsb` makes the DUT
and the model decode the same address to different DRAM cells -- measured, the
reads came back CORRECT and the golden side read zero. A cell whose oracle is
invalid is worse than an absent cell. They stay covered where the oracle does
follow them: `test_addr_mapper` at fub level, and on the board.

Added in their place: `tr_init`, `age_thresh`, `postpone_limit`, `pullin_limit`,
`wr_high_wm`, `wr_batch_max`. Still 15 selectors, so the number this task asks
to report -- 105 -- is unchanged.

### Layer 3 disproved one of layer 2b's own invariants on its first real run

`pre_le_act` asserted `PRE <= ACT`. That is false over a WINDOW: a window
inherits banks left open by the previous round, and refresh issues PREA to close
rows opened before it began. Measured on correct hardware at seed 7, round 3:
**PRE=43 against ACT=42**. Corrected to `pre_le_act_plus_open_banks`,
`PRE <= ACT + NUM_BANKS`, with the measurement recorded beside it.

That is the argument for layer 3 existing, and it is not the one the task
predicted. The covering array could never have found it -- it is not a config
interaction at all, it is a window-boundary effect. Two of the three invariant
corrections in this task have now come from contact with real counters rather
than from reasoning (`act_le_col_ops` was the first).

### Depth, stated rather than banked

The task budgeted 1-3 min per cell and 6-19 h serial. The first build ran a cell
in well under a second: the config crossing was right, the per-cell probing was
shallow. FULL cells now run 4 address bands and 96 concurrent bursts; 312 cells
take **2 min 28 s at `-n 16`**, still far under the estimate. GATE and FUNC are
unchanged and stay inside the ordinary regression.

### Regression

pumice from clean: **912 passed, 0 failed** (175 fub / 171 macro / 518 top /
48 phy), up from 580 before this work and 376 before the branch landed.

### What this plan still does not catch

Unchanged from the analysis above: no sim layer ranks paging or scheduling
POLICY, because the loopback models no page timing -- every bandwidth claim
still needs the board. And 2-way coverage is 2-way: a defect needing three
specific settings at once is reached by layer 3 only eventually and by layer 1
never. "105 of 105 pairs" means every pair was tried, not that the design is
correct.
