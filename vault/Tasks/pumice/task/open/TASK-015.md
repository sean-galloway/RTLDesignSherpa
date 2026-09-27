# TASK-015: test the DUT across configurations — a 4-layer plan with a coverage number

**Status:** open 2026-09-26  **Priority:** P2 — this is the systemic answer to
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

> **This collides with a standing repo rule and needs an explicit decision.**
> `vault/handbook` records *"No assertions in RTL -- they break some tools;
> properties go in external formal/ blocks, never in the module."* Followed
> strictly, that rule deletes the only detector that found BUG-003. And it cannot
> simply move to formal: `reference_formal_internal_visibility` records that
> formal binds on PeakRDL blocks see **only ports**, so an internal invariant like
> "issue_q must be non-empty when a return beat lands" is not checkable there.
> Recommended resolution: allow `ifndef SYNTHESIS` accounting assertions in FUBs,
> keep the no-assertion rule for anything synthesizable, and record the exception
> with BUG-003 as its justification.

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
| 2a more assertions | ~2 days, needs the rule decision | the interaction class the way BUG-003 was actually caught |
| 3 random soak | ~2 days | 3-way and deeper; a growing corpus of pinned seeds |

**Do 0 and 2b first.** Layer 0 is the highest value per hour and needs no
decision from anyone; 2b is what makes the rest meaningful.

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
