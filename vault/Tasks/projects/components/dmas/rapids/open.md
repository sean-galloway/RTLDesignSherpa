<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# RAPIDS tasks — open (not started)

## TASK-057: Enforce register-map hygiene in RAPIDS DV (port the STREAM lessons)

**Priority:** P2
**Status:** Not Started
**Owner:** TBD

**Context:** STREAM had three register-map defects that a coverage/board
bring-up exposed on 2026-07-28/29 (fix: commit `729c774b` + the stream_top_tb
descriptor-fetch proof). RAPIDS is the sibling DMA under `dmas/` and almost
certainly shares the patterns — audit and fix all three:

- [ ] **Use the by-name regmap.** All RAPIDS DV must resolve registers through
  the peakrdl-emitted `rapids_regmap.py` (`RegisterMap` by name), never
  hardcoded APB offsets. STREAM's top TB kicked by hardcoded `0x000 + ch*8` and
  so never touched the regmap — a regmap break passed 8/8 top tests and only
  blew up in the cosims. Mirror the `stream_top_tb` fix (load the regmap in
  setup, resolve `_reg_addr(name)`).

- [ ] **Kick writes MUST look for descriptor reads.** The top/kick tests must
  assert that writing a kick register actually causes a descriptor FETCH —
  observe the descriptor-engine AR channel and prove the kicked descriptor
  address was read — not merely that data moved (a dead/mis-decoded kick path
  still "passes" a datapath-only check if src/dst happen to line up). See
  `stream_top_tb._watch_desc_fetches()` + `assert_descriptors_fetched()`.

- [ ] **No registers done by hand.** Every register must be DEFINED IN THE RDL
  (kick registers STORE the staged address, `sw=rw; hw=r`, with launch via a
  separate KICK_ENABLE write). STREAM had 16 `CHx_CTRL` aliases hand-stuffed into `stream_regmap.py`
  while the RDL declared them "NOT defined here"; a regmap regen dropped them and
  broke every by-name consumer. Verify `rapids_regmap.py` has NO hand-added
  entries — anything a clean `bin/peakrdl_generate.py` run does not emit is a
  latent showstopper. (Regenerate via the bin wrapper only — see
  [[feedback_peakrdl_generate_bin]] equivalent.)

**Done when:** RAPIDS DV resolves every register by name from a regen-clean
`rapids_regmap.py`, the top/kick tests fail if a kick does not fetch a
descriptor, and no register is hand-added.

## RAPIDS-OBS — adopt the shared instrumentation pair (axi4_intf_master_observer + dma_slave_monitors)
**Status:** open 2026-08-05

The beats HAS (`ch06_performance/01_throughput`) already commits to measuring
per-direction bus utilization with the same instrument STREAM uses, and names
wiring it into `rapids_char_harness` as the remaining step. Two things changed
on 2026-08-05 that make that cheaper than it was:

- **`axi4_dma_observer` -> `axi4_intf_master_observer`**, moved to
  `projects/components/misc/rtl/`. The old name was a misnomer (its own header
  said "DMA-agnostic") and read wrong for a block shared by a DMA, a memory
  controller and a characterization harness.
- **It owns its config.** An APB regblock (`obs_regs`, 16 registers) replaced 29
  `cfg_*` ports that each harness had to tie off. Adopting it is now one bridge
  APB slave plus one instantiation, and registers go by name through the
  generated regmap ([[registers-by-name]]).

`dma_slave_monitors` is RETIRED (module and filelist both deleted), and its
`slvmon_regs` regblock was deleted with it on 2026-09-20 as part of STREAM
TASK-073 -- it was superseded, not merely orphaned: BOTH observer roles now
instantiate the shared `obs_regs_top`
(`axi4_intf_master_observer.sv:550`, `axi4_intf_slave_observer.sv:547`).
So the slave-side half of this adoption is `axi4_intf_slave_observer` +
`obs_regs`, not the pair named below. The filelist line quoted here no longer
resolves:

    -f $MISC_ROOT/rtl/filelists/axi4_intf_master_observer.f
    -f $MISC_ROOT/rtl/filelists/dma_slave_monitors.f

**Why it matters:** RAPIDS maps to the observer better than STREAM does -- a
read tap on the source master and a write tap on the sink master give a true
per-direction split, where STREAM's shared master is aggregate-only. And one
instrument across RAPIDS/STREAM/pumice means one definition of a stalled cycle,
so the GB/s numbers in three different reports become comparable.

Related: [[PUMICE-016]] is the same adoption for the memory controller.

## RAPIDS-KMAP — RAPIDS-beats has NO contracts workbook at all
**Status:** open 2026-08-06  **Blocked on:** [[TOOLING-KMAP]] items 1-4

Unlike stream and pumice, RAPIDS has **no**
`docs/gen_signal_contracts_kmaps.py` whatsoever. So this is not "finish the
maps" -- it is "there are none". Given RAPIDS-beats was resynced FROM stream
(prefetch, commit-gating, recoverable-timeout all ported across), it inherits
stream's decision shapes without inheriting even stream's partial workbook.

Start by copying the stream generator once [[TOOLING-KMAP]] has promoted the
machinery to `bin/` -- copying it BEFORE that just creates a third private copy
to keep in step.

Targets specific to RAPIDS, in priority order. The first three are OPEN
known_issues, which makes them the highest-value maps in the repo:

1. **Sink data path -- AXI timeout detection missing**
   (`known_issues/active/sink_data_path.md`). A map of the timeout
   qualification cone would make the missing term visible as an axis with no
   contributing expression.
2. **Sink SRAM control -- single-read limitation**
   (`known_issues/active/sink_sram_control.md`). A read-issue qualification map
   with an honest `depends_only_on` is the direct statement of what the
   limitation IS.
3. **`drain_size_gt1` source beat drop**
   (`known_issues/active/drain_size_gt1_source_beat_drop.md`). Beat-drop bugs
   are adjacency bugs; this is the archetypal K-map target.
4. **`scheduler_beats` issue qualification + commit gating.** Ported from
   stream's scheduler, so it carries the same latch/clear and timeout shapes --
   and RAPIDS has no equivalent of stream's macro coverage to catch a
   divergence.
5. **`snk_data_path_axis_beats` credit/RDA accounting.** RAPIDS' network side
   has no counterpart in stream, so nothing stream proved transfers here. This
   is the part of RAPIDS most exposed by having no workbook.
6. **`alloc_ctrl_beats` / `drain_ctrl_beats`.** Same space-accounting shapes as
   stream items 5, but independently drifted since the resync.

Note the naming-conflict history (`known_issues/scheduler_group_signal_naming_
conflicts.md`): RAPIDS has already been bitten by two signals whose names
implied a relationship they did not have. That is the same failure mode the
axis-equation requirement (criterion 3) exists to catch.

## TASK-080: scrub the tests for completeness (rapids)

**Priority:** P2. Blocks the coverage/formal push, not day-to-day work.
**Status:** open 2026-09-04. Raised by Sean: test scrubbing was meant to be
part of the kimi review packets and got dropped along the way. Applies to the
components suites as well as rtl/.

**ID note:** this area draws from the shared `TASK-nnn` sequence, whose
counter lives in [amba/INDEX.md](../../../../amba/INDEX.md). It is not a
per-area namespace -- take the number from there and bump it.

**Sequencing.** A FOCUSED pass, run after qc/humanize is finished everywhere
and BEFORE coverage and formal are driven clean.

**Scope:** `projects/components/dmas/rapids/dv/tests/` -- 17 test files.

**The capability already exists and was simply never run here.**
`bin/review/run_batch.py` has a `testqc` mode alongside `qc` and `humanize`,
with `bin/review/TEST_REVIEWER_BRIEF.md` as its brief and
`bin/review/build_test_review_bundle.py` to build the units.

**Why this is not busywork.** A test that passes because the RTL is broken is
worse than no test. The template is apb5 (2026-09-04): nothing drove
`rsp_ready`, so the response skid filled and never drained, and the TB's
completion check returned True on exactly the state the defect produced. The
suite was green BECAUSE the RTL was broken.

**Area-specific:** rapids has not been functional for roughly two months and
work resumes only after qc/humanize, the flat-flow migration and formal are
done (Sean, 2026-09-03). Do NOT start this scrub before the area is live
again -- auditing tests against RTL that is about to change is wasted effort.
This block exists so the requirement is recorded, not so it gets picked up
early.
**What "complete" has to mean, at minimum:**

- Every `test_*.py` actually exercises the DUT it names.
- No test asserts a condition the bug itself satisfies.
- Inputs the DUT needs are actually driven.
- gate/func/full levels mean something distinct, not three names for one run.
- No `run()` call pins `testcase=` to a single cocotb test. A pinned
  `testcase=` silently hides every OTHER `@cocotb.test` in that module, so a
  test can sit in the file for months and never execute. `test_apb5_master.py`
  did exactly this (2026-09-04) -- a witness added beside the basic test ran
  zero times until the pin was widened. A comma-separated list is the fix when
  a pin is genuinely wanted.
- A fix landed with a test has a mutation check recorded: the test was seen
  RED against the unfixed RTL. Without that the test is decoration.

**Related:** [[TASK-078]], [[COMMON-025]], [[MATH-010]], [[CDC-001]] are the
same task in the rtl/ areas.

## TASK-082: the sink-ingress AXIS meter reads zero on hardware

**Priority:** Medium -- it does not corrupt data, but it puts a 0.0% utilisation
and "0 B, 0 pkts" into recorded board numbers for an interface that demonstrably
carried traffic. **Status:** open 2026-09-22; reproduced in sim 2026-09-23 (TASK-084).

Measured on the Genesys 2, 2026-09-22, on the freshly fixed bitstream:

```
 8ch x 8 beats:  SINK AXIS-in: util=0.0%  (prod=0  bp=0 starv=70 idle=0)  0 B, 0 pkts
                 SINK AXI4-wr: util=91.4% (prod=64 bp=0 starv=6  idle=0)  5.85 GB/s
 2ch x 4 beats:  SINK AXIS-in: prod=0 starv=14        SINK AXI4-wr: prod=8
 sim (OLD tb):   sin meter: prod=32 bp=0 starv=12 idle=100 util=72.7%
 sim (NEW tb):   sin meter: prod=0  bp=0 starv=38            util=0.0%   <-- reproduces
 board 2026-09-23 (post-TASK-084, 8ch x 8): AXIS-in prod=0 starv=70, AXI4-wr prod=64
```

**IT REPRODUCES IN SIMULATION NOW (2026-09-23).** That is the useful part of
this update. Before TASK-084 the cocotb TB hand-sequenced the launch: it kicked
the channels, explicitly waited for `snk_system_idle` to deassert, and only THEN
started the AXIS generator -- with a long comment explaining that this was what
kept the sin window open. The board never does that; it stages everything and
fires one atomic GO. So the old TB was driving the DUT in a way the hardware
never does, and that masked the defect. The TB now reuses the board's own
campaign, drives the same GO path, and reads the same prod=0.

This moves TASK-082 from a board-only mystery (needs the Genesys 2, an ILA, and
a reprogram per experiment) to a waveform-debuggable one (`WAVES=1` on the
harness sim). Worth doing before theorising further.

All sink CRCs match golden in every one of those runs, so the data flowed. The
sink IS AXIS-fed (`axis4_master_pattern_gen` drives `s_axis_*`), so this is not a
different stimulus path -- the meter is blind, not the wire idle.

**MECHANISM PROVEN 2026-09-23 (board suite, 28 configs).** My earlier guess in
this task -- "the clear at window-open wipes the count" -- was WRONG, and so were
two follow-ups (a meter misclassification, then a bad tap). The counters settle
it without a waveform:

```
 beats/ch  total   sin prod  missed   sin starv  wr starv  dStarv   window total
        1      8          0       8          21        13       8   sin==wr  (21)
       16    128          0     128         134         6     128   sin==wr (134)
       64    512        322     190         204        14     190   sin==wr (526)
      256   2048       1858     190         196         6     190   sin==wr (2054)
     1024   8192       8002     190         196         6     190   sin==wr (8198)
     4096  32768      32578     190         196         6     190   sin==wr (32774)
```

Three facts fall out, and together they are conclusive:

1. **`missed == min(190, total)`** -- a FIXED quantity, not a proportional loss.
   Below 190 total beats the whole transfer is missed, which is why small runs
   read exactly 0 and looked like a dead meter.
2. **Beats lost from `prod` reappear in `starv`, exactly** (dProd == dStarv on
   every row). Nothing is uncounted; the meter is awake and watching an idle
   wire.
3. **`sin` and `wr` report the SAME window total** on every row, so they share
   one `obs_meter_clear`/`obs_meter_freeze` and the window itself is fine.

So the beats are not lost inside the window -- they land in a DEAD ZONE between
the meter being armed and the window actually opening, and inside the window the
ingress sits starved for precisely that many cycles while the write side drains
what was buffered.

**Confirmed at cycle level 2026-09-23** (`WAVES=1` sink run, timescale 1ps,
aclk=10,000ps, 4ch x 8 beats = 32):

```
  clear #2        875,840,000   GO: arms the meter AND pulses cfg_gen_start
  32 handshakes   875,860,000 .. 876,170,000   (31 clocks, back to back)
  clear #3        876,940,000
  obs_win_active  876,950,000 .. 877,330,000   (38 clocks)  <-- the counted window
  obs_wr_prod     reaches 32 INSIDE that window
  obs_sin_prod    never leaves 0
```

The window that produces the reported numbers opens **78 clocks after the last
ingress beat**. `obs_win_active` is gated on `obs_dut_busy` (`~snk_system_idle`),
which cannot assert until the DUT has already accepted traffic -- so ingress is
structurally guaranteed to start before the window it is supposed to be measured
in. Note there are TWO windows in the run (an earlier 1196-clock one from a prior
phase); an analysis that latches onto the first will read "no handshakes before
the window" and look like a refutation. It is not -- it is the wrong window.

*Correction:* an earlier draft of this task guessed the 190 was absorbed by
`SRAM_DEPTH=256`. The waveform does not support that. The bound is the dead-zone
DURATION (~111 clocks in this sim config), not a buffer depth; 190 is simply how
many beats fit in that gap in the 8-channel board configuration.

This is the same front-loading the OLD cocotb TB worked around by hand: it kicked,
waited for `snk_system_idle` to deassert, and only then started the generator,
with a comment explaining that this was what kept the sin window open. The board
never does that -- it stages and fires one atomic GO -- so the workaround hid a
real measurement defect for as long as sim and board ran different code.

**Not a datapath fault.** Every one of those 28 configs PASSED with golden CRCs.
The data always moved; only the ingress meter under-reports.

**Do:**
- [ ] Anchor the sink-ingress measurement to the stimulus rather than to
      `obs_dut_busy`. The window opens on `~snk_system_idle`, which necessarily
      lags the first ingress beat by however long the DUT takes to go busy --
      and that lag is the whole defect. Options: open on `cfg_gen_start`, give
      `sin` its own window, or make the generator wait for the window.
- [ ] Re-run `--suite --suite-beats 1,4,16,64,256` afterwards and assert
      `sin prod == wr prod` at every size. The bug is silent at small sizes
      today precisely because 0 looks like "no traffic" rather than "190 early".

## TASK-085: backpressure runs record meter numbers that cannot mean anything

**Priority:** Medium -- nothing is broken, but the suite JSON stores
`AXIS-out util=0.0% eff=0.00 GB/s` for every backpressure run and nothing marks
those as non-measurements. **Status:** open 2026-09-23.

Found while diagnosing TASK-082. Under `--suite` with backpressure ON the source
egress meter reports, on all 10 bp-on configs:

```
  prod=0   bp=<the whole window>   starv=0   idle=9
```

That is not a meter fault -- it is arithmetically forced by how the knob works:

- `run_source_selfcheck` arms the checker with `CHK_READY_EN=0` (tready LOW),
- then `go()` arms the meter window AND kicks in the same on-chip pulse,
- then `_poll_backpressure` raises/lowers ready FROM THE HOST over UART.

One CSR write is ~24 bytes at 115200 baud = **2.08 ms = 208,333 aclk cycles**.
The bp-on windows measured 276..2300 cycles (2.8..23 us). So **at most 0.011 of a
single host write fits inside the window** -- it closes 90x to 750x before the
host can raise ready even once. The meter therefore measures a deliberately
stalled egress and freezes; the real transfer happens afterwards. `axis_bus_meter`
is correct (`w_prod = tvalid && tready` etc., mutually exclusive), and the tap is
on the real `m_axis_*` nets.

Backpressure mode is a DATA-INTEGRITY test -- the golden CRC passes and that is
its point (`_poll_backpressure`: "always makes forward progress"). The hazard is
only that its throughput numbers are recorded as if they were measurements.

**Do:**
- [ ] Mark bp-on rows in the JSON and the printed table as integrity-only, or
      omit their `perf` block. A future reader comparing suite files will
      otherwise conclude the egress collapsed under backpressure.
- [ ] If host-paced backpressure is ever supposed to be measurable, it needs an
      on-chip stall generator; over UART it cannot be, by three orders of
      magnitude.
