# Structure trackers

Passive per-FUB monitors that emit ONE greppable markdown table per
structure, so a decision can be followed ACROSS structures after the fact
instead of re-deriving it with ad-hoc `$display`s every investigation.

Reference implementation: `projects/components/memory-controllers/
pumice-ddr2-lpddr2/dv/tbclasses/trackers/`.

## Why they exist

Three of pumice's hardest bugs (the REFpb rotor desync, the refresh
double-issue, and the column-after-PRE read wedge) were each found by
hand-adding `$display`s to RTL, reading them once, and deleting them. The
next investigation started from zero. A tracker makes that instrumentation
permanent, selectable, and — critically — *cross-referenced*: the paging
verdict, the refresh grant and the CAM entry that collided are three rows
you can line up by cycle.

## The contract

1. **One fixed column layout for every tracker.**
   `| time(ns) | cycle | tracker | event | rank | bank | slot | data |`
   Same widths everywhere, so logs from different structures concatenate
   into one sortable table and `grep '| b3 '` finds every structure's view
   of bank 3.

2. **Short stable tracker names.** `pgpol`, `refr`, `sched`, `camrd`,
   `camwr`, `btmr`, `dficmd`… The name is the grep key; renaming it breaks
   everyone's saved greps, so treat it as API.

3. **Emit on EVENTS, not per cycle.** State changes, handshakes, counter
   increments. A per-cycle dump is unreadable at scale and buries the
   three rows that matter.

4. **OFF by default, one env var on.** In pumice: `PUMICE_TRACKERS=1`.
   The normal regression pays nothing; a debugging run pays one line.

5. **A tracker may NEVER fail a test.** It is instrumentation, not a
   checker. Resolve signals tolerantly (`safe_int` / `is_high` returning
   0/False on a miss) and wrap `run()` so an exception disables THAT
   tracker with a warning instead of killing the simulation.

6. **Resolve the clock by name, not by assumption.** `aclk` / `mc_clk` /
   `clk` / `dfi_clk` — try them in order. See the rot lesson below.

## They rot silently — validate against the RTL

Trackers observe signal NAMES, so a rename in RTL does not break them
loudly; it makes them emit nothing. Pumice's set had drifted through an
entire rearchitecture undetected (2026-08-27 audit):

- one tracker targeted a FUB that had been **deleted** (`page_predictor`),
- three targeted **renamed** FUBs (`xbank_timers`, `rd_cl_aligner`,
  `wr_beat_sequencer`) and read signals that no longer existed,
- **every** tracker hard-coded `mc_clk` while the rearchitected FUBs use
  `aclk` — so the first one to run took the whole test down with an
  `AttributeError`,
- the `wire_trackers` hierarchy map still pointed at the pre-rearchitecture
  instance path.

None of that surfaced because nothing had run them since the rearchitecture.

**So: the only proof a tracker works is a clean run whose `.out` file
contains the events you expect.** Check the CONTENT, not the file's
existence — a tracker bound to nothing writes a valid, empty, header-only
table. Good acceptance checks:

- **conservation** — `INSERT` count == `ISSUE` count == retire count for a
  CAM-like structure,
- **the test's own story** — running a mode test, the tracker should show
  that test's arms (pumice's rbl test produced
  `MODE_0 → MODE_6 → RBL_LOWLOC(b3) → MODE_7 → MODE_0`, matching the
  arms exactly),
- **cross-tracker agreement** — the scheduler's `EVT_ACT` count should
  match the bank timers' `ROW_ACTIVE_SET` count.

## Channel utilization is a different question — and a trap

A handshake tracker (`AxiChanTracker` in pumice) buckets every cycle the
way `rtl/amba/shared/axi_bus_meter.sv` does — productive / backpressure /
starvation / idle — plus the RUN LENGTH of consecutive `valid && ready`.

Read the buckets before believing a utilization number:

- **high `starv%` (ready high, valid low) means the STIMULUS is the
  bottleneck, not the DUT.** Pumice's tightest back-to-back core test
  measures 8.6% data-channel utilization with 91% starvation and *zero*
  backpressure — the controller was ready and waiting almost the whole
  run. That number grades the testbench, not the design.
- **high `bp%`** is the interesting one: the DUT stalling a master that
  wants to send.
- **`max_run`** answers "how long can the handshake hold". A data channel
  that never exceeds one burst length is not bridging bursts — which may
  be the design, the page policy, or (again) the stimulus.

So: to grade a DUT's streaming ceiling you need a stimulus that keeps the
request pipe full; otherwise you are measuring your own driver.

## Wiring

`wire_trackers(dut, scope_paths={...})` takes a per-tracker instance path
because each tracker watches a different sub-module. Keep that map next to
the hierarchy it describes and update it with the RTL — it is the piece
most likely to rot after a refactor.

## Related

- [[silent-fallbacks]] — the same failure shape: instrumentation that
  degrades to silence instead of erroring.
- [[measure-over-the-window]] — what to do with the numbers once the
  trackers hand them over.
