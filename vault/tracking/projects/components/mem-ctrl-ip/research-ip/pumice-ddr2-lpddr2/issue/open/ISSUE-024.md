# ISSUE-024: the perf proxies wait on engines with a WALL-CLOCK timeout, so a loaded machine fails the framework suite spuriously

> Source: pumice TASK-049 gates (2026-10-23). The ddr2_char framework suite
> (`make run-func-parallel`, 222 cells) failed 10 cells -- "col_major: read
> engine did not complete" on the granite and LiteDRAM proxies, the char
> families test, seven UART smoke / page-hit cells -- while a 159-cell
> val/amba run, four other sims and a Vivado implementation shared the
> machine. The same ten cells, re-run alone on the same text an hour later,
> passed 10 / 10 in 28 minutes. The text had not changed.
> Related: `pumice_master.wait_engine(drv, which, timeout_s=120)` (a
> `time.monotonic()` deadline), the proxies' `measure_family` (write and
> read phases each bounded by it), the "never dismiss failures as flaky"
> rule -- this is the mechanism, not a dismissal.

**Priority:** P2
**Status:** open
**Owner:** TBD

## What is wrong

`wait_engine` polls the engine's done flag over the simulated UART bridge
until a WALL-CLOCK deadline (`timeout_s`, 120 s on the proxies). In
simulation the engine's progress is measured in simulated cycles, which the
host cannot see; under load the simulator runs slower, the deadline passes
with the engine still mid-phase, and the proxy records `rd_ok = False` and
asserts "read engine did not complete". The number of cells that fail is a
function of machine load, not of the design or the text. 56 pytest reruns
happened in that run for the same reason.

## What to do

- In simulation, bound the wait in SIMULATED cycles (the harness timer or a
  cycle count read over the bridge), or scale `timeout_s` by the observed
  simulation rate; keep the wall-clock bound for the board, where it is the
  right unit.
- Until then, run the framework suite on a quiet machine, and treat a
  "did not complete" with an otherwise clean log as this issue -- but
  re-run the cell alone to prove it, every time.
