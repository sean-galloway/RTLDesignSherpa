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
**Status:** closed 2026-10-29 (the wait is bounded by time without progress; see the closing entry)
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

**2026-10-23, granite proxy:** the `mixed` cell at eight threads on the new
FIFO store failed twice with "write engine did not complete" -- once under
five parallel proxies, once under three -- while the timer window it did
record (200 290 / 200 299 cycles) was the entry store's to the cycle. Run
alone it passed with those same counts. Third instance of this issue; the
granite proxy now dumps `gen_done` / `gen_errors` and the store's registered
state on a failed cell (`_host_diag`), so the next one can be told apart
from a hang without a rerun.

## Fix (2026-10-29)

`pumice_master.wait_engine` now bounds the time WITHOUT PROGRESS rather
than the run: it samples the engine's bus-meter productive-beat count
(`OBS_WR_PROD` / `OBS_RD_PROD`, live while the trace is unfrozen, which it
is during every wait) once a second, and each advance moves the deadline
out by `timeout_s` again, up to `max_extensions` (60) times. On the board
nothing changes: a stuck engine stops counting and times out at
`timeout_s` as before. In simulation a slow but moving engine is waited
for, which is the ISSUE's case: the engine's progress is in simulated
cycles the host cannot see, and the wall clock no longer decides the
verdict on its own. One signature for every caller (the proxies, the char
profiles, the bring-up scripts); the probe costs four register reads per
second of wait.

Validated through both perf proxies on a clean build (pumice 1 passed in
382 s, granite 1 passed in 242 s) and the host unit tests (31 passed), then the whole framework suite
(`make clean-all && make run-all-func-parallel`: 222 passed, 2 xfailed in
32.5 min, no reruns). The
loaded-machine case itself is not reproducible on demand; the next
"did not complete" with a clean log and a moving meter is this mechanism's
test, and the proxies' `_host_diag` dump (2026-10-23 entry) tells a hang
from a slow sim without a rerun.
