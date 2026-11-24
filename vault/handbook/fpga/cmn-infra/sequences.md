---
title: Test sequences
summary: Named, ordered, dependency-checked campaign steps - one init, N tests.
---

# Sequences (projects/fpga-systems/bin/sequence.py)

A campaign is an **init sequence** followed by one or more **test sequences**.
Each is a named `Sequence` in the area's own `bin/`; a `run_<test>.py` composes
the transport once and hands the runner an order:

```python
runner = SequenceRunner(SequenceContext()).discover(SEQ_DIR)
runner.resolve(order)          # validate BEFORE opening anything
runner.ctx.bus = driver        # inject the already-built transport
report = runner.run(order)
```

Reference area: `projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/bin/` (`seq_init.py`,
`seq_write_read.py`, `seq_memtest.py`, `run_smoke.py`). Areas nest by board and
component; the build flow they drive stays where it is (pumice's drivers still
live under `projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/build-perf/host/`).

## The two rules, and the failure each prevents

**A sequence never opens its own port.** It receives a `SequenceContext`
carrying an already-built bus and addresses registers by name only. This is what
keeps [[uart-harness]] equivalence intact -- the identical sequence runs against
silicon and against the cocotb sim, because only the injected bridge differs. A
sequence that accepted `--port` would quietly end that property.

**Names are declared and resolved up front.** Every sequence declares `name`;
the runner resolves the requested order *and* every `requires` before a single
UART frame moves. Convention-only discovery was the tempting alternative and is
a trap: a misspelled `seq_int.py` silently skips init, and a skipped init on a
DDR2 board looks exactly like a timing bug -- same hour of chasing, wrong
suspect. `requires` is checked against what has actually RUN, so listing init
*after* its dependant is an error, not a coin flip.

Two more defaults chosen for the same reason:

- `stop_on_fail=True`. Once init fails, later steps measure a controller that
  never came up. Their numbers are worse than useless -- they look like data.
- `discover()` raises when an area yields no sequences, rather than reporting a
  clean pass over an empty plan.

## A sequence that writes memory changes what the next sweep reads

A sweep compared against an earlier bin is a cycle-identity check only if the
board starts it in the earlier bin's state. A sequence that writes memory
before the sweep breaks that without any error. On 2026-11-24 the onyx IO
sequence (`seq_io`, a WriteUnique to line 0x440) ran before the bin 5 sweep,
and the sweep's read-data CRC then differed from bin 4 in every cell whose read
region covers that line, while the cycle counts were equal everywhere but the
first cell. Run the identity sweep straight after init + smoke, and run any
sequence that writes memory after it. When a CRC moves while the cycles hold,
check what the steps before the sweep wrote before suspecting the design.

## Passing state between steps

A sequence's return value lands in `ctx.results[name]`; the next one reads it
with `ctx.result("init")`, which raises if that step did not run. Pumice's init
returns its live `SimpleTest` (carrying the leveled read window) and the test
sequences take it from there -- neither module imports the other.

## Related

- [[host-stack]] - the transport the context is handed
- [[boards]] - which board, and which of its ports
- [[uart-harness]] - the sim/silicon equivalence this preserves
