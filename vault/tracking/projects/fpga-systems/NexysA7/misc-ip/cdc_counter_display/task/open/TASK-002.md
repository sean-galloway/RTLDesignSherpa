# TASK-002: sim must carry a value through every CDC mode, not just round-trip the mode code

**Priority:** P2
**Status:** open (filed 2026-11-07 from the CDC_DEMO_TODO migration)
**Owner:** TBD

## The gap

`build-demo/dv/tests/test_cdc_demo_uart.py` has four tests. `press` and
`cfg_load` run with `cdc_mode=CDC_NO_CDC` (the default argument in
`build-demo/host/cdc_programs.py`). `cdc_mode` writes each of the five codes
and reads the CSR back -- it proves the register fan-out, not the crossing.
So **no simulation drives a value through STRETCH, SYNC_FIFO, TWO_PHASE or
FOUR_PHASE**; those four paths are proven only on the board.

## Done when

- `press` and `cfg_load` (or a new program) run in each of modes 1-4 and check
  VALUE against the expected count, at a slow and a fast counter clock.
- Mode 1 is checked below its STRETCH ceiling only (above it, failure is the
  intended behaviour and RTL sim will not show it -- that is TASK-005).
- The same program runs unchanged on the board (`make host-cdc_demo`), per the
  UART-harness rule that sim and board run one host program.
- Run through the build-demo Makefile, clean-all first.
