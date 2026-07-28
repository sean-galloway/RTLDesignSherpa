---
title: FPGA notes
summary: Board process - build flows, timing triage, harness, board handling.
---

# FPGA

- [[build-flows]] - Vivado batch flow, board switches, bitstream naming
- [[timing-closure]] - the triage order when timing fails
- [[timing-triage-tool]] - bin/vivado_timing_failures.py (bucketizes fails)
- [[uart-harness]] - one host program against sim and silicon
- [[boards]] - JTAG serials, UART chips, the gotchas that eat an afternoon

## Boards / components

Board- and component-specific FPGA docs nest by target (the layout the repo
Linux paths will grow into) - they are NOT flat handbook notes:

- [Genesys2/stream-mon/](Genesys2/stream-mon/INDEX.md) - STREAM monitor coverage build + campaign
