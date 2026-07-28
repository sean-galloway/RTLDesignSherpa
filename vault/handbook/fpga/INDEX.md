---
title: FPGA notes
summary: Board process - build flows, timing triage, harness, board handling.
---

# FPGA

- [[build-flows]] - Vivado batch flow, board switches, bitstream naming
- [[timing-closure]] - the triage order when timing fails
- [[timing-triage-tool]] - bin/vivado_timing_failures.py (bucketizes fails)
- [[uart-harness]] - one host program against sim and silicon
- [[monitor-board-coverage]] - see every packet type from every agent via a config-defined dense tally
- [[monitor-coverage-testplan]] - the 12-32 board sequences that drive that coverage
- [[boards]] - JTAG serials, UART chips, the gotchas that eat an afternoon
