---
title: FPGA common infrastructure
summary: Cross-cutting, board-agnostic FPGA method + the shared host py stack.
---

# FPGA -- common infrastructure

Canonical ideas and shared code used across every board and component. Anything
board- or component-specific does NOT live here -- it nests under a board (see
the [FPGA area](../INDEX.md) "Boards / components").

## Canonical patterns
- [[uart-harness]] - one host program against sim and silicon
- [[host-stack]] - the shared py transport stack that pattern is built on
  (board/port discovery -> UARTAxiBridge -> Device/DeviceBus, registers by name)
- [[sequences]] - named, ordered, dependency-checked campaign steps
  (fpga/bin/sequence.py); one init, N tests, transport injected

## Build + timing process
- [[build-flows]] - Vivado batch flow, board switches, bitstream naming
- [[timing-closure]] - the triage order when timing fails
- [[timing-triage-tool]] - bin/vivado_timing_failures.py (bucketizes fails)

## Board handling
- [[boards]] - the fpga/bin/boards registry: JTAG serials, UART chips, the
  gotchas that eat an afternoon
