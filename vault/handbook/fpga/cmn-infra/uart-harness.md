---
title: UART harness
summary: One host program against sim and silicon; transports differ, bytes do not.
---

# UART harness: sim + FPGA, one host program

The characterization pattern (ddr2_char, cdc_counter_display, stream_char,
rapids_char): the host program speaks a UART byte protocol to harness CSRs.
- SIM transport: `make_uart_channel(dut, clock, clks_per_bit)` from
  `bin/TBClasses/harness/cocotb_axil_bridge.py`, handed to
  `UARTAxiBridge(channel=...)`. A cocotb.function bridge, NOT a polling pump.
  The TB wraps the HARNESS with an injectable driver - not the clocking top -
  so co-prime/awkward clocks stay testable.
- FPGA transport: `UARTAxiBridge(port=...)`, the real serial port. Same bytes,
  same host code; `channel=` versus `port=` is the entire difference.
- Both halves already exist and are shared - see [[host-stack]] for the layer
  map. Write neither.
- All register access by name via the PeakRDL regmap
  ([[registers-by-name]] in dv/) - this is what guarantees sim and board
  cannot disagree about the address map.
- Sim equivalence is the point: run the SAME host program in sim first; it
  has caught real host bugs (clear_stats, data-mode CRC) before silicon.
- Sim config replicates the FPGA config EXACTLY (channels, presets,
  monitor sizing); shrink only transfer lengths for runtime.
Board-side mechanics: [[boards]].

## The anti-pattern: a private bridge in the testbench

**Never define a bridge class inside a testbench.** If sim reaches the DUT by
any path other than `UARTAxiBridge(channel=...)`, the equivalence property is
gone and nothing reports it - the sim still passes, it just stops being
evidence about the board.

What it cost (STREAM Genesys 2, found 2026-08-25). The cosim declared FOUR
byte-identical `_Bridge` classes inline in
`Genesys2/stream/dv/tbclasses/stream_harness_tb.py`, each wrapping
`cocotb.function(tb.uart_write/uart_read)`. Grepping that whole `dv/` tree for
`UARTAxiBridge`, `byte_channel`, `cocotb_axil_bridge`, `make_uart_channel` or
`TracingChannel` returned ZERO hits, while the file's own docstring claimed
"there is one transport class and no copy to drift". Two consequences:

- Those shims hook in at the REGISTER level, above the ASCII protocol, so the
  UART byte framing the board's host actually talks through was never
  exercised in simulation at all. A defect in that layer is structurally
  invisible: sim green, board dead, descriptors verifying fine in memory
  because they arrived by a different route than the board uses.
- With no `ByteChannel` there is no wire, so `TracingChannel` cannot record
  one, so the board-vs-sim byte diff - the entire reason the abstraction
  exists - was unavailable exactly when a board was moving zero beats.

The campaign layer had drifted the same way: eight board host programs import
`CharacterizationRunner` from the flow's shared `bin/characterization.py`; no
sim code imported it. The cosim reimplemented the campaigns inline, carrying
comments like "Match the FPGA characterization's first config exactly" - a
hand-maintained lookalike of the runner the board runs.

Same failure shape as [[one-source-config]] one layer up: a second
implementation beside a shared one, with nothing comparing them. The rule is
the same - inject the transport, run the ONE program.
