---
title: UART harness
summary: One host program against sim and silicon; transports differ, bytes do not.
---

# UART harness: sim + FPGA, one host program

The characterization pattern (ddr2_char, cdc_counter_display, stream_char,
rapids_char): the host program speaks a UART byte protocol to harness CSRs.
- SIM transport: a cocotb.function bridge (NOT a polling pump) driving the
  DUT's UART; the TB wraps the HARNESS with an injectable driver - not the
  clocking top - so co-prime/awkward clocks stay testable.
- FPGA transport: the real serial port. Same bytes, same host code.
- All register access by name via the PeakRDL regmap
  ([[registers-by-name]] in dv/) - this is what guarantees sim and board
  cannot disagree about the address map.
- Sim equivalence is the point: run the SAME host program in sim first; it
  has caught real host bugs (clear_stats, data-mode CRC) before silicon.
- Sim config replicates the FPGA config EXACTLY (channels, presets,
  monitor sizing); shrink only transfer lengths for runtime.
Board-side mechanics: [[boards]].
