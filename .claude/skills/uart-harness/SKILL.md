---
name: uart-harness
description: The UART characterization-harness methodology - one host program running identically against cocotb sim and the FPGA. Sim transport, regmap-by-name, board bring-up gotchas (JTAG serials, ttyUSB). Use for any board characterization flow.
---

# UART harness: sim + FPGA, one host program

Pattern (proven in ddr2_char, cdc_counter_display, stream_char, rapids_char):
the host program speaks a UART byte protocol to harness CSRs; in sim the
transport is a cocotb.function bridge (NOT a pump loop); on the board it is a
real serial port. Same bytes, same regmap, both worlds - sim equivalence has
caught real host-program bugs before silicon.

Rules:
- Registers by NAME via the PeakRDL-generated regmap (peakrdl_generate.py
  --regmap); hardcoded offsets are forbidden (they broke when monitors moved
  to 0x1000).
- Regenerate registers ONLY via bin/peakrdl_generate.py (RTL+docs+regmap in
  lockstep).
- The sim TB wraps the HARNESS (injectable driver), not the clocking top.

Board bring-up (this lab):
- Shared JTAG chain: Nexys A7 = 210292B7D46F (xc7a100t), Genesys 2 =
  200300B818A0 (xc7k325t); select via RAPIDS_CHAR_JTAG_SERIAL.
- Genesys 2 UART is a SEPARATE FT232R (AU05X8RM). Adept kills its ttyUSB;
  do NOT power-cycle after programming.
- Replicate the FPGA config EXACTLY in sim (channels, presets, sizes);
  never adapt/shrink except transfer length for runtime.
