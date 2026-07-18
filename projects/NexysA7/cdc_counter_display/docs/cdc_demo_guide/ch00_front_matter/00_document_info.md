# Document Information

This is the operator / developer guide for the Nexys A7 **CDC Counter Display**
project (`projects/NexysA7/cdc_counter_display`). It explains what the project
is, how it works, how to build / simulate / program / run it, and how the UART
characterization harness is configured. It is a practical guide, not a formal
architecture specification.

The project ships in two phases that coexist in the same tree:

- **Phase 1** — a standalone, button-driven CDC counter (`cdc_counter_display_top`).
- **Phase 2** — a UART-controlled, four-counter CDC demonstrator
  (`cdc_demo_top`) with a host program that runs byte-for-byte identically on the
  FPGA and in a cocotb simulation. This guide focuses on Phase 2.

---

## References

| Source | Title |
|--------|-------|
| RTL Design Sherpa | `projects/NexysA7/cdc_counter_display/README.md` |
| RTL Design Sherpa | `docs/HARNESS.md` (CSR map + wiring) |
| RTL Design Sherpa | `docs/RUNBOOK.md` (operator procedures) |
| RTL Design Sherpa | `bin/TBClasses/harness/` (shared UART-char collateral) |
| Digilent | Nexys A7 Reference Manual |
| ARM | AMBA AXI and APB Protocol Specifications |

: Document references

---

## Conventions

- **Registers are accessed by name**, never by hardcoded offset (see Chapter 4).
- **Clock:** `sys_clk` = 100 MHz on-board oscillator. Per-counter source clocks
  (`ctr_clk[i]`) are asynchronous to `sys_clk` and to each other.
- **Reset:** `CPU_RESETN` (board button BTNR, active-low) or `CTRL.soft_reset`.
- **Register/signal prefixes:** `r_` registered, `w_` combinational.

---

## Revision History

| Version | Date | Notes |
|---------|------|-------|
| 0.90 | 2026-07-18 | Initial project guide |

: Revision history
