---
title: projects/fpga-systems/bin
summary: The shared board + UART layer every characterization flow composes.
repo: projects/fpga-systems/bin
---

# projects/fpga-systems/bin

**Code:** [`projects/fpga-systems/bin/`](../../../../../projects/fpga-systems/bin)

The board half of the host stack: which board, which of its serial ports, and
how to program it. Every characterization flow (pumice/ddr2, cdc, rapids,
stream) composes this rather than growing its own copy.

## What lives here

| File | Role |
|---|---|
| `uart_link.py` | Port enumeration (`UartPort`, `list_uart_ports`), the `UartLink` client, and `find_port` with its identity probes |
| `uart_axi_bridge.py` | `UARTAxiBridge` - the ASCII `W`/`R` register protocol. **The real home**; the `converters/bin` copy is a re-export shim, never import through it |
| `board.py` | `BoardSpec` + `Board`: per-board UART discovery and JTAG programming, both by serial |
| `boards/` | The registry, one file per board (`nexys_a7_100t.py`, `genesys2.py`), import-discovered so a new board needs no central list edit |
| `fpga_board.py` | CLI over the registry: `list`, `info`, `ports`, `serial`, `program` |
| `program_fpga.tcl` | The one programming script. Knows no board facts; everything arrives as `FPGA_BITSTREAM` / `FPGA_JTAG_SERIAL` / `FPGA_BOARD` |
| `test_uart_link.py`, `test_sequence.py` | Board-less tests for the selection logic |
| `sequence.py` | The campaign runner - see [sequences](../../../../../vault/handbook/fpga/cmn-infra/sequences.md) |

Local `vivado.jou` / `vivado.log` are tool droppings from running the tcl here;
`.gitignore` already covers them under `vivado*`.

## The one thing to understand: the transport pivot

Method lives in the handbook -
[uart-harness](../../../../../vault/handbook/fpga/cmn-infra/uart-harness.md) for the
equivalence property and its anti-pattern,
[host-stack](../../../../../vault/handbook/fpga/cmn-infra/host-stack.md) for the full
layer map. What is worth knowing *here* is where this directory sits in it.

A host program never learns whether it is talking to silicon or a simulator.
`UARTAxiBridge` emits the identical ASCII byte stream either way, and the whole
difference is one keyword at construction:

```
FPGA   UARTAxiBridge(port="/dev/ttyUSB1")      -> pyserial -> FT2232/FT232R -> uart_axil_bridge RTL
SIM    UARTAxiBridge(channel=make_uart_channel(dut, clk, clks_per_bit))
                                               -> cocotb UARTMaster/Monitor -> the SAME RTL
```

Both satisfy `ByteChannel` (`bin/TBClasses/harness/byte_channel.py`), so nothing
above the bridge can tell them apart. Above it sit `UartRegisterMap` and
`Device`/`DeviceBus`, which address registers by name off the PeakRDL regmap -
that is what stops sim and board disagreeing about the address map.

The sim side is a `cocotb.function` bridge, not a polling pump: the synchronous
host program runs in a worker thread under `cocotb.external`, and its blocking
`write`/`read_until` hand coroutines back to the scheduler so sim time actually
advances. A free-running pump with plain thread queues stalls instead.

On the board, two filters are both required to reach the right target, and they
pull in opposite directions on the same FTDI interface letter: UART port
matching must be *loose* (`...D46F` vs `...D46FB`, or a present board reads as
absent), while JTAG target selection must be *specific* (the short serial is a
prefix of the real target name, and the sibling channel has no scan chain).
Both are worked through in
[boards](../../../../../vault/handbook/fpga/cmn-infra/boards.md).

Flow Makefiles do not call `fpga_board.py`; they include `make/fpga_board.mk`,
which supplies `program`, `ports`, `board-info` and `boards`, switchable with
`BOARD=genesys2`.

## Notes

**The registry and the handbook disagree about the Nexys A7 serial.** The
registry says `210292BFA3EE`; `boards.md` still lists `210292B7D46F`. Dated
evidence favours the registry - `B7D46F` appears only in June 2026 and earlier
artifacts, while every measurement from 2026-08-25 on (pumice re-validation,
`seq_page_policy` 2026-09-21, the cdc board validation) names `BFA3EE`. The lab
has had two A7-100T units on the desk and the registry's own comment says so.
The handbook note looks stale rather than wrong-in-principle. Unverified against
the hardware.

**A per-flow `program_fpga.tcl` survived the consolidation.**
`Genesys2/rapids_characterization/flows-rapids-beats/tcl/program_fpga.tcl:23`
still hardcodes `set want_serial "210292B7D46F"` - a copy of the pattern this
directory exists to replace, pinning the unit that is probably no longer on the
bench.

**Nothing runs the board-less tests.** `test_uart_link.py` and
`test_sequence.py` are not referenced by any Makefile or CI workflow. They cover
exactly the logic whose failures are silent on hardware - a wrong port or a
skipped init reads as a timing bug - so they are worth wiring in.
