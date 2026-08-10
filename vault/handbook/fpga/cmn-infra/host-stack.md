---
title: Host transport stack
summary: The shared py stack every char flow's host tools build on.
---

# Host transport stack (shared py)

The canonical, cross-project py plumbing that makes [[uart-harness]] real -- one
host program, sim and silicon. Every board/component host suite (e.g. the STREAM
[[host-tools]]) composes THIS stack; none of it is board-specific, so it lives
here in cmn-infra, not under a board.

Layers, bottom up:
- **Board + port discovery** -- `projects/fpga-systems/bin/` (`uart_link.py`, `board.py`,
  `boards/`): which board, and which of its `ttyUSB`s runs the right bitstream.
  `UartLink` satisfies the same `ByteChannel` protocol as `SerialChannel`, so it
  drops straight into `UARTAxiBridge(channel=...)`. Before this existed each flow
  grew its own `autodetect_port()` -- four near-identical copies. See [[boards]].
- **Byte transport** -- `bin/TBClasses/harness/byte_channel.py`:
  `SerialChannel(port, baudrate)` is the real pyserial transport; the cocotb
  side swaps in a `cocotb.function` bridge. Same bytes either way.
- **AXI-over-UART bridge** -- `projects/components/converters/bin/uart_axi_bridge.py`:
  `UARTAxiBridge(port, baudrate)` speaks the ASCII register protocol
  (`"W {addr:08X} {data:08X}\n"` -> `"OK"`, `"R {addr:08X}\n"` -> `"0x..."`) and
  exposes `write(addr, data)` / `read(addr)` / `write_verify(addr, data)`.
- **By-name register access** -- `UartRegisterMap`
  (`bin/TBClasses/harness/uart_register_map.py`): the UART-transport adaptation
  of the house `RegisterMap`. It reuses `bin/TBClasses/apb/register_map.py`
  as-is for register/field parsing and offset/mask math; only the transaction
  emission differs (drives an injected bridge's `write`/`read` instead of
  building APBPackets). **It already does read-modify-write** --
  `regs.write("REG", rmw=True, some_field=3)` preserves the unnamed fields.
  Reaching for a read-back-then-write loop in a device class means duplicating
  this; don't.
- **Named devices** -- `Device` / `DeviceBus` (`bin/TBClasses/harness/device.py`):
  wrap a `UartRegisterMap` so registers are accessed BY NAME over one injected
  bridge (`bus["stream"].SCHED_CONFIG.write_word(...)`). This is the
  [[registers-by-name]] guarantee that sim and board can't disagree about the
  address map. A flow's `build_*_bus(bridge)` factory composes each regmap as
  its own Device. `Device.write(reg, **fields)` forwards kwargs, so `rmw=True`
  passes straight through to the layer above.
- **Sequences** -- `projects/fpga-systems/bin/sequence.py`: an area's init + test steps, named and
  ordered, with dependencies resolved before any traffic. The bus above is
  *injected* into each step, which is what keeps the equivalence property.
  See [[sequences]].

Why it matters: a new campaign never re-implements transport or address decode.
It injects `UARTAxiBridge(port=...)` (silicon) or the sim bridge, calls the
flow's `build_*_bus`, and drives everything by name. The primitive-routine PoC
(`flows-stream-monitor/host/poc.py`) and the DMA routine (`poc_dma.py`) are the
minimal worked examples against a live board.
