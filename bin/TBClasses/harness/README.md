# TBClasses.harness — reusable UART-AXIL characterization harness transport

The NexysA7 characterization flows (`ddr2-characterization`, `stream_characterization`,
`cdc_counter_display`, …) all share the same spine:

```
USB ── UART ── uart_axil_bridge ── AXI4-Lite ── <name>_char_harness (harness_csr + DUT)
```

What differs per project is the **register map and the programs**. The **transport
spine is common**, and lives here so one host program can run byte-for-byte
identically against the FPGA (pyserial) **or** a cocotb simulation — no forked
"vaguely similar" code.

> **Agents / methodology:** see [CLAUDE.md](CLAUDE.md) for the equivalence
> principle, the recommended build order, and the non-obvious traps
> (cocotb.function vs a pump, match-the-FPGA-config, sticky-error vs soft_reset,
> digital-only reproduction). Read it before wiring a new flow.

## Modules

| Module | Side | What it is |
|--------|------|-----------|
| `byte_channel` | host | `ByteChannel` protocol + `SerialChannel` (pyserial) + `TracingChannel` (records the wire for equivalence checks). |
| `uart_register_map` | host | `UartRegisterMap` — by-name register access (`regs.write("CTRL", start_wr=1)`, `regs.field("STATUS","init_done")`, `rmw=`) over a bridge, backed by a PeakRDL-generated `<top>_regmap.py`. Adapts `TBClasses.apb.register_map`. |
| `device` | host | `Device` — one named IP instance = `UartRegisterMap` (base + regmap) over an injected bridge, with by-name passthroughs (`write`/`read`/`field`/`addr`). `DeviceBus` — a unified by-name view of N IP behind ONE bridge (heterogeneous IP *and* multiple instances of the same IP, e.g. `pumice0`/`pumice1`). IP-agnostic base for per-IP subclasses. |
| `cocotb_axil_bridge` | sim | `CocotbUartChannel` + `make_uart_channel(dut, clock, clks_per_bit)` — drives the DUT's UART pins from a cocotb `UARTMaster`/`UARTMonitor` and bridges the synchronous host program (run under `cocotb.external`) via `cocotb.function`. |
| `harness` | sim | `UartSimHarness` — the common cocotb bringup (clock + reset + UART-idle + traced channel + bridge, all signal-name-parameterized) plus the `DeviceBus` registry. A flow's sim test calls `start()` then attaches only its DUT-specific backend BFM; the generic transport bringup is no longer copy-pasted per flow. |

### Multiple IP instances

The register-map base is a per-instance argument (`UartRegisterMap(...,
start_address=...)`), so N instances of an IP live at N address windows over one
shared bridge — or over N bridges (separate links); both `bridge` and base are
injected, so nothing is a singleton. `DeviceBus` makes this the primary interface:
one bridge, a registry of named `Device`s, every register by name and never by
offset — `bus.add("pumice0", base=0x0, regmap_file=PUMICE_REGMAP, cls=Pumice)`,
`bus.add("pumice1", base=0x2000, ...)`, then `bus["pumice0"].write("SCHED_TUNING",
force_inorder=1)`. Heterogeneous IP (harness_csr + pumice + a debug block) and
multiple instances of the same IP compose the same way. `UartSimHarness` owns a
`DeviceBus` over its bridge (`h.add_device(...)`, `h["pumice0"]`). See
`test_device_bus.py` for a board-less proof (two pumice by name). `Device` is the
thin convention on top: subclass it per IP, add that IP's operations, and a
multi-DMA system reads as `stream0.<op>` / `stream1.<op>`. Reference subclass:
STREAM's `Stream`
(`projects/NexysA7/stream_characterization/flows-stream-bridge/host/stream_device.py`)
adds descriptor-RAM programming + kick + channel status/enable, all by name. The
transport spine and the byte-stream equivalence boundary are unchanged — only the
base address and regmap differ per instance, so the same objects drive sim + FPGA.

The shared RTL bridge (`UARTAxiBridge`, ASCII `W/R` protocol) lives in
`projects/components/converters/bin/uart_axi_bridge.py` and takes an injected
`channel=` (default pyserial; pass a `CocotbUartChannel` for sim).

## Using it in a new characterization flow

1. Describe your harness CSR in a `<name>_csr.rdl` and generate the regmap:
   `python3 bin/peakrdl_generate.py <name>_csr.rdl --regmap --docs-only --no-html --no-markdown`
2. Host driver:
   ```python
   from uart_axi_bridge import UARTAxiBridge            # converters/bin
   from TBClasses.harness.uart_register_map import UartRegisterMap
   bridge = UARTAxiBridge(port="/dev/ttyUSB1")           # or channel=... for sim
   regs   = UartRegisterMap(bridge, start_address=HARNESS_BASE,
                            regmap_file=".../<name>_csr_regmap.py")
   ```
3. Sim: a cocotb tb_top exposing `i_uart_rx`/`o_uart_tx`; then
   ```python
   from TBClasses.harness.cocotb_axil_bridge import make_uart_channel
   chan = make_uart_channel(dut, dut.aclk, CLKS_PER_BIT)
   drv  = MyDriver(bridge=UARTAxiBridge(channel=chan))   # same driver as silicon
   result = await cocotb.external(my_program)(drv)
   ```

Reference implementations:
- `projects/NexysA7/ddr2-characterization/` (host `flows-ours-uart/host/`, sim
  `ddr2_char_framework/dv/tests/test_ddr2_char_uart.py`) — DFI-model backend.
- `projects/NexysA7/cdc_counter_display/` (host `host/cdc_demo.py` +
  `cdc_programs.py`, sim `dv/tests/test_cdc_demo_uart.py`, CSR
  `rtl/cdc_demo_csr.rdl`) — a compact example whose sim swaps the unsimulatable
  MMCM/BUFGMUX clock tree for behavioral co-prime `ctr_clk`s.
