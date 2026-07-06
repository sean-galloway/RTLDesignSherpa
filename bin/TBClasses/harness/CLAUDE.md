# CLAUDE.md — UART-AXIL characterization harness methodology

Agent guidance for `TBClasses.harness`: how to make one host program run
byte-for-byte identically against an FPGA **and** a cocotb sim, and the
non-obvious traps that cost real debugging time. Read this before adding a
sim-equivalence layer to a characterization flow (ddr2 / stream / cdc / new).

The `README.md` here is the usage recipe; this file is the *why* + the *don'ts*.

---

## The one principle

**The equivalence boundary is the ASCII byte stream on the UART wire.** The host
`UARTAxiBridge` emits `"W <hex> <hex>\n"` / `"R <hex>\n"` and the RTL
`uart_axil_bridge.sv` decodes exactly that. If the same program produces the same
bytes, the same bridge RTL decodes them the same way on silicon and in sim.
"Equivalent" means **same bytes**, NOT same bit-timing — sim may lower the baud.

Consequence: nothing above the wire may fork. There is ONE host program; only the
bottom `ByteChannel` differs (pyserial vs a cocotb `UARTMaster`). Do not write a
"sim version" of the driver/programs — inject a different channel.

## Layers (only the bottom one differs)

```
Programs (authored once)            e.g. pumice_master.py — UNCHANGED across FPGA/sim
Driver (by-name registers)          DDR2CharDriver + UartRegisterMap
Protocol (W/R ASCII)                UARTAxiBridge          [same code both sides]
── byte stream ───────────────────────────────────────────────────────────────
ByteChannel        SerialChannel (pyserial)   |   CocotbUartChannel (cocotb)
Wire               FTDI/USB UART              |   UARTMaster/Monitor on DUT pins
```

Registers are accessed BY NAME (`regs.write("CTRL", start_wr=1)`), never by
hardcoded offset — describe the CSR in a `<top>_csr.rdl`, generate `<top>_regmap.py`
with `bin/peakrdl_generate.py --regmap`, hand it to `UartRegisterMap`.

**Multiple instances of an IP** are the base-address argument, not a new layer:
make N `UartRegisterMap`s at N `start_address` windows over one shared bridge (or
N bridges). `device.Device` wraps that into a named instance object; subclass it
per IP (add that IP's ops) so a multi-DMA system reads `stream0.<op>` /
`stream1.<op>` — see STREAM's `Stream`. Nothing is a singleton; the transport
spine and byte-stream equivalence boundary are unchanged.

## Standing up a new flow — order that works

1. RDL for the harness CSR -> generate regmap (`--regmap --docs-only --no-html
   --no-markdown`). Add a consistency test parsing the SV header vs the regmap.
2. Make the driver + bridge injectable: `UARTAxiBridge(channel=...)`,
   `Driver(bridge=...)`. Prove board-lessly with a mock bridge first.
3. New cocotb tb_top wrapping the **full harness** (real UART bridge + harness_csr
   + engines + DUT), DFI/backend to a model. Bring it up with UART idle first.
4. Add `make_uart_channel` + run the UNMODIFIED program via `cocotb.external`.
5. `make sim` runs the same program in sim; the silicon target is unchanged.

## Gotchas (each of these cost hours — do not relearn them)

- **Sync/async bridge = `cocotb.function`, NOT a pump.** The program is synchronous;
  run it in a worker thread via `cocotb.external`, and make the channel's
  read/write `cocotb.function` wrappers that drive the UARTMaster/Monitor and
  advance sim. A free-running pump coroutine + thread `queue`s STALLS the scheduler
  (observed: 3 ns/s). `cocotb.function` is the inverse of `cocotb.external` and is
  the only thing that steps the sim from worker-thread calls.
- **Lower `CLKS_PER_BIT` in sim.** At 868 clks/bit a 20-byte command is ~174k
  clocks. Set it to ~16 (RTL param + BFM `clks_per_bit` together). Changes bit-
  timing only, not the byte stream — equivalence holds.
- **Match the FPGA's EXACT config in sim** (DFI rate, GEAR / DRAM beat width, widths).
  A "close enough" sim (e.g. rate-2/GEAR-1 when the board is rate-4/GEAR-2) will
  PASS while the board fails — it skips the very paths that break. The GEAR>1
  column-address bug was invisible until the sim ran the board's real config.
- **Wrap the FULL harness, not the inner macro.** The macro's direct-cfg/APB
  front-end is a different path; using it makes the two flows "vaguely similar,"
  not equivalent. The real `uart_axil_bridge` + `harness_csr` must be in the DUT.
- **`wait_*` / status: any_error is STICKY and cleared by `clear_stats`, NOT
  `soft_reset`.** A failed read latches rd_error; every subsequent `wait_engine`
  then returns False and looks like a hardware "wedge" that isn't one. Clear it.
- **Don't hand-roll W/R formatting in a sim-only bridge** — reuse `UARTAxiBridge`
  via channel injection, or the byte streams drift.

## What this can and cannot reproduce

- CAN: everything digital — the controller/engines, the bridge RTL, DFI-level
  handshakes, register logic. This is where it earns its keep (it turned a
  board-only, damaging-to-iterate bug into a Verilator repro + a one-line fix).
- CANNOT: analog PHY behaviour. Xilinx SERDES/IDELAY (a7ddrphy: OSERDESE2/
  ISERDESE2/IDELAYE2) do not simulate in verilator, so the sim connects at the
  DFI level with a behavioral model. Read-eye / DQS-gate / pin-LOC problems are
  silicon-only — don't expect the sim to show them.

## Reference implementation

`projects/NexysA7/ddr2-characterization/`: host `flows-ours-uart/host/`
(`ddr2_char.py`, `pumice_master.py`), sim
`ddr2_char_framework/dv/tests/test_ddr2_char_uart.py` (tb_top +
`make_uart_channel` + `cocotb.external`), RDL `ddr2_char_framework/rtl/harness_csr.rdl`.
CDC (`cdc_counter_display`) is a second worked example (host `host/cdc_demo.py` +
`cdc_programs.py`, sim `dv/tests/test_cdc_demo_uart.py`, CSR `rtl/cdc_demo_csr.rdl`);
its sim swaps the unsimulatable MMCM/BUFGMUX clock tree for behavioral co-prime
`ctr_clk`s. STREAM (`stream_characterization`) uses the same spine and can adopt
the sim half the same way.
