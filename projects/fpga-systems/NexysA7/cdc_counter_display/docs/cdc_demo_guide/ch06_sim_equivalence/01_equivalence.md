# Simulation / Silicon Equivalence

This project follows the shared Nexys A7 UART-characterization methodology
(`bin/TBClasses/harness/`): **one authored-once host program runs byte-for-byte
identically on the FPGA and in a cocotb simulation.** The equivalence boundary is
the ASCII `W/R` byte stream on the UART wire — if the same program emits the same
bytes, the same `uart_axil_bridge` RTL decodes them the same way on silicon and
in sim.

## The layered stack (only the bottom layer differs)

```
Programs   cdc_programs.py            authored once, unchanged FPGA/sim
Driver     CdcDemoDriver + UartRegisterMap   by-name registers
Protocol   UARTAxiBridge (W/R ASCII)  same code both sides
-- byte stream ---------------------------------------------------------
Channel    SerialChannel (pyserial)  |  CocotbUartChannel (cocotb)
Wire       FTDI/USB UART             |  UARTMaster/Monitor on DUT pins
```

The bridge is **injectable**: `CdcDemoDriver(port=...)` opens a real serial port;
`CdcDemoDriver(bridge=UARTAxiBridge(channel=cocotb_channel))` drives the sim.
Nothing above the wire forks.

## How the sim runs the same program

`dv/tb/cdc_demo_uart_tb_top.sv` wraps the **real** `uart_axil_bridge` +
`cdc_demo_harness` + four `cdc_counter_domain` instances. `dv/tests/test_cdc_demo_uart.py`:

1. Starts `aclk` and reset, and drives the four `ctr_clk[i]` at co-prime periods.
2. Builds a `CocotbUartChannel` via `make_uart_channel(dut, dut.aclk, CLKS_PER_BIT)`.
3. Constructs `CdcDemoDriver(bridge=UARTAxiBridge(channel=chan))`.
4. Runs the unmodified `cdc_programs.*` functions inside `cocotb.external(...)`.

The synchronous host program runs in a worker thread; the channel's read/write
are `cocotb.function` wrappers that drive the UART master and advance simulation
time. The four cocotb tests (smoke, press, cfg_load, cdc_mode) assert the same
results the CLI checks on the board.

## What the sim can and cannot reproduce

- **CAN:** everything digital — the bridge RTL, CSR decode, per-counter CDC
  datapaths, register logic. The sim proves the byte protocol and the harness
  contract before you ever touch the board.
- **CANNOT:** the analog clock tree. `cdc_demo_top`'s `MMCME2_BASE` /
  `BUFGMUX_CTRL` / `IBUF` / `BUFG` do not simulate in Verilator, so the tb_top
  drives `ctr_clk[i]` behaviorally instead. Consequently the NO-CDC "garbage
  read" is a silicon-only effect — in Verilator (no metastability) mode 0 reads
  the true value, so the sim asserts exact values in NO-CDC while the board shows
  scramble at speed.

## Gotchas worth keeping

- **Lower `CLKS_PER_BIT` in sim** (16, in both the tb_top param and the BFM) —
  bit-timing only, the byte stream is unchanged, so equivalence holds.
- **Wrap the full harness, not the inner block** — the real `uart_axil_bridge` +
  `cdc_demo_harness` must be in the DUT, or the two flows are only "vaguely
  similar," not equivalent.
- **Use `cocotb.function`, not a free-running pump** — a pump coroutine plus
  thread queues stalls the scheduler; `cocotb.function` is what steps the sim
  from worker-thread calls.
