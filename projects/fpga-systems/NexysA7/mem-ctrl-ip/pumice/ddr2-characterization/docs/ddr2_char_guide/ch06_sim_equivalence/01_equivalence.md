# Simulation / Silicon Equivalence

This project follows the shared UART-characterization methodology
(`bin/TBClasses/harness/`): **one authored-once host program runs byte-for-byte
identically on the FPGA and in a cocotb simulation.** The equivalence boundary is
the ASCII `W/R` byte stream on the UART wire; only the bottom `ByteChannel`
differs — `SerialChannel` (pyserial) on the board vs `CocotbUartChannel` on the
DUT pins in sim.

## Testbenches

| tb_top | Wraps | Drives cfg via |
|--------|-------|----------------|
| `ddr2_char_uart_tb_top.sv` | the **full** `ddr2_char_harness` (real UART bridge + harness_csr + 1→N bridge + engines + pumice) | the real UART pins (cocotb `UARTMaster`/`Monitor`) |
| `ddr2_char_macro_tb_top.sv` | the inner `ddr2_char_macro` | direct ports + an APB BFM |

: Simulation testbenches

The UART tb is the equivalence vehicle: it exposes real UART pins so the sim
consumes the identical byte stream the host sends to silicon. The DFI side is
wired to internal `phy_dfi_*` nets so the framework's `DFISlavePHY` + `MemoryModel`
loopback auto-binds by prefix. **There is no a7ddrphy in sim** — it reproduces
the digital DFI handshake, not the analog eye.

## How the same program runs in sim

`test_ddr2_char_uart.py` builds the `DFISlavePHY` + `MemoryModel` backend, then:

```python
r = await cocotb.external(prog)()   # prog is an UNMODIFIED pumice_master routine
```

`make_uart_channel(dut, clock, clks_per_bit)` returns a `CocotbUartChannel` that
drives the UART pins; the synchronous host program runs in a worker thread under
`cocotb.external`, and the channel's read/write are `cocotb.function` wrappers
that step the sim. The baud is lowered for sim (`UART_BAUD = 6_250_000` →
`CLKS_PER_BIT = 16` vs 868 on board) — bit-timing only, the byte stream is
unchanged. `make sim` / `sim-smoke` / `sim-simple` / `sim-level` run the same
programs the board runs.

## Match the board's exact DFI config

`GEAR_RATIO = log2(DFI_RATE)` and **must** match the compile-time `DFI_RATE` or
reads corrupt. The test threads `TEST_DFI_RATE` / `TEST_GEAR_RATIO` /
`TEST_DRAM_BEAT_BYTES` into both the SV `parameters={...}` and the host via
`drv.set_dfi_phase(...)`. The board is built at `DFI_RATE = 4` (GEAR = 2, AXI 64 /
DRAM beat 32); a rate-2 / GEAR-1 sim will **pass while the board fails** — it
skips the very paths that break. Named variants
(`..._smoke_rate4`, `..._smoke_rate4_x16`, `..._pagehit_rate4_x16`, …) exist to
run the board's real geometry.

## What the sim can and cannot reproduce

- **CAN:** everything digital — the controller/engines, the bridge RTL,
  DFI-level handshakes, register logic. This is where it earns its keep.
- **CANNOT:** analog PHY behavior. Xilinx SERDES/IDELAY in a7ddrphy do not
  simulate, so read-eye / DQS-gate / pin-LOC problems are silicon-only.
