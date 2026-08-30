# Simulation / Silicon Equivalence

The primary `flows-stream-bridge` flow has a real **UART-equivalence** cocotb
sim: the testbench drives the *same* `uart_axil_bridge` RTL over the *same* ASCII
`W/R` byte stream the FPGA host uses, and the extended-addressing tests run the
*same* Python host programs. Only the bottom transport differs.

## The testbench

- **TB:** `flows-stream-bridge/dv/tbclasses/stream_char_tb.py` (`StreamCharTB`).
  Drives `i_uart_rx` / `o_uart_tx` via the CocoTBFramework `UARTMaster` /
  `UARTMonitor` BFMs; `UART_BAUD` is raised (`CLKS_PER_BIT = 8`) for sim speed —
  bit-timing only, the byte stream is unchanged. Registers are addressed by name
  (`stream_addrs.A`, `harness_addrs.H`).
- **Backend model:** the real harness RTL, elaborated in Verilator —
  `axi4_dma_slaves` (LFSR pattern-gen source + CRC-check sink),
  `axi_response_delay`, `axi4_dma_observer`. Descriptors are built by the shared
  `flows-stream-bridge/host/descriptor_builder.py`.
- **Running the actual host program in sim:** the ext-addressing tests execute
  `stream_ext_suite.run_suite` / `stream_ext_char` under
  `await cocotb.external(program)()`, with a `_Bridge` shim wrapping
  `cocotb.function(uart_write / uart_read)` — the shared harness methodology (a
  `cocotb.function` transport, **not** a free-running pump). This is the
  same-source silicon-equivalence path.

## Test levels

`flows-stream-bridge/dv/tests/test_stream_char.py` runs by `TEST_LEVEL`:

| Level | Cocotb tests |
|-------|-------------|
| gate | `ping` |
| func | + `desc_load`, `csr_read`, `apb_config`, `desc_perf`, `rw_perf`, `obs_equiv`, `dma_1ch`, `dma_2ch` |
| full | + `dma_3ch … dma_Nch`, `compress_char` |

: cocotb test levels

Plus `test_stream_char_ext_suite` / `test_stream_char_ext_char` (the
run-the-host-program tests) and host-side unit tests
(`flows-stream-bridge/host/test_harness_regmap.py`, `test_stream_device.py`, `test_mon_configs.py`, …).
Sim params (`BASE_RTL_PARAMS`): `NUM_CHANNELS = 4` (down from 8 for Artix BRAM),
`DATA_WIDTH = 128`, `DESC_RAM_ENTRIES = 128`, `DEBUG_SRAM_WORDS = 4096`,
`USE_MON_COMPRESSION = 1`. `make bitstream` runs a `verify-sim` gate
(`-k "ping or csr_read"`) so a broken elaboration is caught before a long build.

## Sibling flows

- `flows-idma-bridge` has a cocotb **cosim** (`make perf` / `make desc-overhead`)
  but not the UART harness.
- `flows-vivado-mcdma` has **no** cocotb — the MCDMA IP is VHDL and Verilator
  cannot simulate it, so that flow is FPGA-only (rationale in its `dv/README.md`).

The shared collateral in `bin/TBClasses/harness/` (`byte_channel.py`,
`uart_register_map.py`, `cocotb_axil_bridge.py` with `make_uart_channel`,
`device.py`, `harness.py`) is the basis this TB builds on.
