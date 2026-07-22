# Simulation vs Silicon

RAPIDS characterization reaches the **same golden CRC** two ways — but, unlike
the ddr2/stream siblings, **the simulation does not run the host over a
simulated UART.** The UART bridge and CSR router live only in the board top
(`rapids_char_top.sv`); the cocotb DUT top is the harness
(`rapids_char_harness`), and the testbench drives its control surface directly.

## The two paths

| | Silicon | Simulation |
|--|---------|-----------|
| Config | host `RegisterMap` over UART → APB | cocotb `RegisterMap` over the harness APB port |
| Descriptors | host DESC-LOAD region → descriptor RAM | cocotb 256-bit AXI4 host-write port |
| Kick | host `CSR_GO` atomic launch | cocotb per-half `apbtodescr` kick windows |
| Data paths | all on-chip (harness gen/check/mem) | the same on-chip blocks, elaborated in Verilator |
| Pass criterion | golden CRC match (host `rapids_char_golden.py`) | golden CRC match (checker CRC == expected) |

: The two characterization paths

The equivalence is by **shared logic**, not a shared transport: the same by-name
DUT config (`rapids_regmap.py`), the same descriptor bytes (the TB's
`create_descriptor()` mirrors `flows-rapids-beats/host/descriptor_builder.py`), and the same golden
CRC-32 asserted in both places.

## The cocotb testbench

- **DUT top:** `rapids_char_harness` (Verilator). Runner
  `flows-rapids-beats/dv/test_rapids_char_harness.py`; TB class `RapidsCharHarnessTB`
  (`flows-rapids-beats/dv/rapids_char_harness_tb.py`).
- **Two self-checks:**
  - `cocotb_test_sink_selfcheck` — `s_axis → sink → m_axi_wr`; asserts
    `wr_crc[ch] == gen_expected_crc[ch]` for each active channel.
  - `cocotb_test_source_selfcheck` — `m_axi_rd → source → m_axis`; asserts
    `chk_actual_crc[ch] == rd_crc[ch]` and `data_error == 0`.
- **Params:** `NUM_CHANNELS=8` (env `TEST_NUM_CHANNELS`), `NUM_ACTIVE=4`,
  `NUM_BEATS=8`, `DATA_WIDTH=512`, `SRAM_DEPTH=512`. Waves via `WAVES=1`.
- **Gate:** `make verify-sim` runs the sink self-check before a bitstream build,
  so a broken elaboration is caught before a long Vivado run.

## Why no UART-in-sim here

The harness data paths are entirely on-chip, so there is nothing for a simulated
host to *drive* beyond the control surface — the TB pokes that surface directly
(APB + descriptor RAM + kick) and reads back the same CRCs the board's host
reads over UART. If a UART-level equivalence sim is wanted later, the shared
`make_uart_channel` / `CocotbUartChannel` collateral in `bin/TBClasses/harness/`
(used by ddr2/stream) can wrap the board top — but it is not wired today.
