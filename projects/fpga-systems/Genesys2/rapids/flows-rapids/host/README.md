# RAPIDS beats Characterization — Host Tools

Host-side Python for driving the `rapids_byte_top` bitstream on a Digilent
Nexys A7-100T over a single 115200-8N1 UART link. This is board automation; it
requires real hardware (an FPGA flashed with the bitstream and a USB-UART).

The host runs the **same on-chip self-check** the cocotb harness testbench
(`../dv/rapids_byte_harness_tb.py`) verifies in simulation, just over UART
instead of poking DUT ports directly.

## Requirements

```bash
source env_python            # from the repo root: sets PYTHONPATH + provides
                             # CocoTBFramework (needed by RegisterMap) + pyserial
```

- `pyserial` — the UART driver (bundled in the repo venv / env_python).
- `RegisterMap` (`bin/TBClasses/apb/register_map.py`) — for by-name DUT register
  access. It reads the generated `projects/components/dma-ip/rapids/rtl/rapids_regmap.py`.
- `UARTAxiBridge` (`projects/fpga-systems/bin/uart_axi_bridge.py`) — the
  existing ASCII UART <-> AXIL wire driver; reused as-is, not re-implemented.

## Files

| File | Purpose |
|------|---------|
| `rapids_byte_io.py` | UART transport + AXIL region map. Wraps `UARTAxiBridge`; provides `axil_read/write`, region helpers (`dut_reg_*`, `desc_*`, `csr_*`), `load_descriptor`, and the by-name register helpers (`csr_read_reg`, `csr_write_reg`, `csr_field`, `desc_*_reg`). No offsets live in the host code. |
| `descriptor_builder.py` | Builds 256-bit RAPIDS descriptors (DATA / CTRL_READ / CTRL_WRITE) per `rapids_pkg.sv`; `descriptor_to_words()` splits into the 8 x 32-bit DESC-LOAD words. |
| `run_characterization.py` | The campaign: configure both halves by name, load descriptors, run SINK + SOURCE passes, print PASS/FAIL per channel. |
| `dump_status.py` | Read + pretty-print the STATUS bitfield, beat-count totals, sched-error words, and per-channel CRC arrays. |

## AXIL regions (all register access is BY NAME)

The AXIL address space is split into four regions, selected by the host
address bits above `REGION_SHIFT`. The region indices, the half select inside
the DUT-REG and observer regions, and the shifts are generated into
`rtl/rapids_harness_map.py` by `bin/gen_rapids_harness_regmap.py`, which also
checks them against the `REGION_*` localparams in `rtl/rapids_byte_harness.sv`.
Nothing in `host/` carries a literal register offset; register names resolve
through the regmaps below.

| Region | Register map | Contents |
|--------|--------------|----------|
| DUT-REG (`APB`) | `projects/components/dma-ip/rapids/rtl/rapids_regmap.py`, one `RegisterMap` per half (`src` / `snk`) | AXIL -> `apb4_master` -> the DUT's APB: config, idle/error/reset registers, and the per-half kick windows. |
| DESC-LOAD (`DESC`) | `rtl/rapids_harness_desc_regmap.py` | `DESC_WORD*`, `DESC_ADDR`, `DESC_KICK`, `DESC_STATUS`: a write to `DESC_KICK` issues one AXI4 write into the descriptor RAM. |
| HARNESS CSR (`CSR`) | `rtl/rapids_harness_csr_regmap.py` | gen / chk / mem / mon control, KICK_* sequencer, `RESP_DELAY`, `BUILD`, `STATUS`, counters, per-channel CRC arrays (indexed by `CH_SEL`). `CTRL` reads back the ID. |
| OBSERVERS (`OBS`) | `projects/components/utility-ip/misc/rtl/regs/generated/obs_regs_top_regmap.py` | the interface observers (`USE_OBSERVERS=1` builds only). |

`RESP_DELAY` programs the memory-latency model on the R and B channels;
`run_characterization.py --suite-delay` sweeps it.

## Usage

```bash
# Sanity + full campaign (SINK then SOURCE). --channels MUST match the built
# NUM_CHANNELS (RAPIDS_NUM_CHANNELS in the Vivado build; default 4).
./run_characterization.py --port /dev/ttyUSB1 --channels 4 --active 4 --beats 8 -v

# One pass only
./run_characterization.py --sink-only   --channels 4
./run_characterization.py --source-only --channels 4

# Snapshot the CSR block
./dump_status.py --port /dev/ttyUSB1 --channels 4
```

Exit code from `run_characterization.py`: `0` = all pass, `1` = a self-check
failed, `2` = no UART link / wrong ID.

## What the campaign checks

Both passes rely on the harness's shared LFSR (`0xDEADBEEF`) + CRC-32 so the
on-chip blocks self-check per channel:

- **SINK** (`s_axis` -> sink -> `m_axi_wr`): `GEN_EXPECTED_CRC[ch] == WR_CRC_VALUE[ch]`.
- **SOURCE** (`m_axi_rd` -> source -> `m_axis`): `RD_CRC_VALUE[ch] == CHK_ACTUAL_CRC[ch]`, with `data_error == 0`.

Config (scheduler, descriptor engine, AXI transfer, channel enables) is
programmed **by name** through `RegisterMap`, split-proof against register-map
edits — never by hardcoded offset.
