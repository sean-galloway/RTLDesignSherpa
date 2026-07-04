# RAPIDS beats Characterization — Host Tools

Host-side Python for driving the `rapids_char_top` bitstream on a Digilent
Nexys A7-100T over a single 115200-8N1 UART link. This is board automation; it
requires real hardware (an FPGA flashed with the bitstream and a USB-UART).

The host runs the **same on-chip self-check** the cocotb harness testbench
(`../dv/rapids_char_harness_tb.py`) verifies in simulation, just over UART
instead of poking DUT ports directly.

## Requirements

```bash
source env_python            # from the repo root: sets PYTHONPATH + provides
                             # CocoTBFramework (needed by RegisterMap) + pyserial
```

- `pyserial` — the UART driver (bundled in the repo venv / env_python).
- `RegisterMap` (`bin/TBClasses/apb/register_map.py`) — for by-name DUT register
  access. It reads the generated `projects/components/rapids/rtl/rapids_regmap.py`.
- `UARTAxiBridge` (`projects/components/converters/bin/uart_axi_bridge.py`) — the
  existing ASCII UART <-> AXIL wire driver; reused as-is, not re-implemented.

## Files

| File | Purpose |
|------|---------|
| `rapids_char_io.py` | UART transport + AXIL region map. Wraps `UARTAxiBridge`; provides `axil_read/write`, region helpers (`dut_reg_*`, `desc_*`, `csr_*`), `load_descriptor`, and all CSR offset constants. |
| `descriptor_builder.py` | Builds 256-bit RAPIDS descriptors (DATA / CTRL_READ / CTRL_WRITE) per `rapids_pkg.sv`; `descriptor_to_words()` splits into the 8 x 32-bit DESC-LOAD words. |
| `run_characterization.py` | The campaign: configure both halves by name, load descriptors, run SINK + SOURCE passes, print PASS/FAIL per channel. |
| `dump_status.py` | Read + pretty-print the STATUS bitfield, beat-count totals, sched-error words, and per-channel CRC arrays. |

## AXIL word-address map (region = host addr bits [19:16])

| Region | Base | Contents |
|--------|------|----------|
| `0x0_0000` DUT-REG | APB byte addr `addr[12:0]` | AXIL -> `apb_master` -> harness `s_apb`. SRC config @ `0x0000`, SNK config @ `0x1000` (half = APB `addr[12]`), plus the per-half `apbtodescr` kick windows (`base + ch*8` = LOW, `+4` = HIGH). |
| `0x1_0000` DESC-LOAD | byte offsets | `DESC_WORD[0..7]` @ `0x00..0x1C`, `DESC_ADDR` @ `0x20`, `DESC_KICK` @ `0x24` (write issues one AXI4 write into the descriptor RAM; `data[0]` selects SRC=0 / SNK=1), `DESC_STATUS` @ `0x28` (read: `[0]` = last BRESP OK). |
| `0x2_0000` HARNESS CSR | byte offsets | gen/chk/mem/mon control + status readback. `ID` @ `0x00` = `0x52415031` ("RAP1"); `STATUS` @ `0x80`; beat totals @ `0x84-0x94`; sched errors @ `0x98/0x9C`; per-channel CRC arrays @ `0xA0-0xAC` indexed by `CH_SEL` @ `0x60`; valid masks @ `0xB0-0xBC`. |

These offsets are taken directly from the `rapids_char_top.sv` header.

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
