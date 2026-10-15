# DDR2 Characterization Harness — Address Map (pumice build)

Authoritative source: the RTL. This document mirrors the register decoding for
convenience. If you find a mismatch, fix the host driver and this page to match
`harness_csr.sv` and `bridge_ddr2_char_axil.toml`.

A rendered version of this map lives in the FPGA-system book:
`docs/pumice_fpga_system/ch02_harness/02_address_map.md` (Figure 2.2).

---

## Bridge (1 master × 6 slaves)

Source: `ddr2_char_framework/rtl/bridges/configs/bridge_ddr2_char_axil.toml`.

| Slave | Base | Size | Protocol | Purpose |
|---|---:|---:|---|---|
| `ddr2_apb` | `0x0000_0000` | 4 KB | APB | pumice controller CSR (PeakRDL-generated) |
| `harness_csr` | `0x0001_0000` | 4 KB | AXIL | Harness ctrl / status / timer / perf / build identity |
| `debug_sram` | `0x0004_0000` | 256 KB | AXIL 64b | MonBus / DFI trace ring |
| `dfi_mon_ram` | `0x0008_0000` | 4 KB | AXIL | DFI cmd observability placeholder |
| `obs_apb` | `0x0009_0000` | 4 KB | APB | Expansion slot; tied off on this build |
| `chargen_apb` | `0x000A_0000` | 4 KB | APB | Per-generator config, status, and `GO` |

The 256 KB `debug_sram` window spans `0x40000..0x7FFFF`, so `dfi_mon_ram` sits
at `0x80000` (not `0x50000`) to avoid overlap. The `0x00020000..0x0003FFFF`
slot used to hold `desc_ram`; it is unallocated now that the pattern-gen engines
cover the workload class the descriptor mode was reserved for.

> **Note (this build):** the `debug_sram` *backing store* is shrunk to
> `DEBUG_SRAM_WORDS=512` (256 x 64-bit = 2 KB). The full-size ring would have
> needed ~44 K LUT-as-distributed-RAM cells -- 2.4x over the Artix-7 100T's
> 19 K sites -- which blocked `place_design`; the trace ring is not used on this
> build. The 256 KB address *window* is unchanged (accesses above 2 KB alias
> into the ring). Raise `DEBUG_SRAM_WORDS` in `ddr2_char_harness.sv` to restore
> the full trace if the target device has the headroom.

---

## harness_csr register map (offsets from `0x0001_0000`)

Source: `projects/fpga-systems/rtl/mem_char_framework/rtl/harness_csr.sv`.
Every address unlisted here reads as 0 and ignores writes.

### Harness ctrl / status

| Off | Reg | R/W | Bits |
|---:|---|:---:|---|
| `0x00` | `CTRL` | RW | [0]/[1] retired (`start_wr`/`start_rd`); [2] `clear_stats`; [3] `freeze_trace`; [4] `soft_reset` |
| `0x04` | `STATUS` | R | [0] `wr_done`; [1] `rd_done`; [2] `wr_error`; [3] `rd_error`; [4] `any_error`; [5] `dbg_clear_busy`; [6] `init_done`; [7] `init_fail` |
| `0x08` | `DBG_WR_PTR` | R | Words written to `debug_sram` since last clear |
| `0x0C` | `DBG_OVERFLOW` | R | [0] sticky trace-overflow flag |
| `0x10` | `CRC_EXPECTED` | R | **Retired**, reads 0 |
| `0x14` | `CRC_ACTUAL` | R | **Retired**, reads 0 |
| `0x18` | `CRC_MATCH` | R | [0] whole-run `exp==act` |
| `0x1C` | `SCRATCH` | RW | Host bring-up ping |
| `0x20` | `BUILD_ID` | R | `0x44445232` ("DDR2") |
| `0x24` | `BEATS_MISM` | R | **Retired**, reads 0 |

### Characterization timer

| Off | Reg | R/W | Notes |
|---:|---|:---:|---|
| `0x28` | `TIMER_CTRL` | W | [0] clear-pulse |
| `0x2C` | `TIMER_STATUS` | R | [0] `done`; [1] `running`; [2] `pass` |
| `0x30` | `TIMER_CYCLES_LO` | R | Low 32b of 64b cycle counter |
| `0x34` | `TIMER_CYCLES_HI` | R | High 32b |
| `0x38` | `TIMER_EXP_BEATS` | RW | Beat-count stop trigger; 0 = disable |
| `0x3C` | `RESP_DELAY` | RW | Present but **unwired** on this build |
| `0x40`–`0x5C` | `TIMER_{R,W}_{FIRST,LAST}_{LO,HI}` | R | First/last R/W beat timestamps |

### Runtime controller cfg

| Off | Reg | R/W | Bit-packing |
|---:|---|:---:|---|
| `0x60` | `CTRLR_CFG` | RW | [0] memtype; [15:8] `t_phy_wrlat`; [23:16] `t_rddata_en`; [24] `rd_in_order` |
| `0x64` | `CTRLR_CAP` | RW | [3:0] `cap_lookahead_max`; [7:4] `cap_synth_mask` |
| `0x68` | `DFI_TUNING` | RW | [3:0] `cmd_delay`; [7:4] `rddata_delay` |

### a7ddrphy calibration CSR passthrough (`0x80`–`0x8C`)

| Off | Reg | R/W | Notes |
|---:|---|:---:|---|
| `0x80` | `PHY_CSR_ADDR` | RW | [9:0] a7ddrphy CSR word index |
| `0x84` | `PHY_CSR_WDATA` | RW | 32b value to write |
| `0x88` | `PHY_CSR_CTRL` | W | [0] pulse → drive one CSR-bus write |
| `0x8C` | `PHY_CSR_RDATA` | R | a7ddrphy `dat_r` for current `PHY_CSR_ADDR` |

### Retired engine-cfg region

`0x100`–`0x1AF` is a **retired** hole; reads return 0. The per-generator config
that replaced it lives in `chargen_regs` at `0x000A0000`.

### Perf observability (`0x1C0`–`0x1E8`)

All 32b. Cleared by `CTRL.clear_stats`; frozen by `CTRL.freeze_trace`.

| Off | Reg | R/W | Notes |
|---:|---|:---:|---|
| `0x1C0` | `OBS_RD_PROD` | R | RD data-channel productive cycles |
| `0x1C4` | `OBS_RD_BP` | R | RD backpressure |
| `0x1C8` | `OBS_RD_STARV` | R | RD starvation |
| `0x1CC` | `OBS_RD_IDLE` | R | RD idle |
| `0x1D0` | `OBS_WR_PROD` | R | WR productive |
| `0x1D4` | `OBS_WR_BP` | R | WR backpressure |
| `0x1D8` | `OBS_WR_STARV` | R | WR starvation |
| `0x1DC` | `OBS_WR_IDLE` | R | WR idle |
| `0x1E0` | `OBS_HIST_SEL` | RW | [0] bus; [1] metric; [5:2] bin |
| `0x1E4` | `OBS_HIST_COUNT` | R | Selected bin count |
| `0x1E8` | `OBS_HIST_TOTAL` | R | Total txns on selected metric |

Bin `b` covers `[2^b, 2^(b+1))` cycles (16 bins → 0..15 cycles for b=0 up to
32K..64K cycles for b=15).

### Build identity (`0x1EC`–`0x1F8`)

| Off | Reg | R/W | Notes |
|---:|---|:---:|---|
| `0x1EC` | `BUILD_VERSION` | R | Functional build number |
| `0x1F0` | `BUILD_CONFIG` | R | `dfi_rate`, `gear_ratio`, `dram_bl`, `row_width`, `bank_width` |
| `0x1F4` | `BUILD_DATA_CFG` | R | `axi_data_width`, `dram_beat_width`, `dram_device_width` |
| `0x1F8` | `BUILD_CLK_HZ` | R | Sys/AXI clock this build was compiled for |

---

## UART bridge wire protocol

Source: `projects/components/utility-ip/converters/rtl/uart_to_axil4/uart_axil_bridge.sv`.
ASCII, line-based, 115200 8N1 by default (change with the `UART_BAUD`
harness parameter and rebuild).

### Write
```
W <hex-addr-32b> <hex-data-32b>\n
```
FPGA replies `OK\n` after BRESP=OKAY.

### Read
```
R <hex-addr-32b>\n
```
FPGA replies `0x<hex-data-32b>\n`.

Both hex fields are big-endian, zero-padded to 8 digits, case-insensitive.
The Python `UARTAxiBridge` class (`projects/components/utility-ip/converters/bin/
uart_axi_bridge.py`) handles the framing.
