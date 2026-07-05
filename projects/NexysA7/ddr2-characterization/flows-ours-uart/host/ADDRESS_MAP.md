# DDR2 Characterization Harness — Address Map

Authoritative source: the RTL. This document mirrors the register decoding for
convenience. If you find a mismatch, fix `ddr2_char.py` to match `harness_csr.sv`
and `bridge_ddr2_char_axil.toml`.

---

## Bridge (1 master × 4 slaves)

Source: `ddr2_char_framework/rtl/bridges/configs/bridge_ddr2_char_axil.toml`.

| Slave         | Base           | Size    | Protocol | Purpose                                           |
|---------------|----------------|---------|----------|---------------------------------------------------|
| `ddr2_apb`    | `0x0000_0000`  | 4 KB    | APB      | ddr2-lpddr2 controller CSR (autogen regs)         |
| `harness_csr` | `0x0001_0000`  | 4 KB    | AXIL     | Harness ctrl + timer + engine cfg + perf readback |
| `debug_sram`  | `0x0004_0000`  | 256 KB  | AXIL 64b | MonBus / DFI trace ring                           |
| `dfi_mon_ram` | `0x0008_0000`  | 4 KB    | AXIL     | Small AXIL ring for DFI cmd observability         |

The 256-KB `debug_sram` window intentionally spans `0x40000..0x7FFFF`, so
`dfi_mon_ram` sits at `0x80000` (not `0x50000`) to avoid overlap. The
`0x00020000..0x0003FFFF` slot used to hold `desc_ram`; it's unallocated
now that the pattern-gen engines cover the workload class the descriptor
mode was reserved for.

> **Note (this build):** the `debug_sram` *backing store* is shrunk to
> `DEBUG_SRAM_WORDS=512` (256 x 64-bit = 2 KB). The full-size ring would have
> needed ~44 K LUT-as-distributed-RAM cells — 2.4x over the Artix-7 100T's
> 19 K sites — which blocked `place_design`; the trace ring is not used on this
> build. The 256-KB address *window* is unchanged (accesses above 2 KB alias
> into the ring). Raise `DEBUG_SRAM_WORDS` in `ddr2_char_harness.sv` to restore
> the full trace if the target device has the headroom.

---

## harness_csr register map (offsets from `0x0001_0000`)

Source: `ddr2_char_framework/rtl/harness_csr.sv`. Every address unlisted
here reads as 0 and ignores writes.

### Harness ctrl / status

| Off  | Reg              | R/W | Bits                                                  |
|------|------------------|-----|-------------------------------------------------------|
| 0x00 | CTRL             | RW  | [0] start_wr (pulse) · [1] start_rd (pulse) · [2] clear_stats (pulse) · [3] freeze_trace (latch) · [4] soft_reset (pulse) |
| 0x04 | STATUS           | R   | [0] wr_done · [1] rd_done · [2] wr_error · [3] rd_error · [4] any_error · [5] dbg_clear_busy · [6] init_done · [7] init_fail |
| 0x08 | DBG_WR_PTR       | R   | Words written to `debug_sram` since last clear        |
| 0x0C | DBG_OVERFLOW     | R   | [0] sticky trace-overflow flag                        |
| 0x10 | CRC_EXPECTED     | R   | WR-engine `o_expected_crc`                            |
| 0x14 | CRC_ACTUAL       | R   | RD-engine `o_actual_crc`                              |
| 0x18 | CRC_MATCH        | R   | [0] exp==act · [1] exp_valid · [2] act_valid · [3] beats_mism!=0 |
| 0x1C | SCRATCH          | RW  | Host bring-up ping                                    |
| 0x20 | BUILD_ID         | R   | `0x44445232` ("DDR2")                                 |
| 0x24 | BEATS_MISM       | R   | `o_beats_mismatched` (RD engine)                      |

### Characterization timer

| Off  | Reg               | R/W | Notes                                             |
|------|-------------------|-----|---------------------------------------------------|
| 0x28 | TIMER_CTRL        | W   | [0] clear-pulse (resets done/cycles/pass)         |
| 0x2C | TIMER_STATUS      | R   | [0] done · [1] running · [2] pass                 |
| 0x30 | TIMER_CYCLES_LO   | R   | Low 32b of 64b cycle counter (10 ns / cycle)      |
| 0x34 | TIMER_CYCLES_HI   | R   | High 32b                                          |
| 0x38 | TIMER_EXP_BEATS   | RW  | Beat-count stop trigger; 0 = disable              |
| 0x3C | RESP_DELAY        | RW  | [15:0] rd_cyc · [31:16] wr_cyc (unwired for now)  |
| 0x40 | TIMER_R_FIRST_LO  | R   | First R-beat stamp (low 32b of 64b timer)         |
| 0x44 | TIMER_R_FIRST_HI  | R   |                                                   |
| 0x48 | TIMER_R_LAST_LO   | R   | Last R-beat stamp                                 |
| 0x4C | TIMER_R_LAST_HI   | R   |                                                   |
| 0x50 | TIMER_W_FIRST_LO  | R   | First W-beat stamp                                |
| 0x54 | TIMER_W_FIRST_HI  | R   |                                                   |
| 0x58 | TIMER_W_LAST_LO   | R   | Last W-beat stamp                                 |
| 0x5C | TIMER_W_LAST_HI   | R   |                                                   |

### Runtime controller cfg

| Off  | Reg        | R/W | Bit-packing                                                                   |
|------|------------|-----|-------------------------------------------------------------------------------|
| 0x60 | CTRLR_CFG  | RW  | [0] memtype (0=DDR2, 1=LPDDR2) · [15:8] t_phy_wrlat · [23:16] t_rddata_en · [24] rd_in_order |
| 0x64 | CTRLR_CAP  | RW  | [3:0] cap_lookahead_max · [7:4] cap_synth_mask                                |

### a7ddrphy calibration CSR passthrough (0x80..0x8C)

Indirect access to the LiteDRAM a7ddrphy's 13 read/write-leveling knobs
(firmware drives leveling — no hardware FSM). Knob map:
`rtl-vivado/a7ddrphy/a7ddrphy_csr_map.txt`. Only meaningful on hardware with
the generated PHY (the sim stub ignores it).

| Off  | Reg           | R/W | Notes                                                          |
|------|---------------|-----|----------------------------------------------------------------|
| 0x80 | PHY_CSR_ADDR  | RW  | [9:0] a7ddrphy CSR word index (the knob to access)             |
| 0x84 | PHY_CSR_WDATA | RW  | 32b value to write to the selected knob                        |
| 0x88 | PHY_CSR_CTRL  | W   | [0] pulse → drive one CSR-bus write (adr=ADDR, dat=WDATA)       |
| 0x8C | PHY_CSR_RDATA | R   | a7ddrphy dat_r for the current PHY_CSR_ADDR                     |

Leveling flow (firmware): set PHY_CSR_ADDR + PHY_CSR_WDATA, pulse PHY_CSR_CTRL
to write a knob; or set PHY_CSR_ADDR and read PHY_CSR_RDATA to sample a status
knob. Sequence per LiteDRAM's read/write-leveling algorithm.

### WR engine cfg (0x100..0x128)

| Off   | Reg              | Bit-packing                                                                                 |
|-------|------------------|---------------------------------------------------------------------------------------------|
| 0x100 | WR_START_ADDR    | 32b address                                                                                 |
| 0x104 | WR_STRIDE_0      | Signed 24b, sign-extended                                                                   |
| 0x108 | WR_STRIDE_1      | Signed 24b                                                                                  |
| 0x10C | WR_WRAP_MASK_0   |                                                                                             |
| 0x110 | WR_WRAP_MASK_1   |                                                                                             |
| 0x114 | WR_BLEN_TXN      | [7:0] burst_len · [23:8] txn_count · [27:24] gap                                            |
| 0x118 | WR_AXI_ATTR      | [7:0] axi_id · [9:8] id_mode · [12:10] axi_size · [14:13] axi_burst · [15] data_mode         |
| 0x11C | WR_LFSR_SEED     |                                                                                             |
| 0x120 | WR_HASH_SEED0    |                                                                                             |
| 0x124 | WR_HASH_SEED1    |                                                                                             |
| 0x128 | WR_HASH_SEED2    |                                                                                             |

### RD engine cfg (0x180..0x1A8)

Identical layout to WR block, addresses shifted by +0x80.

### Perf observability (0x1C0..0x1E8)

All 32b. Cleared by `CTRL.clear_stats`; frozen by `CTRL.freeze_trace`.

| Off   | Reg             | R/W | Notes                                                                        |
|-------|-----------------|-----|------------------------------------------------------------------------------|
| 0x1C0 | OBS_RD_PROD     | R   | RD data-channel meter — productive cycles                                    |
| 0x1C4 | OBS_RD_BP       | R   |                              backpressure                                    |
| 0x1C8 | OBS_RD_STARV    | R   |                              starvation                                      |
| 0x1CC | OBS_RD_IDLE     | R   |                              idle                                            |
| 0x1D0 | OBS_WR_PROD     | R   | WR data-channel meter — productive                                           |
| 0x1D4 | OBS_WR_BP       | R   |                              backpressure                                    |
| 0x1D8 | OBS_WR_STARV    | R   |                              starvation                                      |
| 0x1DC | OBS_WR_IDLE     | R   |                              idle                                            |
| 0x1E0 | OBS_HIST_SEL    | RW  | [0] bus (0=rd, 1=wr) · [1] metric (0=AR→firstR or AW→B, 1=AR→RLAST) · [5:2] bin |
| 0x1E4 | OBS_HIST_COUNT  | R   | Selected bin count (muxed rd/wr on bit 0)                                    |
| 0x1E8 | OBS_HIST_TOTAL  | R   | Total txns on the selected metric (muxed rd/wr on bit 0)                     |

Bin `b` covers `[2^b, 2^(b+1))` cycles (16 bins → 0..15 cycles for b=0
up to 32K..64K cycles for b=15).

---

## UART bridge wire protocol

Source: `projects/components/converters/rtl/uart_to_axil4/uart_axil_bridge.sv`.
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
The Python `UARTAxiBridge` class (`projects/components/converters/bin/
uart_axi_bridge.py`) handles the framing.
