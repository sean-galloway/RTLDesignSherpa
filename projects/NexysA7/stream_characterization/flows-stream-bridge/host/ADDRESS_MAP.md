# stream_char_harness — host address map

All addresses are 32-bit absolute AXIL addresses as seen from the host
(UART → uart_axil_bridge → bridge_stream_char_axil → slave port).

## Top-level bridge slaves

| Base address | Range | Slave         | Width | Protocol | Purpose                                      |
| ------------ | ----- | ------------- | ----- | -------- | -------------------------------------------- |
| `0x0000_0000` | 4 KB  | `stream_apb`  | 32b   | APB      | STREAM configuration register block          |
| `0x0001_0000` | 4 KB  | `harness_csr` | 32b   | AXIL     | Harness control / status / obs counters     |
| `0x0002_0000` | 64 KB | `desc_ram`    | 256b  | AXIL     | Descriptor SRAM (32 B/descriptor)            |
| `0x0003_0000` | 4 KB  | `stream_err`  | 32b   | AXIL     | STREAM error / scheduler-status FIFO         |
| `0x0004_0000` | 256 KB| `debug_sram`  | 64b   | AXIL     | MonBus trace SRAM                            |
| `0x0008_0000` | 4 KB  | `dma_axil`    | 32b   | AXIL     | DMA / MCDMA s_axi_lite window (future use)   |

> **Note on the 256b desc_ram slave.** The host (32b AXIL) writes single
> beats into the 256b slave port. The bridge generator emits the
> `axil_to_axi4_wide_align_wr` aligner (since this commit) so each
> 32b host write lands at the correct byte lane of the 32B SRAM row,
> as derived from `awaddr & 0x1F`. STREAM's `m_axi_desc` (256b) reads
> the descriptors back as one beat per descriptor.

## `harness_csr` register map (base = 0x0001_0000)

Decoded from the address-map block at the top of
`stream_char_framework/rtl/harness_csr.sv`.

| Offset | Name                  | RW | Bits / meaning                                                          |
| ------ | --------------------- | -- | ----------------------------------------------------------------------- |
| `0x00` | `CTRL`                | W  | `[0]` start_pulse, `[1]` clear_stats_pulse, `[2]` freeze_trace, `[3]` soft_reset_pulse |
| `0x04` | `STATUS`              | R  | `[0]` stream_irq, `[1]` any_error, `[2]` trace_overflow (sticky "wrapped ≥ 1×") |
| `0x08` | `DBG_WR_PTR`          | R  | Trace SRAM write pointer (in words). **Wraps to 0 at `DEBUG_SRAM_WORDS`** to match the monbus group's circular dump address — readers must treat the value modulo SRAM size, not as a monotonic word count. |
| `0x0C` | `DBG_OVERFLOW`        | R  | Sticky "the trace has wrapped at least once" flag. **Does NOT stop writes** — writes continue, overwriting oldest records. Cleared by `clear_stats_pulse`. See `monbus_group.md` "Address-window behavior" for the matching monbus-side invariant. |
| `0x10` | `CRC_RD_EXPECTED`     | R  | aggregate read CRC (back-compat = ch0)                                 |
| `0x14` | `CRC_WR_EXPECTED`     | R  | aggregate expected write CRC                                           |
| `0x18` | `CRC_WR_COMPUTED`     | R  | aggregate computed write CRC                                           |
| `0x1C` | `CRC_MATCH`           | R  | `[0]` match, `[1]` valid                                              |
| `0x20` | `SCRATCH`             | RW | scratchpad                                                             |
| `0x24` | `BUILD_ID`            | R  | "STRC" (`0x5354_5243`) build tag                                       |
| `0x28` | `TIMER_CTRL`          | W  | `[0]` clear pulse                                                      |
| `0x2C` | `TIMER_STATUS`        | R  | `[0]` done, `[1]` running, `[2]` pass                                  |
| `0x30..0x34` | `TIMER_CYCLES`  | R  | 64b free-running cycle count                                           |
| `0x38` | `TIMER_EXPECTED_BEATS`| RW | sink-side beat count gating `done`                                     |
| `0x3C` | `RESP_DELAY`          | RW | `[15:0]` rd_resp_delay, `[31:16]` wr_resp_delay (aclk cycles)         |
| `0x40..0x5C` | `TIMER_R/W_*`   | R  | r_first, r_last, w_first, w_last 64b stamps                            |
| `0x60..0x7C` | `CRC_RD_PER_CH[0..7]`  | R | per-channel read CRC                                            |
| `0x80..0x9C` | `CRC_WR_PER_CH[0..7]`  | R | per-channel write CRC                                           |
| `0xA0` | `CRC_VALID_MASK`      | R  | per-channel valid bits (`[N-1:0]`)                                     |
| `0xA4` | `CRC_MATCH_MASK`      | R  | per-channel match bits                                                 |
| `0xB0..0xBC` | `CH_KICK_ADDR[0..3]` | RW | per-channel descriptor kick-off address (shadow), ch 0..3        |
| `0xC0` | `KICK_GO`             | W  | bitmask: pulse hardware kick line for each set bit                     |
| `0xC4..0xD0` | `CH_KICK_ADDR[4..7]` | RW | per-channel kick address shadow, ch 4..7                         |
| `0xD4` | `DESC_SRAM_AR_HS`     | R  | desc_ram AXIL AR handshakes at the SRAM port                           |
| `0xD8` | `DESC_SRAM_R_HS`      | R  | desc_ram AXIL R handshakes at the SRAM port                            |
| `0xE0` | `DESC_AR_HS`          | R  | STREAM 256b m_axi_desc AR handshakes                                   |
| `0xE4` | `DESC_AR_STALL`       | R  | STREAM 256b m_axi_desc AR stalled cycles                               |
| `0xE8` | `DESC_R_HS`           | R  | STREAM 256b m_axi_desc R handshakes                                    |
| `0xEC` | `DESC_R_STALL`        | R  | STREAM 256b m_axi_desc R stalled cycles                                |
| `0xF0` | `DESC_AW_HS`          | R  | desc_ram AXIL AW handshakes (host -> SRAM)                             |
| `0xF4` | `DESC_W_HS`           | R  | desc_ram AXIL W handshakes                                             |
| `0xF8` | `DESC_B_HS`           | R  | desc_ram AXIL B handshakes                                             |
| `0xFC` | `DESC_VR_LIVE`        | R  | live 16b valid/ready snapshot (see harness comment for bit layout)     |
| `0x100..0x17C` | `RD_METER_*`  | R  | AXI read bus meter (agg + per-channel; see harness_csr.sv layout)      |
| `0x180..0x1FC` | `WR_METER_*`  | R  | AXI write bus meter (agg + per-channel)                                |

### Kick-burst fast-path layout
The `KICK_GO` register sits at `0xC0`, between `CH_KICK_ADDR[3]` (0xBC)
and `CH_KICK_ADDR[4]` (0xC4). The split exists so a naive
`BASE + 4*ch` stride would not land ch=4 on the KICK_GO slot; use
`kick_addr_csr(ch)` (in `run_characterization.py` / `stream_char_tb.py`)
to compute the right shadow address.

## `stream_apb` register map (base = 0x0000_0000)

Decoded from STREAM's PeakRDL-generated `stream_regmap.py` (see
`projects/components/stream/regs/`). Offsets shown are the ones the
host actually pokes during a characterization run.

| Offset | Name                  | RW | Notes                                                              |
| ------ | --------------------- | -- | ------------------------------------------------------------------ |
| `0x000..0x03F` | per-ch kick (apbtodescr) | W  | 8-byte stride per channel (LOW@+0, HIGH@+4)                |
| `0x100` | `GLOBAL_CTRL`         | RW | `[0]` GLOBAL_EN                                                    |
| `0x104` | `GLOBAL_STATUS`       | R  | `[0]` GLOBAL_BUSY                                                  |
| `0x120` | `CHANNEL_ENABLE`      | RW | per-channel enable bitmask                                         |
| `0x124` | `CHANNEL_RESET`       | W  | per-channel reset pulse                                            |
| `0x140` | `CHANNEL_IDLE`        | R  | per-channel idle bitmask                                           |
| `0x144` | `DESC_ENGINE_IDLE`    | R  | per-channel desc-engine idle bitmask                               |
| `0x148` | `SCHEDULER_IDLE`      | R  | per-channel scheduler idle bitmask                                 |
| `0x170` | `SCHED_ERROR`         | R  | per-channel scheduler error bitmask                                |
| `0x174` | `AXI_RD_COMPLETE`     | R  | per-channel "all reads complete" bitmask                           |
| `0x178` | `AXI_WR_COMPLETE`     | R  | per-channel "all writes complete" bitmask                          |
| `0x200` | `SCHED_TIMEOUT_CYC`   | RW | scheduler activity-timeout window (cycles)                         |
| `0x204` | `SCHED_CONFIG`        | RW | `[0]` SCHED_EN, `[1]` TIMEOUT_EN, `[2]` ERR_EN, `[3]` COMPL_EN     |
| `0x220` | `DESCENG_CONFIG`      | RW | `[0]` DESCENG_EN                                                   |
| `0x224..0x230` | `DESCENG_ADDR0/1_BASE/LIMIT` | RW | descriptor address-range gates                          |
| `0x240` | `DAXMON_ENABLE`       | RW | descriptor-fetch AXI monitor enable bits                           |
| `0x24C` | `DAXMON_PKT_MASK`     | RW | per-packet-type drop mask at monbus entry                          |
| `0x250` | `DAXMON_ERR_CFG`      | RW | `[3:0]` ERR_SELECT (route to err FIFO), `[15:8]` ERR_MASK         |
| `0x260..0x270` | `RDMON_*`     | RW | data-read monitor (same layout as DAXMON_*)                        |
| `0x280..0x290` | `WRMON_*`     | RW | data-write monitor (same layout as DAXMON_*)                       |
| `0x2A0` | `AXI_XFER_CONFIG`     | RW | `[7:0]` rd_beats per burst, `[15:8]` wr_beats per burst (ARLEN/AWLEN) |

## `desc_ram` descriptor layout (base = 0x0002_0000)

Each descriptor is 32 bytes / 256 bits. The harness host writes
descriptors 32b-at-a-time; the bridge's AXIL aligner places each 32b
word at the byte lane derived from `awaddr & 0x1F`.

| Word | Host-side offset (within desc) | Width | Field                                                  |
| ---- | ------------------------------ | ----- | ------------------------------------------------------ |
| 0    | +0x00                          | 32b   | `src_addr[31:0]`                                       |
| 1    | +0x04                          | 32b   | `src_addr[63:32]`                                      |
| 2    | +0x08                          | 32b   | `dst_addr[31:0]`                                       |
| 3    | +0x0C                          | 32b   | `dst_addr[63:32]`                                      |
| 4    | +0x10                          | 32b   | `length`  (in BEATS, not bytes)                        |
| 5    | +0x14                          | 32b   | `next_descriptor_ptr` (absolute address, 0 = chain end)|
| 6    | +0x18                          | 32b   | `ctrl` word — see below                                |
| 7    | +0x1C                          | 32b   | reserved (read as last write; STREAM ignores)          |

### `ctrl` word bit-fields

```
 31                                                                  0
 +------------------+------------------+------------+----+----+----+--+
 |   stamp / top16  |     priority     | channel_id |LST |IRQ |ERR | V|
 |     [31:16]      |     [15:8]       |   [7:4]    |[2] |[1] |[3] |[0]|
 +------------------+------------------+------------+----+----+----+--+
```

| Bit(s)    | Field         | Notes                                                  |
| --------- | ------------- | ------------------------------------------------------ |
| `[0]`     | `valid`       | Descriptor is valid — STREAM ignores the row otherwise |
| `[1]`     | `interrupt`   | Generate IRQ when this descriptor completes            |
| `[2]`     | `last`        | Last in chain — STREAM terminates after this           |
| `[3]`     | `error`       | Error flag (descriptor pre-marked invalid)             |
| `[7:4]`   | `channel_id`  | Target channel for this descriptor                     |
| `[15:8]`  | `priority`    | Optional priority (unused by stream_char today)        |
| `[31:16]` | `stamp / top16` | Free-form (descriptor_builder leaves as 0)           |

## Where to look next

- `dump_descriptors.py` — readable per-descriptor dump for any chain
  (built locally from `descriptor_builder`, no FPGA needed).
- `desc_ram_check.py` — unified descriptor-RAM readback / compare tool.
  Use it three ways:
  - **Read-only** (`desc_ram_check.py`) — read current SRAM contents
    and diff against the golden chain for the chosen config. Run this
    after a manual `run_characterization` or after a previous
    `--kick` session has hung.
  - **Write + read** (`desc_ram_check.py --write`) — reprograms the
    FPGA, soft-resets the unit, writes the chain, reads back, diffs.
    Round-trip sanity check.
  - **Write + kick + wait + read** (`desc_ram_check.py --write --kick`)
    — full preload + STREAM config + kick burst + wait for
    `timer.done` / `any_error` / timeout + readback + diff. Use this
    to detect whether STREAM (or another master) writes into desc_ram
    during a run.
- `harness_csr.sv` (in stream_char_framework/rtl/) — authoritative
  offsets for the harness CSR; STREAM APB offsets come from
  PeakRDL-generated `stream_regmap.py`.
