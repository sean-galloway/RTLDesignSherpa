<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

**[← Back to README](../README.md)** | **[← jet_fpga_system_index](jet_fpga_system_index.md)**

# Jet Pair-Rig Genesys2 — Address Map

The host sees a single 32-bit AXI4-Lite address space decoded by the
auto-generated `bridge_jet_axil` crossbar (1 master × 6 slaves). All
apertures are 4 KB and are as-built in the harness RTL.

### Figure 2.1: Host AXI4-Lite Address Map

![Amber address map](assets/graphviz/jet_address_map.png)

The address map above is derived from `bridge_jet_axil.toml` and the host
base constants in `host/jet_board.py`.

## Window summary

| Base | Range | Slave | Protocol | Data | Purpose |
| --- | --- | --- | --- | --- | --- |
| `0x0001_0000` | 4 KB | `harness_csr` | AXIL | 32 | Global control/status + free-running cycle counter |
| `0x0002_0000` | 4 KB | `cycle_injector0` | AXIL | 32 | Core 0 stimulus engine config/status |
| `0x0003_0000` | 4 KB | `cycle_injector1` | AXIL | 32 | Core 1 stimulus engine config/status |
| `0x0004_0000` | 4 KB | `tally_cnt` | AXIL | 64 | MonBus tally bin-count readback (host reads low 32 bits) |
| `0x0005_0000` | 4 KB | `tally_cfgw` | AXIL | 64 | MonBus tally CAM legal-set load / config write |
| `0x0006_0000` | 4 KB | `tally_cfgr` | AXIL | 64 | MonBus tally config/status readback |

: Table 2.1: Host-visible AXI4-Lite address windows

Any address outside the six windows above returns a DECERR response from the
bridge.

## `harness_csr` registers (`0x0001_0000`)

| Offset | Name | Access | Description |
| --- | --- | --- | --- |
| `0x000` | CTRL | RW | `[0]` TALLY_CLEAR — write-1-pulse: one-cycle `tally_clear` strobe to `monbus_tally_axil` (zeros all bins, re-arms the first-event latch bank); self-clears, always reads 0. `[1]` TALLY_FREEZE — level: hold bin counting for a coherent snapshot. `[31:2]` scratch. Host protocol: **settle** (let the MonBus path drain — a clear landing on a partial in-flight record phase-shifts the record stream into UNEXPECTED), freeze, read bins, clear (RMW preserves freeze), unfreeze. |
| `0x004` | STATUS | R | `{26'b0, ci1_err, ci0_err, ci1_busy, ci0_busy, ci1_done, ci0_done}` |
| `0x008` | CYCLE_LO | R | Free-running cycle counter [31:0] |
| `0x00C` | CYCLE_HI | R | Free-running cycle counter [63:32] |
| `0x010` | FABRIC_DBG | R | `jet_pair_fabric` debug state [3:0] |

: Table 2.2: harness_csr register map

## `cycle_injector` registers (`0x0002_0000` and `0x0003_0000`)

| Offset | Name | Access | Description |
| --- | --- | --- | --- |
| `0x000` | CTRL | RW | `{we_mix[15:8], 7'b0, run}` |
| `0x004` | SEED | RW | Fibonacci LFSR seed (0 substitutes `0xDEAD_BEEF`) |
| `0x008` | ADDR_BASE | RW | Base address for generated transactions |
| `0x00C` | ADDR_MASK | RW | Wrap mask applied to LFSR index (`addr = base + (lfsr & mask)`) |
| `0x010` | TRANS_COUNT | RW | Number of transactions to issue |
| `0x014` | STATUS | R | `{30'b0, busy, done}` |
| `0x018` | ACC_COUNT | R | Accepted CPU-request count |
| `0x01C` | RSP_COUNT | R | Returned CPU-response count |
| `0x020` | ERR_FLAG | R | `{31'b0, err_flag}` (set on response timeout) |
| `0x024` | LAT_MIN | R | Min per-request latency, cycles (accept → response; 0 before any response) |
| `0x028` | LAT_MAX | R | Max per-request latency, cycles |
| `0x02C` | RUN_CYCLES | R | Busy-cycle count for the run |
| `0x030` | RSP_CRC_LO | R | CRC-32 over returned read data [31:0] |
| `0x034` | RSP_CRC_HI | R | CRC-32 over returned read data [63:32] |
| `0x038` | WDATA_CRC_LO | R | CRC-32 over issued write data [31:0] |
| `0x03C` | WDATA_CRC_HI | R | CRC-32 over issued write data [63:32] |
| `0x040` | LAT_SUM_LO | R | Latency sum [31:0] (mean = sum / TRANS_COUNT) |
| `0x044` | LAT_SUM_HI | R | Latency sum [63:32] |
| `0x048` - `0x064` | LAT_HIST0..7 | R | Log2 latency histogram: bucket *b* covers [2^b, 2^(b+1)−1], bucket 7 catches ≥128; buckets sum to TRANS_COUNT |

All LAT_*/RUN_CYCLES registers are read-only and cleared on run start.

: Table 2.3: cycle_injector register map

## `tally_cnt` registers (`0x0004_0000`)

`monbus_tally_axil` stores 33 entries as 64-bit counters. The bridge exposes
`count` as a 64-bit-data slave, but the 32-bit host read path returns the
lower 32 bits of each entry.

| Offset | Name | Description |
| --- | --- | --- |
| `0x000` - `0x0F8` | COUNT0..COUNT31 | 32 legal-set profile bins (8 bytes each) |
| `0x100` | UNEXPECTED | Catch-all bin for packets not in the legal set |

: Table 2.4: tally_cnt read-back layout

## `tally_cfgw` / `tally_cfgr` registers (`0x0005_0000` / `0x0006_0000`)

These apertures expose the generated `tally_regs` register block from
`monbus_tally_axil`.

| Offset | Name | Description |
| --- | --- | --- |
| `0x100` | CAM_CLEAR | Write `CLEAR=1` to clear the legal-set CAM |
| `0x108` | CAM_KEY | 32-bit key value for CAM load |
| `0x110` | CAM_LOAD | `{VALID[31], INDEX[7:0]}` load a key→index mapping (32-bit write only) |
| `0x118` | WATCH_CTRL | `{ARM, MASK[15:0]}` watch/control |
| `0x120` | LATCH_SEL | `{SEL[7:0]}` latch select |

: Table 2.5: tally_cfgw/cfgr register map

The `tally_cfgr` aperture also serves the first-event latch readback (16
slots, re-armed by every CTRL[0] tally clear). These are named registers in
the generated `tally_regs` regmap; select the slot with LATCH_SEL first:

| Offset | Name | Description |
| --- | --- | --- |
| `0x010` | LATCH_STATUS | `{VALID[16], FILL[15:0]}` — slots captured so far |
| `0x018` | LATCH_PKT0 | Selected slot packet[31:0] |
| `0x020` | LATCH_PKT1 | Selected slot packet[63:32] |
| `0x028` | LATCH_PKT2 | Selected slot packet[95:64] |
| `0x030` | LATCH_PKT3 | Selected slot packet[127:96] |
| `0x038` | LATCH_TS_LO | Selected slot timestamp[31:0] |
| `0x040` | LATCH_TS_HI | Selected slot timestamp[63:32] |

: Table 2.6: tally_cfgr first-event latch readback

---

**Last Updated:** 2026-11-01
**Maintained By:** RTL Design Sherpa Project
