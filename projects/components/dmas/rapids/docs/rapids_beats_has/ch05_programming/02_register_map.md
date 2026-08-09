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

# Register Map

## Overview

RAPIDS Beats provides a memory-mapped register interface for configuration and
status. All registers are accessed through the single top-level APB slave
(`s_apb_*`) and are implemented by the PeakRDL-generated `rapids_regs` register
block. A single addrmap (one APB slave) contains a base regfile at 0x100-0x3FF
and a nested monitor regfile (`rapids_mon_regs`) at 0x1000. Descriptor kick-off
uses a separate address range (0x000-0x03F) routed to `apb4todescr`.

Because the monitor regfile lives at 0x1000, the APB address bus must be at
least 13 bits wide.

## Address Space Layout

| Range | Target | Purpose |
|-------|--------|---------|
| 0x000-0x03F | `apb4todescr` | Per-channel descriptor kick-off |
| 0x100-0x3FF | `rapids_regs` base regfile | Configuration and status |
| 0x1000+ | `rapids_regs` monitor regfile | AXI-monitor config and performance |

: Address Space Layout

## Base Registers (0x100-0x3FF)

| Offset | Name | Access | Description |
|--------|------|--------|-------------|
| 0x100 | `GLOBAL_CTRL` | RW | `GLOBAL_EN[0]`, `GLOBAL_RST[1]` (self-clearing) |
| 0x104 | `GLOBAL_STATUS` | RO | `SYSTEM_IDLE[0]` |
| 0x108 | `VERSION` | RO | `MINOR[7:0]`, `MAJOR[15:8]`, `NUM_CHANNELS[23:16]=8` |
| 0x120 | `CHANNEL_ENABLE` | RW | `CH_EN[7:0]` per-channel enable |
| 0x124 | `CHANNEL_RESET` | RW | `CH_RST[7:0]` per-channel reset (self-clearing) |
| 0x140 | `CHANNEL_IDLE` | RO | `CH_IDLE[7:0]` |
| 0x144 | `DESC_ENGINE_IDLE` | RO | Per-channel descriptor-engine idle |
| 0x148 | `SCHEDULER_IDLE` | RO | Per-channel scheduler idle (excludes CH_ERROR) |
| 0x150-0x16C | `CH_STATE[0..7]` | RO | Per-channel FSM state (stride 0x4) |
| 0x170 | `SCHED_ERROR` | RO | Per-channel sticky scheduler error |
| 0x174 | `AXI_RD_COMPLETE` | RO | Per-channel read-complete |
| 0x178 | `AXI_WR_COMPLETE` | RO | Per-channel write-complete |
| 0x200 | `SCHED_TIMEOUT_CYCLES` | RW | Write-progress timeout window (cycles, reset 1000) |
| 0x204 | `SCHED_CONFIG` | RW | `SCHED_EN`, `TIMEOUT_EN`, `ERR_EN`, `COMPL_EN`, `PERF_EN` |
| 0x208 | `SCHED_TIMEOUT_LIMIT` | RW | `LIMIT[7:0]` escalation limit (reset 4, 0 = never) |
| 0x220 | `DESCENG_CONFIG` | RW | `DESCENG_EN[0]`, `PREFETCH_EN[1]`, `FIFO_THRESH[5:2]` (reset 8) |
| 0x224 | `DESCENG_ADDR0_BASE` | RW | Descriptor address range 0 base [31:0] |
| 0x228 | `DESCENG_ADDR0_LIMIT` | RW | Descriptor address range 0 limit [31:0] |
| 0x22C | `DESCENG_ADDR1_BASE` | RW | Descriptor address range 1 base [31:0] |
| 0x230 | `DESCENG_ADDR1_LIMIT` | RW | Descriptor address range 1 limit [31:0] |
| 0x240 | `CTRL_CONFIG` | RW | `CTRLRD_MAX_TRY[8:0]` control-read poll retry budget (0-511, reset 16) |
| 0x2A0 | `AXI_XFER_CONFIG` | RW | AXI transfer sizing configuration |
| 0x2B0 | `PERF_CONFIG` | RW | Performance profiler configuration |
| 0x2C0-0x2CC | `OBS_CTRL`/`OBS_FLAGS`/`OBS_DATA0`/`OBS_DATA1` | RW/RO | Observation mux |
| 0x35C | `PERF_CH_SEL` | RW | Performance channel select |
| 0x378-0x380 | `HIST_SEL`/`HIST_DATA`/`HIST_TOTAL` | RW/RO | Latency histogram |

: Base Registers

## Monitor Registers (0x1000)

| Offset | Name | Access | Description |
|--------|------|--------|-------------|
| 0x1000 | `MON_FIFO_STATUS` | RO | MonBus capture/error FIFO status |
| 0x1004 | `MON_FIFO_COUNT` | RO | MonBus FIFO occupancy |
| 0x10C0-0x10DC | `DAXMON_*` | RW | Descriptor-monitor config (enable/timeout/latency/masks) |
| 0x10E0-0x10FC | `RDMON_*` | RW | Read-monitor config (same layout) |
| 0x1100-0x111C | `WRMON_*` | RW | Write-monitor config (same layout, incl. `COMPRESS_EN`) |
| 0x1150-0x1178 | `DAXMON_PERF_*` | RO/RW | Descriptor-monitor performance counters |
| 0x1180-0x11A8 | `RDMON_PERF_*` | RO/RW | Read-monitor performance counters |
| 0x11B0-0x11D8 | `WRMON_PERF_*` | RO/RW | Write-monitor performance counters |
| 0x11E0-0x11F4 | `{RD,WR}MON_PERF_CH_*` | RO | Per-channel producer/backpressure/starve/idle/overflow |

: Monitor Registers (base 0x1000)

## Key Register Fields

### GLOBAL_CTRL (0x100) - Read/Write

| Bits | Field | Reset | Description |
|------|-------|-------|-------------|
| [0] | `GLOBAL_EN` | 0 | Master enable for the entire engine |
| [1] | `GLOBAL_RST` | 0 | Global reset (self-clearing) |
| [31:2] | Reserved | 0 | Reserved |

: GLOBAL_CTRL Register

### SCHED_TIMEOUT_LIMIT (0x208) - Read/Write

| Bits | Field | Reset | Description |
|------|-------|-------|-------------|
| [7:0] | `LIMIT` | 4 | Consecutive write-progress timeout windows before escalating to a fatal, sticky CH_ERROR. 0 = never escalate. Total escalation time ~= LIMIT x SCHED_TIMEOUT_CYCLES. |

: SCHED_TIMEOUT_LIMIT Register

### DESCENG_CONFIG (0x220) - Read/Write

| Bits | Field | Reset | Description |
|------|-------|-------|-------------|
| [0] | `DESCENG_EN` | 1 | Descriptor engine master enable |
| [1] | `PREFETCH_EN` | 0 | Prefetch chaining (0 = on-demand, ~1 ahead) |
| [5:2] | `FIFO_THRESH` | 8 | Descriptors buffered ahead when prefetch enabled |
| [31:6] | Reserved | 0 | Reserved |

: DESCENG_CONFIG Register

## Register Access Timing

![Register Read](../assets/wavedrom/register_read.svg)

**Source:** [register_read.json](../assets/wavedrom/register_read.json)

```wavedrom
{
  "signal": [
    {"name": "pclk", "wave": "p........"},
    {},
    {"name": "psel", "wave": "01....0.."},
    {"name": "penable", "wave": "0.1...0.."},
    {"name": "pwrite", "wave": "0........"},
    {"name": "paddr", "wave": "x=....x..", "data": ["0x104"]},
    {},
    {"name": "pready", "wave": "0..1..0.."},
    {"name": "prdata", "wave": "x..=..x..", "data": ["STATUS"]},
    {"name": "pslverr", "wave": "0........"}
  ],
  "config": {"hscale": 1.5},
  "head": {"text": "APB Register Read (CH0 Status)"}
}
```

![Register Write](../assets/wavedrom/register_write.svg)

**Source:** [register_write.json](../assets/wavedrom/register_write.json)

```wavedrom
{
  "signal": [
    {"name": "pclk", "wave": "p........"},
    {},
    {"name": "psel", "wave": "01....0.."},
    {"name": "penable", "wave": "0.1...0.."},
    {"name": "pwrite", "wave": "01....0.."},
    {"name": "paddr", "wave": "x=....x..", "data": ["0x100"]},
    {"name": "pwdata", "wave": "x=....x..", "data": ["0x8000_0000"]},
    {},
    {"name": "pready", "wave": "0..1..0.."},
    {"name": "pslverr", "wave": "0........"},
    {},
    {"name": "ch0_enable", "wave": "0....1..."}
  ],
  "config": {"hscale": 1.5},
  "head": {"text": "APB Register Write (CH0 Enable)"}
}
```

## Channel Kick Sequence

Writing to the `kick` bit triggers descriptor processing:

```wavedrom
{
  "signal": [
    {"name": "pclk", "wave": "p............"},
    {},
    ["APB Write",
      {"name": "psel", "wave": "01...0......."},
      {"name": "penable", "wave": "0.1..0......."},
      {"name": "paddr", "wave": "x=...x.......", "data": ["0x000"]},
      {"name": "pwdata", "wave": "x=...x.......", "data": ["KICK"]}
    ],
    {},
    ["Channel Response",
      {"name": "kick_valid", "wave": "0...1.0......"},
      {"name": "ch_state", "wave": "=....=.......", "data": ["IDLE","WAIT_DESC"]},
      {"name": "desc_fetch", "wave": "0....1.0....."}
    ]
  ],
  "config": {"hscale": 1.5},
  "head": {"text": "Channel Kick Sequence"}
}
```

## Address Decoding

Registers are global (not per-channel windows); per-channel fields are packed
as bit lanes within a single 32-bit register (e.g. `CHANNEL_ENABLE.CH_EN[7:0]`,
`CHANNEL_IDLE.CH_IDLE[7:0]`). The only per-channel array is `CH_STATE[0..7]` at
0x150-0x16C (stride 0x4). Descriptor kick-off is a separate address range
(0x000-0x03F) handled by `apb4todescr`, not part of the register regfile.

```
0x000 - 0x03F: Descriptor kick-off (apb4todescr)
0x100 - 0x3FF: Base configuration / status registers
0x1000+      : Monitor configuration / performance registers
```

