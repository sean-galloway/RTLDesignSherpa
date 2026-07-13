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

# RAPIDS Registers Specification

**Module:** `rapids_regs.sv` (generated)
**Source:** `projects/components/rapids/rtl/macro_beats/rapids_regs.rdl`, `rapids_mon_regs.rdl`
**Generated:** `projects/components/rapids/regs/generated/rtl/rapids_regs.sv`
**Status:** Implemented (PeakRDL-generated)

---

## Overview

`rapids_regs` is the PeakRDL-generated register block for the RAPIDS Beats
top-level. It exposes configuration and status through a single command/response
CPU interface and drives the hardware via a `hwif_out` structure that
`rapids_config_block` maps onto the core/monitor `cfg_*` signals.

A single addrmap (one APB slave) contains two regfiles:

- **Base config/status** registers at `0x100`-`0x3FF`.
- A nested **`rapids_mon_regs`** monitor regfile at base `0x1000`, decoded under
  `hwif_out.MON.*` (all DAXMON / RDMON / WRMON / MON_FIFO and per-monitor
  performance registers).

Because the monitor regfile lives at `0x1000`, the register-block address decode
requires at least **13 bits** (`cpuif_addr` is a 13-bit compare in the generated
RTL). The APB address bus feeding the block (`APB_ADDR_WIDTH`) must therefore be
>= 13 to reach the monitor regfile.

---

## Base Register Map (0x100-0x3FF)

| Offset | Name | Access | Description |
|--------|------|--------|-------------|
| 0x100 | `GLOBAL_CTRL` | RW | `GLOBAL_EN[0]`, `GLOBAL_RST[1]` (self-clearing) |
| 0x104 | `GLOBAL_STATUS` | RO | `SYSTEM_IDLE[0]` (all channels idle) |
| 0x108 | `VERSION` | RO | `MINOR[7:0]=0x5A`, `MAJOR[15:8]`, `NUM_CHANNELS[23:16]=0x08` |
| 0x120 | `CHANNEL_ENABLE` | RW | `CH_EN[7:0]` per-channel enable |
| 0x124 | `CHANNEL_RESET` | RW | `CH_RST[7:0]` per-channel reset (self-clearing) |
| 0x140 | `CHANNEL_IDLE` | RO | `CH_IDLE[7:0]` per-channel idle |
| 0x144 | `DESC_ENGINE_IDLE` | RO | Per-channel descriptor-engine idle |
| 0x148 | `SCHEDULER_IDLE` | RO | Per-channel scheduler idle (excludes CH_ERROR) |
| 0x150-0x16C | `CH_STATE[0..7].STATE` | RO | Per-channel FSM state (stride 0x4) |
| 0x170 | `SCHED_ERROR` | RO | Per-channel sticky scheduler error |
| 0x174 | `AXI_RD_COMPLETE` | RO | Per-channel read-complete flags |
| 0x178 | `AXI_WR_COMPLETE` | RO | Per-channel write-complete flags |
| 0x200 | `SCHED_TIMEOUT_CYCLES` | RW | `TIMEOUT_CYCLES[31:0]` write-progress window (reset 1000) |
| 0x204 | `SCHED_CONFIG` | RW | `SCHED_EN`, `TIMEOUT_EN`, `ERR_EN`, `COMPL_EN`, `PERF_EN` |
| 0x208 | `SCHED_TIMEOUT_LIMIT` | RW | `LIMIT[7:0]` consecutive-timeout escalation limit (reset 4, 0 = never) |
| 0x220 | `DESCENG_CONFIG` | RW | `DESCENG_EN[0]`, `PREFETCH_EN[1]`, `FIFO_THRESH[5:2]` (reset 8) |
| 0x224 | `DESCENG_ADDR0_BASE` | RW | Descriptor address range 0 base [31:0] |
| 0x228 | `DESCENG_ADDR0_LIMIT` | RW | Descriptor address range 0 limit [31:0] |
| 0x22C | `DESCENG_ADDR1_BASE` | RW | Descriptor address range 1 base [31:0] |
| 0x230 | `DESCENG_ADDR1_LIMIT` | RW | Descriptor address range 1 limit [31:0] |
| 0x240 | `CTRL_CONFIG` | RW | `CTRLRD_MAX_TRY[8:0]` control-read poll retry budget (0-511, reset 16) |
| 0x2A0 | `AXI_XFER_CONFIG` | RW | AXI transfer sizing configuration |
| 0x2B0 | `PERF_CONFIG` | RW | Performance profiler configuration |
| 0x2C0 | `OBS_CTRL` | RW | Observation mux control (channel/category select) |
| 0x2C4 | `OBS_FLAGS` | RO | Observation flags |
| 0x2C8 | `OBS_DATA0` | RO | Observation data word 0 |
| 0x2CC | `OBS_DATA1` | RO | Observation data word 1 |
| 0x35C | `PERF_CH_SEL` | RW | Performance channel select |
| 0x378 | `HIST_SEL` | RW | Histogram bucket select |
| 0x37C | `HIST_DATA` | RO | Histogram bucket data |
| 0x380 | `HIST_TOTAL` | RO | Histogram total count |

: Table 3.12.1: Base Register Map

### Key Register Fields

**SCHED_TIMEOUT_LIMIT (0x208)** -- `LIMIT[7:0]` sets the number of consecutive
write-progress timeout windows a channel tolerates before the recoverable
timeout escalates to a fatal, sticky `CH_ERROR`. `0` = never escalate (pure soft
timeout). Total time to escalate is approximately `LIMIT x TIMEOUT_CYCLES`.
Reset value is 4.

**DESCENG_CONFIG (0x220)** -- `PREFETCH_EN[1]` and `FIFO_THRESH[5:2]` control the
now-functional descriptor prefetch: prefetch off = on-demand chaining (~1 ahead),
prefetch on = buffer up to `FIFO_THRESH` descriptors ahead.

**CTRL_CONFIG (0x240)** -- `CTRLRD_MAX_TRY[8:0]` bounds the control-read poll
retry budget (0-511, reset 16) fed to every channel's `ctrlrd_engine`. A
`CTRL_READ` descriptor polls its gate address once per retry; if the masked value
never matches within `CTRLRD_MAX_TRY` attempts the engine raises `ctrlrd_error`
so a never-satisfied gate cannot hang the channel. See the Control-Read /
Control-Write Engine specs (Sections 2.8 / 2.9) and the Scheduler control
interface (Section 2.1).

---

## Monitor Register Map (rapids_mon_regs @ 0x1000)

The monitor regfile is instantiated at base `0x1000` under `hwif_out.MON.*`. It
holds the MonBus FIFO status, the three AXI-monitor configuration groups
(DAXMON = descriptor monitor, RDMON = read monitor, WRMON = write monitor), and
per-monitor performance counters.

| Offset | Name | Access | Description |
|--------|------|--------|-------------|
| 0x1000 | `MON.MON_FIFO_STATUS` | RO | MonBus capture/error FIFO status |
| 0x1004 | `MON.MON_FIFO_COUNT` | RO | MonBus FIFO occupancy |
| 0x10C0 | `MON.DAXMON_ENABLE` | RW | Descriptor-monitor enables (incl. `COMPRESS_EN`) |
| 0x10C4 | `MON.DAXMON_TIMEOUT` | RW | Descriptor-monitor timeout cycles |
| 0x10C8 | `MON.DAXMON_LATENCY_THRESH` | RW | Descriptor-monitor latency threshold |
| 0x10CC | `MON.DAXMON_PKT_MASK` | RW | Descriptor-monitor packet mask |
| 0x10D0 | `MON.DAXMON_ERR_CFG` | RW | Descriptor-monitor error select/mask |
| 0x10D4-0x10DC | `MON.DAXMON_MASK1/2/3` | RW | Descriptor-monitor category masks |
| 0x10E0-0x10FC | `MON.RDMON_*` | RW | Read-monitor config (same layout as DAXMON) |
| 0x1100-0x111C | `MON.WRMON_*` | RW | Write-monitor config (same layout as DAXMON) |
| 0x1150-0x1178 | `MON.DAXMON_PERF_*` | RO/RW | Descriptor-monitor performance counters |
| 0x1180-0x11A8 | `MON.RDMON_PERF_*` | RO/RW | Read-monitor performance counters |
| 0x11B0-0x11D8 | `MON.WRMON_PERF_*` | RO/RW | Write-monitor performance counters |
| 0x11E0-0x11EC | `MON.{RD,WR}MON_PERF_CH_*` | RO | Per-channel producer/backpressure/starve/idle |
| 0x11F0 | `MON.RDMON_PERF_CH_OVERFLOW` | RO | Read-monitor per-channel overflow |
| 0x11F4 | `MON.WRMON_PERF_CH_OVERFLOW` | RO | Write-monitor per-channel overflow |

: Table 3.12.2: Monitor Register Map (base 0x1000)

Each `*_ENABLE` register carries `MON_EN`, `ERR_EN`, `COMPL_EN`, `TIMEOUT_EN`
(and `COMPRESS_EN` on the write monitor); each `*_PERF_*` group provides window,
producer, backpressure, starve, idle, beat, byte (lo/hi), and burst counters.

---

**Last Updated:** 2026-07-02
