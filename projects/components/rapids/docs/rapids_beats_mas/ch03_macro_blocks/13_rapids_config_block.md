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

# RAPIDS Config Block Specification

**Module:** `rapids_config_block.sv`
**Location:** `projects/components/rapids/rtl/macro_beats/`
**Status:** Implemented

---

## Overview

`rapids_config_block` is a combinational adapter that maps the register block's
`hwif_out` structure onto the flat `cfg_*` signals consumed by
`rapids_core_beats` and the AXI monitors. It contains no state; every output is a
direct assignment (with a small number of width expansions and global-enable
gates).

The monitor registers arrive under `hwif_out.MON.*`; base configuration and
status arrive at the top level of `hwif_out`.

---

## Mapping Groups

### Base Configuration

Routes scheduler, channel, and descriptor-engine configuration to the core:

- `cfg_channel_enable = CHANNEL_ENABLE.CH_EN & {8{GLOBAL_CTRL.GLOBAL_EN}}`
  (per-channel enable gated by the global master enable).
- `cfg_sched_timeout_cycles = SCHED_TIMEOUT_CYCLES.TIMEOUT_CYCLES` (32-bit).
- `cfg_sched_timeout_limit  = SCHED_TIMEOUT_LIMIT.LIMIT` (8-bit, direct).
- `cfg_desceng_*` from `DESCENG_CONFIG` (enable / prefetch / FIFO threshold).
- Descriptor address ranges (`cfg_desceng_addr{0,1}_{base,limit}`) are
  zero-extended from the 32-bit register fields to the 64-bit `ADDR_WIDTH`.

### Monitor Configuration (hwif_out.MON.*)

Three parallel groups map to the descriptor, read, and write AXI monitors:

| Register group | cfg_* target |
|----------------|--------------|
| `MON.DAXMON_*` | `cfg_desc_mon_*` (descriptor monitor) |
| `MON.RDMON_*`  | `cfg_rdeng_mon_*` (read monitor) |
| `MON.WRMON_*`  | `cfg_wreng_mon_*` (write monitor) |

: Table 3.13.1: Monitor Register-to-Config Mapping

Within each group the enable/timeout/latency/mask fields map 1:1, e.g.
`cfg_desc_mon_enable = MON.DAXMON_ENABLE.MON_EN & GLOBAL_CTRL.GLOBAL_EN`,
`cfg_desc_mon_timeout_cycles = MON.DAXMON_TIMEOUT.TIMEOUT_CYCLES`, and the
category masks (`timeout`/`compl`/`thresh`/`perf`/`addr`/`debug`) pass through
directly. Key enables are gated by `GLOBAL_CTRL.GLOBAL_EN`; masks pass through
ungated.

### Performance and Observation

`PERF_CONFIG`, `PERF_CH_SEL`, and `OBS_CTRL` map to the profiler and
channel-observation-mux `cfg_*` signals.

---

**Last Updated:** 2026-07-02
