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

# APB Configuration Interface

## Overview

At the top level (`rapids_beats_top`), RAPIDS Beats exposes a single **APB4
slave** (`s_apb_*`) for all software access. This interface allows software to:

1. Configure channel and monitor parameters (via the register block)
2. Initiate descriptor processing (kick-off)
3. Read status and error information

## APB Slave and Address Routing

The APB slave is converted to an internal command/response transaction and
routed by address to two targets:

| Address Range | Target | Purpose |
|---------------|--------|---------|
| 0x000-0x03F | Descriptor kick-off (`apbtodescr`) | Per-channel descriptor chain start |
| 0x100-0x3FF | `rapids_regs` (base regfile) | Channel/scheduler/descriptor configuration and status |
| 0x1000+ | `rapids_regs` (monitor regfile) | AXI-monitor configuration and performance counters |

: APB Address Routing

Because the monitor regfile is located at 0x1000, the APB address bus must be at
least 13 bits wide to reach it. Configuration that was formerly imagined as
discrete `cfg_*` ports is now driven internally by the register block through
`rapids_config_block`; see the [Register Map](../ch05_programming/02_register_map.md)
for the full address map, and the descriptor address ranges
(`DESCENG_ADDR0/1_*` at 0x224-0x230).

### APB Slave Signal List

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `s_apb_paddr` | APB_ADDR_WIDTH (>=13) | input | Address |
| `s_apb_psel` | 1 | input | Select |
| `s_apb_penable` | 1 | input | Enable phase |
| `s_apb_pwrite` | 1 | input | Write / read |
| `s_apb_pwdata` | 32 | input | Write data |
| `s_apb_pstrb` | 4 | input | Write byte strobes |
| `s_apb_prdata` | 32 | output | Read data |
| `s_apb_pready` | 1 | output | Ready |
| `s_apb_pslverr` | 1 | output | Slave error |

: APB Slave Signals

### Descriptor Kick-Off

To start descriptor processing on a channel:

1. Write descriptor to memory
2. Assert `apb_valid[ch]` with descriptor address on `apb_addr`
3. Wait for `apb_ready[ch]` assertion
4. Deassert `apb_valid[ch]`

### Timing Diagram

![APB Kick-Off Timing](../assets/wavedrom/apb_kickoff_timing.svg)

**Source:** [apb_kickoff_timing.json](../assets/wavedrom/apb_kickoff_timing.json)

```wavedrom
{
  "signal": [
    {"name": "clk", "wave": "p........"},
    {},
    {"name": "apb_valid[0]", "wave": "0.1..0..."},
    {"name": "apb_ready[0]", "wave": "1....0.1."},
    {"name": "apb_addr", "wave": "x.=..x...", "data": ["DESC_ADDR"]},
    {},
    {"name": "channel_idle[0]", "wave": "1....0..."},
    {"name": "desc_fetch_start", "wave": "0...1.0.."}
  ],
  "config": {"hscale": 1.5},
  "head": {"text": "Descriptor Kick-Off Sequence"}
}
```

## Status Interface

### Per-Channel Status Signals

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `channel_idle` | NC | output | Channel idle status |
| `channel_error` | NC | output | Channel error flag |
| `scheduler_state` | 4*NC | output | FSM state per channel |

: Status Signals

### Channel State Encoding

| State | Value | Description |
|-------|-------|-------------|
| IDLE | 4'h0 | Waiting for kick-off |
| WAIT_DESC | 4'h1 | Waiting for descriptor |
| PARSE_DESC | 4'h2 | Parsing descriptor |
| CH_XFER_DATA | 4'h3 | Transfer in progress |
| CHECK_NEXT | 4'h4 | Checking next descriptor |
| COMPLETE | 4'h5 | Transfer complete |
| ERROR | 4'hF | Error state |

: Scheduler State Encoding

## Configuration Registers

### Address Range Validation

RAPIDS validates descriptor addresses against configurable ranges:

```
Valid if:
  (addr >= cfg_addr0_base && addr < cfg_addr0_limit) ||
  (addr >= cfg_addr1_base && addr < cfg_addr1_limit)
```

### Configuration Registers

Configuration and status registers are provided by the `rapids_regs` register
block. See the [Register Map](../ch05_programming/02_register_map.md) for the
complete, RTL-accurate address map. The registers most relevant to bring-up are:

| Register | Offset | Description |
|----------|--------|-------------|
| `GLOBAL_CTRL` | 0x100 | `GLOBAL_EN`, `GLOBAL_RST` (self-clearing) |
| `CHANNEL_ENABLE` | 0x120 | Per-channel enable bitmap |
| `SCHED_TIMEOUT_CYCLES` | 0x200 | Write-progress timeout window |
| `SCHED_TIMEOUT_LIMIT` | 0x208 | Consecutive-timeout escalation limit (0 = never) |
| `DESCENG_CONFIG` | 0x220 | Descriptor-engine enable / prefetch / FIFO threshold |
| `DESCENG_ADDR0_BASE`/`_LIMIT` | 0x224/0x228 | Descriptor address range 0 |

: Key Configuration Registers

## Programming Sequence

### Initialization

```c
// 1. Optional global reset (self-clearing)
GLOBAL_CTRL = 0x2;
while (GLOBAL_CTRL & 0x2);   // wait for GLOBAL_RST to clear

// 2. Configure descriptor address range(s)
DESCENG_ADDR0_BASE  = 0x8000_0000;
DESCENG_ADDR0_LIMIT = 0x9000_0000;

// 3. Scheduler timeout policy
SCHED_TIMEOUT_CYCLES = 1000;
SCHED_TIMEOUT_LIMIT  = 4;    // escalate after 4 stalled windows; 0 = never

// 4. Enable channels and global enable
CHANNEL_ENABLE = 0xFF;       // enable all 8 channels
GLOBAL_CTRL    = 0x1;        // GLOBAL_EN
```

### Descriptor Kick-Off

```c
// Prepare descriptor in memory
desc->src_addr = src;
desc->dst_addr = dst;
desc->length = beats;
desc->last = 1;
desc->valid = 1;

// Kick off channel 0
apb_kickoff(0, desc_addr);

// Wait for completion
while (!(channel_idle & 0x01));

// Check for errors
if (channel_error & 0x01) {
    handle_error(0);
}
```
