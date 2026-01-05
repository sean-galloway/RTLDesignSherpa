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

# APB Configuration Block

**Module:** `stream_config_block.sv`
**Location:** `projects/components/stream/rtl/top/`
**Category:** TOP (Integration)
**Parent:** `stream_top.sv`
**Status:** Implemented
**Last Updated:** 2025-11-30

---

## Overview

The `stream_config_block` module maps PeakRDL-generated register outputs to STREAM core configuration inputs. It provides a clean interface layer between the register file and the STREAM DMA engine core, handling field extraction, width conversion, and global enable gating.

### Key Features

- **Field Extraction:** Extracts fields from packed register values
- **Width Conversion:** Converts register fields to configuration signal widths
- **Global Enable Gating:** Gates enables by global enable register
- **Address Extension:** Zero-extends 32-bit register addresses to 64-bit
- **Clean Interface:** Isolates register naming from core logic

---

## Architecture

### Block Diagram

### Figure 1: Stream Config Block Diagram

![Stream Config Block Diagram](../assets/mermaid/14_stream_config_block.png)

**Source:** [14_stream_config_block.mmd](../assets/mermaid/14_stream_config_block.mmd)

### Configuration Groups

```
stream_config_block
 Global and Channel Control
    cfg_channel_enable (gated by global_en)
    cfg_channel_reset (OR'd with global_rst)
 Scheduler Configuration
    cfg_sched_enable (gated by global_en)
    cfg_sched_timeout_cycles
    cfg_sched_*_enable flags
 Descriptor Engine Configuration
    cfg_desceng_enable (gated by global_en)
    cfg_desceng_prefetch
    cfg_desceng_addr*_base/limit (zero-extended)
 Monitor Configurations (3 sets)
    Descriptor AXI Monitor (cfg_desc_mon_*)
    Read Engine Monitor (cfg_rdeng_mon_*)
    Write Engine Monitor (cfg_wreng_mon_*)
 AXI Transfer Configuration
    cfg_axi_rd_xfer_beats
    cfg_axi_wr_xfer_beats
 Performance Profiler
     cfg_perf_enable (gated by global_en)
     cfg_perf_mode
     cfg_perf_clear
```

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `NUM_CHANNELS` | int | 8 | Number of DMA channels |
| `ADDR_WIDTH` | int | 64 | Address width for config outputs |

: Parameters

---

## Port List

### Clock and Reset

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `clk` | input | 1 | System clock |
| `rst_n` | input | 1 | Active-low asynchronous reset |

: Clock and Reset

### PeakRDL Register Inputs

**Global Control:**

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `reg_global_ctrl_global_en` | input | 1 | Global enable |
| `reg_global_ctrl_global_rst` | input | 1 | Global reset |
| `reg_channel_enable_ch_en` | input | 8 | Per-channel enable bits |
| `reg_channel_reset_ch_rst` | input | 8 | Per-channel reset bits |

: PeakRDL Register Inputs

**Scheduler Configuration:**

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `reg_sched_timeout_cycles_*` | input | 16 | Timeout threshold |
| `reg_sched_config_*` | input | 1 | Various enables |

: PeakRDL Register Inputs

**Descriptor Engine Configuration:**

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `reg_desceng_config_*` | input | varies | Enable and threshold |
| `reg_desceng_addr*_*` | input | 32 | Address range limits |

: PeakRDL Register Inputs

**Monitor Configurations (3 sets):**

Each monitor (DAXMON, RDMON, WRMON) has:
- `reg_*_enable_*` - Enable flags
- `reg_*_timeout_*` - Timeout configuration
- `reg_*_latency_thresh_*` - Latency threshold
- `reg_*_pkt_mask_*` - Packet type mask
- `reg_*_err_cfg_*` - Error configuration
- `reg_*_mask*_*` - Event masks

**AXI Transfer Configuration:**

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `reg_axi_xfer_config_rd_xfer_beats` | input | 8 | Read burst size |
| `reg_axi_xfer_config_wr_xfer_beats` | input | 8 | Write burst size |

: PeakRDL Register Inputs

**Performance Profiler:**

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `reg_perf_config_perf_en` | input | 1 | Profiler enable |
| `reg_perf_config_perf_mode` | input | 1 | Profiling mode |
| `reg_perf_config_perf_clear` | input | 1 | Clear profiler |

: PeakRDL Register Inputs

### Configuration Outputs

**Global and Channel:**

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cfg_channel_enable` | output | NUM_CHANNELS | Gated channel enables |
| `cfg_channel_reset` | output | NUM_CHANNELS | Combined channel resets |

: Configuration Outputs

**Scheduler:**

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cfg_sched_enable` | output | 1 | Gated scheduler enable |
| `cfg_sched_timeout_cycles` | output | 16 | Timeout value |
| `cfg_sched_*_enable` | output | 1 | Feature enables |

: Configuration Outputs

**Descriptor Engine:**

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cfg_desceng_enable` | output | 1 | Gated desceng enable |
| `cfg_desceng_prefetch` | output | 1 | Prefetch enable |
| `cfg_desceng_fifo_thresh` | output | 4 | FIFO threshold |
| `cfg_desceng_addr*_base` | output | ADDR_WIDTH | Zero-extended address |
| `cfg_desceng_addr*_limit` | output | ADDR_WIDTH | Zero-extended address |

: Configuration Outputs

**Monitor Outputs (3 sets):**

Each monitor outputs ~16 configuration signals covering:
- Enable flags
- Timeout values
- Thresholds
- Masks

**AXI Transfer:**

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cfg_axi_rd_xfer_beats` | output | 8 | Read burst size |
| `cfg_axi_wr_xfer_beats` | output | 8 | Write burst size |

: Configuration Outputs

**Performance Profiler:**

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cfg_perf_enable` | output | 1 | Gated profiler enable |
| `cfg_perf_mode` | output | 1 | Profiling mode |
| `cfg_perf_clear` | output | 1 | Clear signal |

: Configuration Outputs

---

## Operation

### Global Enable Gating

```systemverilog
// Gate all channel enables by global enable
assign cfg_channel_enable = reg_channel_enable_ch_en & {NUM_CHANNELS{reg_global_ctrl_global_en}};

// Gate scheduler enable
assign cfg_sched_enable = reg_sched_config_sched_en & reg_global_ctrl_global_en;

// Gate monitor enables
assign cfg_desc_mon_enable = reg_daxmon_enable_mon_en & reg_global_ctrl_global_en;
```

### Global Reset OR

```systemverilog
// Channel resets are OR'd with global reset
assign cfg_channel_reset = reg_channel_reset_ch_rst | {NUM_CHANNELS{reg_global_ctrl_global_rst}};
```

### Address Zero Extension

```systemverilog
// Zero-extend 32-bit register addresses to ADDR_WIDTH (typically 64-bit)
assign cfg_desceng_addr0_base = {{(ADDR_WIDTH-32){1'b0}}, reg_desceng_addr0_base_addr0_base};
assign cfg_desceng_addr0_limit = {{(ADDR_WIDTH-32){1'b0}}, reg_desceng_addr0_limit_addr0_limit};
```

---

## Integration Example

```systemverilog
stream_config_block #(
    .NUM_CHANNELS   (8),
    .ADDR_WIDTH     (64)
) u_config_block (
    .clk            (clk),
    .rst_n          (rst_n),

    // From PeakRDL register file
    .reg_global_ctrl_global_en      (regs_global_ctrl_global_en),
    .reg_global_ctrl_global_rst     (regs_global_ctrl_global_rst),
    .reg_channel_enable_ch_en       (regs_channel_enable_ch_en),
    // ... more register inputs

    // To stream_core
    .cfg_channel_enable             (cfg_channel_enable),
    .cfg_channel_reset              (cfg_channel_reset),
    .cfg_sched_enable               (cfg_sched_enable),
    // ... more config outputs
);
```

---

## Related Documentation

- **Parent:** `01_stream_core.md` - Receives configuration signals
- **Register File:** PeakRDL-generated `stream_regs.sv`
- **Scheduler:** `04_scheduler.md` - Uses sched_* config
- **Descriptor Engine:** `05_descriptor_engine.md` - Uses desceng_* config
- **Monitors:** Monitor documentation for each AXI monitor
---

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 0.90 | 2025-11-22 | seang | Initial block specification |
| 0.91 | 2026-01-02 | seang | Added table captions and figure numbers |

: APB Configuration Block Revision History

---

**Last Updated:** 2026-01-02
