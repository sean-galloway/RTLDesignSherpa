<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> &middot; <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> &middot;
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> &middot;
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# CDC Open-Loop

**Module:** `cdc_open_loop.sv`
**Location:** `rtl/amba/shared/`
**Category:** Open-loop CDC (see [CDC Primer](cdc_primer.md))

---

## Overview

Open-loop multi-bit CDC using valid/data stretching. The source captures data on a single-cycle `src_valid` pulse and holds both data and a stretched valid level for `STRETCH_CYCLES` source clock cycles. The destination synchronizes the stretched valid and latches data on its rising edge.

No return path or handshake exists. The source is busy for exactly `STRETCH_CYCLES` source clocks, then free to send again. The designer must set `STRETCH_CYCLES` based on the known clock ratio.

### Key Features

- True open-loop: no return path, no handshake, no backpressure
- Source holds data and stretched valid for a parameterizable number of source clocks
- Destination uses multi-stage synchronizer + rising edge detect to latch data
- `src_busy` blocks the next transfer during the stretch window
- Minimal area: one counter, one synchronizer, one edge detector

### When to Use

- Clock ratio is known and fixed (or bounded)
- Destination is always ready (no flow control needed)
- Configuration register updates, status flags, infrequent events
- Minimum area/complexity is desired

### When NOT to Use

- Clock ratio unknown or variable -- use `cdc_2_phase_handshake` (closed-loop)
- Destination needs backpressure -- use a handshake
- Streaming data -- use `fifo_async` or `gaxi_fifo_async`

---

## Module Interface

```systemverilog
module cdc_open_loop #(
    parameter int DATA_WIDTH     = 8,
    parameter int STRETCH_CYCLES = 8,
    parameter int SYNC_STAGES    = 3
) (
    // Source clock domain
    input  logic                  clk_src,
    input  logic                  rst_src_n,
    input  logic                  src_valid,     // Single-cycle pulse
    input  logic [DATA_WIDTH-1:0] src_data,      // Data to transfer
    output logic                  src_busy,      // High during stretch

    // Destination clock domain
    input  logic                  clk_dst,
    input  logic                  rst_dst_n,
    output logic                  dst_valid,     // Single-cycle pulse
    output logic [DATA_WIDTH-1:0] dst_data       // Latched data
);
```

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `DATA_WIDTH` | 8 | Width of the data bus |
| `STRETCH_CYCLES` | 8 | Source clocks to hold valid+data stable |
| `SYNC_STAGES` | 3 | Destination synchronizer depth (2-4) |

### Setting STRETCH_CYCLES

The stretched valid must be seen by at least one destination clock edge after passing through the synchronizer. The guideline:

```
STRETCH_CYCLES >= ceil(1.5 * T_dst / T_src) + SYNC_STAGES
```

| Source Clock | Dest Clock | Ratio | SYNC_STAGES | Min STRETCH_CYCLES |
|-------------|------------|-------|-------------|-------------------|
| 100 MHz | 100 MHz | 1:1 | 3 | 5 |
| 100 MHz | 50 MHz | 2:1 | 3 | 6 |
| 100 MHz | 25 MHz | 4:1 | 3 | 9 |
| 200 MHz | 25 MHz | 8:1 | 3 | 15 |

When in doubt, round up. Extra stretch cycles cost only source-side latency, not area.

## Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `clk_src` | input | 1 | Source domain clock |
| `rst_src_n` | input | 1 | Source async reset (active low) |
| `src_valid` | input | 1 | Single-cycle pulse: data is valid |
| `src_data` | input | DATA_WIDTH | Data to transfer |
| `src_busy` | output | 1 | High during stretch countdown |
| `clk_dst` | input | 1 | Destination domain clock |
| `rst_dst_n` | input | 1 | Destination async reset (active low) |
| `dst_valid` | output | 1 | Single-cycle pulse: data latched |
| `dst_data` | output | DATA_WIDTH | Latched data (stable until next dst_valid) |

---

## Architecture

```
Source Domain (clk_src):                Destination Domain (clk_dst):

src_valid --+
            v
src_data --> [r_src_data] ---------------------------> [r_dst_data] --> dst_data
              (captured)         (quasi-static)         (latch on rise)

src_valid --> [r_src_valid_stretch] --> [SYNC] --> [edge detect] --> dst_valid
              held high for                 glitch_free
              STRETCH_CYCLES                n_dff_arn
                  |
           [r_stretch_count]
           countdown to 0
                  |
           src_busy = (count != 0)
```

### Timing Diagram

```
src_clk:     |~|_|~|_|~|_|~|_|~|_|~|_|~|_|~|_|~|_|~|_|
src_valid:   ____|~~|________________________________________
src_data:    ====|AAAA|======================================
src_busy:    ________|~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~|______
r_stretch:   ________|~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~|______
                      <-- STRETCH_CYCLES src clocks -->

dst_clk:     |~~~|___|~~~|___|~~~|___|~~~|___|~~~|___|~~~|___|
w_valid_sync:________________________|~~~~~~~~~~~~|__________
dst_valid:   ________________________________|~~|____________
dst_data:    ================================|AAAA|==========
```

---

## Usage Example

```systemverilog
// CPU writes config register at 100 MHz, peripheral runs at 25 MHz
// Ratio = 4:1, STRETCH_CYCLES = ceil(1.5 * 4) + 3 = 9
cdc_open_loop #(
    .DATA_WIDTH     (32),
    .STRETCH_CYCLES (9),
    .SYNC_STAGES    (3)
) u_cfg_cdc (
    .clk_src   (cpu_clk),        // 100 MHz
    .rst_src_n (cpu_rst_n),
    .src_valid (cfg_write_en),
    .src_data  (cfg_write_data),
    .src_busy  (cfg_busy),       // Block next write

    .clk_dst   (periph_clk),    // 25 MHz
    .rst_dst_n (periph_rst_n),
    .dst_valid (cfg_update),
    .dst_data  (cfg_value)
);
```

---

## SDC Constraints

```tcl
# 1. Stretched valid (single-bit level, synchronized by destination)
set_max_delay -datapath_only \
    -from [get_pins u_cdc/r_src_valid_stretch_reg/C] \
    -to   [get_pins u_cdc/u_valid_sync/q_reg[0]/D] \
    <dst_period_ns>

# 2. Data bus (quasi-static, held for STRETCH_CYCLES src clocks)
set_max_delay -datapath_only \
    -from [get_pins u_cdc/r_src_data_reg[*]/C] \
    -to   [get_pins u_cdc/r_dst_data_reg[*]/D] \
    <dst_period_ns>
```

Do NOT use `set_false_path` -- the data bus must arrive within a bounded window.

---

## Resources

- RTL: `rtl/amba/shared/cdc_open_loop.sv`
- Depends on: `rtl/common/glitch_free_n_dff_arn.sv`
- CDC Primer: [cdc_primer.md](cdc_primer.md)
- Closed-loop alternative: [cdc_2_phase_handshake.md](cdc_2_phase_handshake.md)

---

**Last Updated:** 2026-04-21

---

## Navigation

- [Back to CDC Primer](cdc_primer.md)
- [Back to Shared Infrastructure Index](README.md)
