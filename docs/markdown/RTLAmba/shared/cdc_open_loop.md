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
**Status:** Production Ready
**Category:** Open-loop CDC (see [CDC Primer](cdc_primer.md))

---

## Overview

Open-loop multi-bit CDC with synchronized enable pulse. The source holds data stable and asserts a single-cycle valid pulse. A `sync_pulse` synchronizer carries the valid indication to the destination domain, which latches the data on the synchronized pulse.

No acknowledge path exists. The source MUST guarantee that data remains stable for at least `SYNC_STAGES + 1` destination clock cycles after asserting `src_valid`.

### Key Features

- Simplest vector CDC -- minimal logic and area
- No backpressure or handshake overhead
- Uses `sync_pulse` internally for valid crossing
- Source-side holding register keeps data stable during crossing
- Single-cycle `dst_valid` pulse in destination domain
- Parameterizable data width and synchronizer depth

### When to Use

- Configuration register updates (CPU writes, peripheral reads later)
- Infrequent status transfers where source naturally holds data
- Fast-to-slow domain crossings where data persists for many slow clocks
- Any scenario where backpressure is not needed

### When NOT to Use

- Source cannot guarantee hold time -- use `cdc_2_phase_handshake` instead
- Destination needs flow control -- use a handshake or async FIFO
- Streaming data -- use `fifo_async` or `gaxi_fifo_async`

---

## Module Interface

```systemverilog
module cdc_open_loop #(
    parameter int DATA_WIDTH  = 8,
    parameter int SYNC_STAGES = 3
) (
    // Source clock domain
    input  logic                  clk_src,
    input  logic                  rst_src_n,
    input  logic                  src_valid,    // Single-cycle pulse
    input  logic [DATA_WIDTH-1:0] src_data,     // Stable for SYNC_STAGES+1 dst clocks

    // Destination clock domain
    input  logic                  clk_dst,
    input  logic                  rst_dst_n,
    output logic                  dst_valid,    // Single-cycle pulse
    output logic [DATA_WIDTH-1:0] dst_data      // Latched, stable until next dst_valid
);
```

## Parameters

| Parameter | Default | Range | Description |
|-----------|---------|-------|-------------|
| `DATA_WIDTH` | 8 | 1+ | Width of the data bus |
| `SYNC_STAGES` | 3 | 2-4 | Synchronizer depth for valid pulse |

## Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `clk_src` | input | 1 | Source domain clock |
| `rst_src_n` | input | 1 | Source async reset (active low) |
| `src_valid` | input | 1 | Single-cycle pulse indicating data is valid |
| `src_data` | input | DATA_WIDTH | Data to transfer (hold stable after valid) |
| `clk_dst` | input | 1 | Destination domain clock |
| `rst_dst_n` | input | 1 | Destination async reset (active low) |
| `dst_valid` | output | 1 | Single-cycle pulse when data is latched |
| `dst_data` | output | DATA_WIDTH | Latched data (stable until next dst_valid) |

---

## Architecture

```
Source Domain (clk_src):           Destination Domain (clk_dst):

src_data ----> [r_src_data] --------+
                                    |
src_valid ---> [sync_pulse] --------|-----> w_dst_valid_pulse
               (toggle +            |            |
                edge detect)        +----> [r_dst_data] ----> dst_data
                                         (latch on pulse)
                                               |
                                         [r_dst_valid] ----> dst_valid
```

1. Source captures `src_data` into `r_src_data` on `src_valid`
2. `sync_pulse` converts the valid pulse to the destination domain
3. When `w_dst_valid_pulse` fires, destination latches `r_src_data` into `r_dst_data`
4. `dst_valid` is asserted for one destination clock cycle

---

## Usage Example

```systemverilog
// CPU writes a config register; peripheral reads it in a different clock domain
cdc_open_loop #(
    .DATA_WIDTH  (32),
    .SYNC_STAGES (3)
) u_cfg_cdc (
    .clk_src   (cpu_clk),
    .rst_src_n (cpu_rst_n),
    .src_valid (cfg_write_en),    // Pulse on APB write
    .src_data  (cfg_write_data),  // Held by APB until next write

    .clk_dst   (periph_clk),
    .rst_dst_n (periph_rst_n),
    .dst_valid (cfg_update),      // Pulse in peripheral domain
    .dst_data  (cfg_value)        // New config value
);
```

---

## Timing Constraints

The source must guarantee data stability. The minimum spacing between `src_valid` pulses is `SYNC_STAGES + 1` destination clock cycles. Violating this loses transfers silently -- there is no error indication.

```
src_clk:  _|~|_|~|_|~|_|~|_|~|_|~|_|~|_|~|_|~|_|~|
src_valid: __|~~|______________________________________  (pulse)
src_data:  ==|AAAA|====================================  (hold stable)
                    |<-- SYNC_STAGES+1 dst clocks -->|
dst_clk:  _|~~~|___|~~~|___|~~~|___|~~~|___|~~~|___|~~~|
dst_valid: ________________________________|~~|________  (pulse)
dst_data:  ================================|AAAA|======  (latched)
```

---

## Resources

- RTL: `rtl/amba/shared/cdc_open_loop.sv`
- Depends on: `rtl/common/sync_pulse.sv`
- CDC Primer: [cdc_primer.md](cdc_primer.md)
- Related: [cdc_2_phase_handshake.md](cdc_2_phase_handshake.md) (closed-loop alternative)

---

**Last Updated:** 2026-04-21

---

## Navigation

- [Back to CDC Primer](cdc_primer.md)
- [Back to Shared Infrastructure Index](README.md)
