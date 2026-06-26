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

# CDC Open-Loop

**Module:** `cdc_open_loop.sv`
**Location:** `rtl/amba/shared/`
**Category:** Open-loop CDC (see [CDC Primer](cdc_primer.md))

---

## Overview

Open-loop multi-bit CDC using valid/data stretching. The source captures data on a single-cycle `src_valid` pulse and holds both data and a stretched valid level for `STRETCH_CYCLES` source clock cycles. The destination synchronizes the stretched valid and latches data on its rising edge.

No return path or handshake exists. The source is busy for exactly `STRETCH_CYCLES` source clocks, then free to send again. The stretch length can either be set manually (`STRETCH_CYCLES`) or computed from the source/destination clock frequencies (`AUTO_STRETCH=1` with `SRC_CLK_HZ` and `DST_CLK_HZ`).

### Key Features

- True open-loop: no return path, no handshake, no backpressure
- Source holds data and stretched valid for a parameterizable number of source clocks
- Destination uses multi-stage synchronizer + rising edge detect to latch data
- `src_busy` blocks the next transfer during the stretch window
- Optional auto-compute: pass clock frequencies and the module sizes `STRETCH` itself
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
    parameter int SYNC_STAGES    = 2,

    // Optional auto-compute of STRETCH_CYCLES from clock frequencies
    parameter int AUTO_STRETCH = 0,             // 0 = use STRETCH_CYCLES; 1 = auto
    parameter int SRC_CLK_HZ   = 25_000_000,    // Fastest source clock to handle
    parameter int DST_CLK_HZ   = 100_000_000    // Destination clock frequency
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
| `STRETCH_CYCLES` | 8 | Source clocks to hold valid+data stable (used when `AUTO_STRETCH=0`) |
| `SYNC_STAGES` | 2 | Destination synchronizer depth (2-4; raise for extra MTBF margin) |
| `AUTO_STRETCH` | 0 | `0` = use `STRETCH_CYCLES`; `1` = compute from `SRC_CLK_HZ` / `DST_CLK_HZ` |
| `SRC_CLK_HZ` | 25_000_000 | Source clock frequency (used when `AUTO_STRETCH=1`) |
| `DST_CLK_HZ` | 100_000_000 | Destination clock frequency (used when `AUTO_STRETCH=1`) |

### Setting STRETCH_CYCLES manually (`AUTO_STRETCH=0`)

This is a multi-bit data CDC, so the source data bus must remain stable until the synchronized enable has propagated through the destination sync chain *and* loaded the destination register. That gives:

```
STRETCH_CYCLES >= ceil((SYNC_STAGES + 1) * T_dst / T_src)
```

`(SYNC_STAGES + 1)` counts the synchronizer FFs plus the destination load edge. The 1.5 × T_dst "rule of thumb" you may have seen is enough to capture the valid pulse alone, but a multi-bit datapath needs the longer hold so `r_src_data` is still stable when the destination latches it. See *References* below.

| Source Clock | Dest Clock | Ratio | SYNC_STAGES | Min STRETCH_CYCLES |
|-------------|------------|-------|-------------|-------------------|
| 100 MHz | 100 MHz | 1:1 | 2 | 3 |
| 100 MHz | 50 MHz | 2:1 | 2 | 6 |
| 100 MHz | 25 MHz | 4:1 | 2 | 12 |
| 1 GHz | 100 MHz | 10:1 | 2 | 30 |
| 200 MHz | 25 MHz | 8:1 | 2 | 24 |

When in doubt, round up — extra stretch cycles cost only source-side latency, not area.

### Auto-computed STRETCH (`AUTO_STRETCH=1`)

Set `AUTO_STRETCH=1` and pass the source/destination clock frequencies in Hz. The module computes `STRETCH_CYCLES` at elaboration time using:

```
STRETCH = ceil((SYNC_STAGES + 1) * SRC_CLK_HZ / DST_CLK_HZ)
```

The result is a localparam — folds to a literal in synthesis, no runtime cost. `SRC_CLK_HZ` should be the **fastest** source clock you intend to support; sources running faster will start dropping pulses.

When `AUTO_STRETCH=1` the `STRETCH_CYCLES` parameter is ignored. When `AUTO_STRETCH=0` (default) the auto-formula is dead code and `STRETCH_CYCLES` is used as-is, so existing callers see no change.

| Source `SRC_CLK_HZ` | Destination `DST_CLK_HZ` | Computed `STRETCH` (SYNC=2) |
|---------------------|--------------------------|-----------------------------|
| 25 MHz  | 100 MHz | 1 |
| 50 MHz  | 100 MHz | 2 |
| 100 MHz | 100 MHz | 3 |
| 100 MHz | 40 MHz  | 8 |
| 100 MHz | 25 MHz  | 12 |
| 1 GHz   | 100 MHz | 30 |

Prefer auto when the clock plan is captured in a single top-level location — propagate `SRC_CLK_HZ` / `DST_CLK_HZ` as parameters from the top and every instance retunes itself if the clock plan changes.

### Back-to-back pulses

`src_busy` only guards the HIGH stretch window. After it falls, the destination sync chain still needs roughly `(SYNC_STAGES + 1) * T_dst` to see the falling edge before another rising edge can be detected. If the source asserts the next `src_valid` immediately after `src_busy` falls, two HIGH stretches can merge in the dst view and the second pulse is silently dropped.

Two ways to keep this safe:

1. Pick `STRETCH_CYCLES` large enough that one full source-side LOW cycle is comfortably more than `(SYNC_STAGES + 1) * T_dst`. (For slow-source → fast-dst this is automatic; for fast-source → slow-dst you may need extra margin.)
2. Have the source pace pulses: wait `src_busy` to fall, then idle for `ceil((SYNC_STAGES + 1) * T_dst / T_src) + 1` source cycles before the next `src_valid`.

The verification testbench (`bin/TBClasses/amba/cdc_open_loop.py`) enforces option 2 in its no-loss phases.

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

### Manual STRETCH (back-compat default)

```systemverilog
// CPU writes config register at 100 MHz, peripheral runs at 25 MHz
// Ratio = 4:1, STRETCH_CYCLES = ceil((2+1) * 4) = 12
cdc_open_loop #(
    .DATA_WIDTH     (32),
    .STRETCH_CYCLES (12),
    .SYNC_STAGES    (2)
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

### Auto STRETCH from clock frequencies

```systemverilog
// Same CPU→peripheral CDC, but let the module size STRETCH itself.
// If the clock plan changes (e.g. CPU bumped to 200 MHz) you only
// update SRC_CLK_HZ at the top and every instance retunes.
localparam int CPU_HZ    = 100_000_000;
localparam int PERIPH_HZ = 25_000_000;

cdc_open_loop #(
    .DATA_WIDTH   (32),
    .SYNC_STAGES  (2),
    .AUTO_STRETCH (1),
    .SRC_CLK_HZ   (CPU_HZ),
    .DST_CLK_HZ   (PERIPH_HZ)
) u_cfg_cdc (
    .clk_src   (cpu_clk),
    .rst_src_n (cpu_rst_n),
    .src_valid (cfg_write_en),
    .src_data  (cfg_write_data),
    .src_busy  (cfg_busy),

    .clk_dst   (periph_clk),
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
- Testbench: `bin/TBClasses/amba/cdc_open_loop.py`
- Test runner: `val/amba/test_cdc_open_loop.py` (28 configs covering manual, auto, and cliff)
- CDC Primer: [cdc_primer.md](cdc_primer.md)
- Closed-loop alternative: [cdc_2_phase_handshake.md](cdc_2_phase_handshake.md)

## References

The `(SYNC_STAGES + 1) × T_dst` data-hold requirement follows directly from the MCP (Multi-Cycle Path) formulation: the source data must stay stable until the synchronized enable has traversed the destination sync chain and loaded the destination register. The exact closed-form formula is this module's own — the cited references state the principle qualitatively and leave the cycle count to the reader.

- Clifford E. Cummings, *Clock Domain Crossing (CDC) Design & Verification Techniques Using SystemVerilog*, SNUG Boston 2008 — original MCP formulation.
- Verilog Pro, [*Clock Domain Crossing Design — Part 2*](https://www.verilogpro.com/clock-domain-crossing-part-2/): "the input data has to be held until the synchronization pulse loads the data in the destination clock domain. The whole process takes at least two destination clocks." (= `SYNC_STAGES + 1` destination cycles for a 2-FF synchronizer.)
- thedatabus.in, [*Clock Domain Crossing (CDC): The Complete Reference Guide*](https://thedatabus.in/cdc_complete_guide/): "ensure that the source holds the information long enough for it to be safely taken through all the synchronizer stages."
- EDN, [*Understanding Clock Domain Crossing*](https://www.eetimes.com/understanding-clock-domain-crossing-issues/).

---

**Last Updated:** 2026-06-26

---

## Navigation

- [Back to CDC Primer](cdc_primer.md)
- [Back to Shared Infrastructure Index](README.md)
