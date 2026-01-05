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

# GAXI Synchronous FIFO

**Module:** `gaxi_fifo_sync.sv`
**Location:** `rtl/amba/gaxi/`
**Status:** ✅ Production Ready

---

## Overview

The GAXI synchronous FIFO provides elastic buffering for any depth (power of 2 recommended). Unlike the skid buffer, this module uses a true FIFO architecture with read/write pointers, supporting larger depths efficiently.

### Key Features

- ✅ **Arbitrary Depth:** Any depth supported (power of 2 optimal)
- ✅ **Two Read Modes:** Mux mode (combinatorial) or Flop mode (registered)
- ✅ **Counter-Based:** Binary counters with wrapping
- ✅ **Almost Full/Empty:** Configurable thresholds
- ✅ **Single Clock Domain:** Synchronous design

---

## Module Interface

```systemverilog
module gaxi_fifo_sync #(
    parameter int REGISTERED = 0,           // 0=mux mode, 1=flop mode
    parameter int DATA_WIDTH = 4,
    parameter int DEPTH = 4,
    parameter int ALMOST_WR_MARGIN = 1,
    parameter int ALMOST_RD_MARGIN = 1,
    parameter     INSTANCE_NAME = "DEADF1F0"
) (
    input  logic            axi_aclk,
    input  logic            axi_aresetn,
    input  logic            wr_valid,
    output logic            wr_ready,      // not full
    input  logic [DW-1:0]   wr_data,
    input  logic            rd_ready,
    output logic [AW:0]     count,
    output logic            rd_valid,      // not empty
    output logic [DW-1:0]   rd_data
);
```

---

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `REGISTERED` | 0 | 0=mux mode (comb read), 1=flop mode (reg read) |
| `DATA_WIDTH` | 4 | Data bus width |
| `DEPTH` | 4 | FIFO depth (any value, power-of-2 optimal) |
| `ALMOST_WR_MARGIN` | 1 | Almost full threshold |
| `ALMOST_RD_MARGIN` | 1 | Almost empty threshold |
| `INSTANCE_NAME` | "DEADF1F0" | Debug instance name |

---

## Functional Description

### Read Modes

#### Mux Mode (REGISTERED=0)
- **Latency:** 1 cycle write → read
- **Read Path:** Combinatorial from memory
- **Use Case:** Low latency applications
- **Timing:** May create combinatorial path

#### Flop Mode (REGISTERED=1)
- **Latency:** 2 cycles write → read
- **Read Path:** Registered output
- **Use Case:** Timing closure, deep pipelines
- **Timing:** No combinatorial paths

### Architecture

```mermaid
flowchart LR
    subgraph Inputs["Write Interface"]
        wrv["wr_valid"] --> fifo
        wrd["wr_data"] --> fifo
    end

    subgraph fifo["Sync FIFO"]
        ctr["Binary Counters<br/>(wr_ptr, rd_ptr)"]
        mem["Memory Array<br/>[DEPTH-1:0]"]
        ctrl["FIFO Control<br/>(full/empty)"]
    end

    subgraph Outputs["Read Interface"]
        fifo --> rdd["rd_data<br/>(mux or flop)"]
        fifo --> rdv["rd_valid"]
        fifo --> cnt["count"]
    end

    fifo --> wrr["wr_ready"]
    rdr["rd_ready"] --> fifo
```

### Dependencies

- `counter_bin.sv` - Binary counters for read/write pointers
- `fifo_control.sv` - Full/empty flag generation

---

## Usage Examples

### Example 1: Mux Mode (Low Latency)

```systemverilog
gaxi_fifo_sync #(
    .DATA_WIDTH(64),
    .DEPTH(32),
    .REGISTERED(0)        // Mux mode: 1-cycle latency
) u_low_latency_fifo (
    .axi_aclk    (clk),
    .axi_aresetn (rst_n),
    .wr_valid    (wr_valid),
    .wr_ready    (wr_ready),
    .wr_data     (wr_data),
    .rd_ready    (rd_ready),
    .rd_valid    (rd_valid),
    .rd_data     (rd_data),  // Combinatorial read
    .count       (fifo_level)
);
```

### Example 2: Flop Mode (Timing Closure)

```systemverilog
gaxi_fifo_sync #(
    .DATA_WIDTH(128),
    .DEPTH(64),
    .REGISTERED(1)        // Flop mode: 2-cycle latency
) u_registered_fifo (
    .axi_aclk    (clk),
    .axi_aresetn (rst_n),
    .wr_valid    (wr_valid),
    .wr_ready    (wr_ready),
    .wr_data     (wr_data),
    .rd_ready    (rd_ready),
    .rd_valid    (rd_valid),
    .rd_data     (rd_data),  // Registered output
    .count       (fifo_level)
);
```

---

## Timing Characteristics

| Mode | Write→Read Latency | Max Throughput | Read Path |
|------|-------------------|----------------|-----------|
| Mux (REGISTERED=0) | 1 cycle | 1/cycle | Combinatorial |
| Flop (REGISTERED=1) | 2 cycles | 1/cycle | Registered |

---

## Resource Utilization

| DEPTH | Mode | Flops | LUTs | Memory Bits |
|-------|------|-------|------|-------------|
| 16 | Mux | 16×DW + ~20 | ~80 | 16×DW |
| 16 | Flop | 16×DW + DW + ~20 | ~80 | 16×DW |
| 64 | Mux | 64×DW + ~30 | ~120 | 64×DW |
| 64 | Flop | 64×DW + DW + ~30 | ~120 | 64×DW |

---

## Testing

```bash
# Test FIFO modes
pytest val/amba/test_gaxi_buffer_sync.py -k "fifo_mux" -v   # Mux mode
pytest val/amba/test_gaxi_buffer_sync.py -k "fifo_flop" -v  # Flop mode
```

---

## Related Modules

- [gaxi_skid_buffer](gaxi_skid_buffer.md) - Zero-latency bypass, smaller depths
- [gaxi_fifo_async](gaxi_fifo_async.md) - Clock domain crossing version
- [GAXI Index](index.md) - Overview of all GAXI modules

---

**Version:** 1.0
**Last Updated:** 2025-10-06
