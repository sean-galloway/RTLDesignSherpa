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

# MonBus AXI-Lite Group

**Module:** `monbus_axil_group.sv`
**Location:** `projects/components/stream/rtl/macro/`
**Category:** MACRO (Integration)
**Parent:** `stream_top.sv`
**Status:** Implemented
**Last Updated:** 2025-11-30

---

## Overview

The `monbus_axil_group` module receives monitor bus packets from STREAM channels, applies configurable filtering, and routes filtered packets to either an error/interrupt FIFO (accessible via AXI-Lite slave) or a master write interface (writes to memory).

### Key Features

- **Single Monitor Bus Input:** STREAM is memory-to-memory (no network paths)
- **Per-Protocol Filtering:** Configurable packet type masking
- **Dual Output Paths:**
  - Error/Interrupt FIFO - generates interrupt when not empty
  - Master Write FIFO - writes to configurable address range
- **Protocol Support:** AXI, AXIS, CORE (3 protocols)
- **Built-in AXI-Lite Skid Buffering:** For timing closure

### Simplified from RAPIDS

RAPIDS has source + sink data paths requiring TWO monitor buses. STREAM has memory-to-memory only, so this module has ONE monitor bus input (no arbitration needed).

---

## Architecture

### Block Diagram

### Figure 2.16.1: MonBus AXI-Lite Group Block Diagram

![MonBus AXI-Lite Group Block Diagram](../assets/mermaid/16_monbus_axil_group_block.png)

**Source:** [16_monbus_axil_group_block.mmd](../assets/mermaid/16_monbus_axil_group_block.mmd)

### Filter Decision Tree

```
For each incoming packet:
1. Extract: pkt_type, pkt_protocol, pkt_event_code
2. Check protocol-specific masks:
   - pkt_mask: Drop if bit[pkt_type] = 1
   - err_select: Route to error FIFO if bit[pkt_type] = 1
   - event_mask: Drop if bit[event_code] = 1
3. Route:
   - Dropped packets: Consumed silently
   - Error-selected: To error/interrupt FIFO
   - Remaining: To master write FIFO
```

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `FIFO_DEPTH_ERR` | int | 64 | Error/interrupt FIFO depth |
| `FIFO_DEPTH_WRITE` | int | 32 | Master write FIFO depth |
| `ADDR_WIDTH` | int | 32 | AXI address width |
| `DATA_WIDTH` | int | 32 | AXI data width |
| `NUM_PROTOCOLS` | int | 3 | AXI, AXIS, CORE |

: Parameters

---

## Port List

### Clock and Reset

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `axi_aclk` | input | 1 | AXI clock |
| `axi_aresetn` | input | 1 | AXI active-low reset |

: Clock and Reset

### Monitor Bus Input

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `monbus_valid` | input | 1 | Packet valid |
| `monbus_ready` | output | 1 | Ready to accept |
| `monbus_packet` | input | 64 | 64-bit monitor packet |

: Monitor Bus Input

### AXI-Lite Slave Read Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `s_axil_arvalid` | input | 1 | Read address valid |
| `s_axil_arready` | output | 1 | Read address ready |
| `s_axil_araddr` | input | ADDR_WIDTH | Read address |
| `s_axil_arprot` | input | 3 | Protection bits |
| `s_axil_rvalid` | output | 1 | Read data valid |
| `s_axil_rready` | input | 1 | Read data ready |
| `s_axil_rdata` | output | DATA_WIDTH | Read data |
| `s_axil_rresp` | output | 2 | Read response |

: AXI-Lite Slave Read Interface

### AXI-Lite Master Write Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axil_awvalid` | output | 1 | Write address valid |
| `m_axil_awready` | input | 1 | Write address ready |
| `m_axil_awaddr` | output | ADDR_WIDTH | Write address |
| `m_axil_awprot` | output | 3 | Protection bits |
| `m_axil_wvalid` | output | 1 | Write data valid |
| `m_axil_wready` | input | 1 | Write data ready |
| `m_axil_wdata` | output | DATA_WIDTH | Write data |
| `m_axil_wstrb` | output | DATA_WIDTH/8 | Write strobes |
| `m_axil_bvalid` | input | 1 | Write response valid |
| `m_axil_bready` | output | 1 | Write response ready |
| `m_axil_bresp` | input | 2 | Write response |

: AXI-Lite Master Write Interface

### Interrupt Output

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `irq_out` | output | 1 | Interrupt (error FIFO not empty) |

: Interrupt Output

### Configuration Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cfg_base_addr` | input | ADDR_WIDTH | Base for master writes |
| `cfg_limit_addr` | input | ADDR_WIDTH | Limit for master writes |

: Configuration Interface

### Protocol Configuration (per protocol)

**AXI Protocol:**

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cfg_axi_pkt_mask` | input | 16 | Drop mask for packet types |
| `cfg_axi_err_select` | input | 16 | Error FIFO select |
| `cfg_axi_*_mask` | input | 16 | Per-event-type masks |

: Protocol Configuration

**AXIS Protocol:**

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cfg_axis_pkt_mask` | input | 16 | Drop mask |
| `cfg_axis_err_select` | input | 16 | Error FIFO select |
| `cfg_axis_*_mask` | input | 16 | Per-event-type masks |

: Protocol Configuration

**CORE Protocol:**

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cfg_core_pkt_mask` | input | 16 | Drop mask |
| `cfg_core_err_select` | input | 16 | Error FIFO select |
| `cfg_core_*_mask` | input | 16 | Per-event-type masks |

: Protocol Configuration

### Debug/Status

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `err_fifo_full` | output | 1 | Error FIFO full |
| `write_fifo_full` | output | 1 | Write FIFO full |
| `err_fifo_count` | output | 8 | Error FIFO count |
| `write_fifo_count` | output | 8 | Write FIFO count |

: Debug/Status

---

## Operation

### Packet Type Filtering

```systemverilog
// Protocol-specific filtering (example: AXI)
case (pkt_protocol)
    3'b000: begin // AXI
        // Check if packet type is dropped
        pkt_drop = cfg_axi_pkt_mask[pkt_type];

        // Check if packet goes to error FIFO
        pkt_to_err_fifo = cfg_axi_err_select[pkt_type] && !pkt_drop;

        // Check individual event masking
        case (pkt_type)
            PktTypeError:     pkt_event_masked = cfg_axi_error_mask[pkt_event_code];
            PktTypeTimeout:   pkt_event_masked = cfg_axi_timeout_mask[pkt_event_code];
            // ... more packet types
        endcase
    end
endcase
```

### Master Write Address Generation

```systemverilog
// Address wraps within configured range
always_comb begin
    next_write_addr = current_write_addr + (DATA_WIDTH == 64 ? 8 : 4);
    if (next_write_addr > cfg_limit_addr) begin
        next_write_addr = cfg_base_addr;
    end
end
```

### Master Write FSM

```systemverilog
typedef enum logic [2:0] {
    WRITE_IDLE       = 3'b000,
    WRITE_ADDR       = 3'b001,
    WRITE_DATA_LOW   = 3'b010,
    WRITE_DATA_HIGH  = 3'b011,  // For 32-bit data width only
    WRITE_RESP       = 3'b100
} write_state_t;
```

---

## Integration Example

```systemverilog
monbus_axil_group #(
    .FIFO_DEPTH_ERR     (64),
    .FIFO_DEPTH_WRITE   (32),
    .ADDR_WIDTH         (32),
    .DATA_WIDTH         (32),
    .NUM_PROTOCOLS      (3)
) u_monbus_axil_group (
    .axi_aclk           (clk),
    .axi_aresetn        (rst_n),

    // Monitor bus input
    .monbus_valid       (stream_mon_valid),
    .monbus_ready       (stream_mon_ready),
    .monbus_packet      (stream_mon_packet),

    // AXI-Lite slave read (for error FIFO access)
    .s_axil_arvalid     (axil_slave_arvalid),
    .s_axil_arready     (axil_slave_arready),
    // ... more slave signals

    // AXI-Lite master write (for logging)
    .m_axil_awvalid     (axil_master_awvalid),
    .m_axil_awready     (axil_master_awready),
    // ... more master signals

    // Interrupt
    .irq_out            (monbus_interrupt),

    // Configuration
    .cfg_base_addr      (cfg_monbus_base_addr),
    .cfg_limit_addr     (cfg_monbus_limit_addr),
    .cfg_axi_pkt_mask   (cfg_axi_pkt_mask),
    // ... more protocol configuration
);
```

---

## Common Issues

### Issue 1: Missing Monitor Packets

**Symptom:** Expected events not appearing in FIFO

**Root Causes:**
1. Packet type masked in cfg_*_pkt_mask
2. Event masked in cfg_*_*_mask
3. FIFO full (packets dropped)

**Solution:** Check mask configuration and FIFO status.

### Issue 2: Master Writes Stall

**Symptom:** Write FIFO fills up, backpressure to monitor bus

**Root Causes:**
1. AXI-Lite master target not responding
2. Address range exhausted (wrapping too fast)

**Solution:** Increase address range or reduce logging rate via masks.

---

## Related Documentation

- **Parent:** `01_stream_core.md` - Provides monitor bus packets
- **Packet Format:** Monitor Bus Protocol documentation
- **Configuration:** `14_apb_config.md` - Register mapping
---

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 0.90 | 2025-11-22 | seang | Initial block specification |
| 0.91 | 2026-01-02 | seang | Added table captions and figure numbers |

: MonBus AXI-Lite Group Revision History

---

**Last Updated:** 2026-01-02
