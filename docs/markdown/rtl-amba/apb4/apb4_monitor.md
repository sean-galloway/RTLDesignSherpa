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

# apb4_monitor

## Overview

The `apb4_monitor` is an APB transaction monitor with comprehensive error detection, performance tracking, and debug capabilities, all reported through a standardized monitor bus interface. It attaches to APB master cmd/rsp interfaces (timing-convenient proxies for APB signals) and generates standardized event packets — 128-bit monitor bus protocol, paired with a 64-bit side-band timestamp — for error detection, latency analysis, and transaction debugging.

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| ADDR_WIDTH | int | 32 | APB address bus width |
| DATA_WIDTH | int | 32 | APB data bus width |
| UNIT_ID | logic [7:0] | 8'h01 | 8-bit Unit identifier for monitor packets |
| AGENT_ID | logic [15:0] | 16'h000A | 16-bit Agent identifier for monitor packets |
| MAX_TRANSACTIONS | int | 4 | Maximum concurrent transactions (APB typically 1-4) |
| N_ADDR_RANGES | int | 0 | Address-range checker ranges; 0 disables the checker |
| MONITOR_FIFO_DEPTH | int | 8 | Internal FIFO depth for monitor packets |
| USE_MONITOR | bit | 1 | Synthesis-time monitor enable. 0 = omit monitor and tie outputs to safe non-blocking defaults; 1 = full monitor functionality. |

## Ports

```systemverilog
module apb4_monitor
    import monitor_common_pkg::*;  // PROTOCOL_APB, PktType*, transaction states
    import monitor_amba4_pkg::*;   // APB_ERR_*, APB_TIMEOUT_*, etc.
    // (`import monitor_pkg::*;` is intentionally omitted -- its helpers
    // duplicate monitor_common_pkg's and Vivado flags the wildcard overlap)
#(
    parameter bit USE_MONITOR         = 1'b1,  // 0 = omit monitor body, tie outputs
    parameter int N_ADDR_RANGES       = 0,     // 0 = address-range checker disabled
    parameter int ADDR_WIDTH          = 32,
    parameter int DATA_WIDTH          = 32,
    parameter logic [7:0]  UNIT_ID    = 8'h01,     // 8-bit Unit ID
    parameter logic [15:0] AGENT_ID   = 16'h000A,  // 16-bit Agent ID
    parameter int MAX_TRANSACTIONS    = 4,     // APB is typically single outstanding
    parameter int MONITOR_FIFO_DEPTH  = 8,     // Monitor packet FIFO depth

    // Short params
    parameter int AW                  = ADDR_WIDTH,
    parameter int DW                  = DATA_WIDTH,
    parameter int SW                  = DW/8
)
(
    // Clock and Reset (aclk domain - matches cmd/rsp interfaces)
    input  logic                     aclk,
    input  logic                     aresetn,

    // Command Interface Monitoring (aclk domain)
    input  logic                     cmd_valid,
    input  logic                     cmd_ready,
    input  logic                     cmd_pwrite,
    input  logic [AW-1:0]            cmd_paddr,
    input  logic [DW-1:0]            cmd_pwdata,
    input  logic [SW-1:0]            cmd_pstrb,
    input  logic [2:0]               cmd_pprot,

    // Response Interface Monitoring (aclk domain)
    input  logic                     rsp_valid,
    input  logic                     rsp_ready,
    input  logic [DW-1:0]            rsp_prdata,
    input  logic                     rsp_pslverr,

    // Configuration - Error Detection
    input  logic                     cfg_error_enable,        // Enable error event packets
    input  logic                     cfg_timeout_enable,      // Enable timeout event packets
    input  logic                     cfg_protocol_enable,     // Enable protocol violation detection
    input  logic                     cfg_slverr_enable,       // Enable slave error detection

    // Configuration - Performance Monitoring
    input  logic                     cfg_perf_enable,         // Enable performance packets
    input  logic                     cfg_latency_enable,      // Enable latency tracking
    input  logic                     cfg_throughput_enable,   // ACCEPTED BUT UNIMPLEMENTED -- no throughput event exists (see Design Notes)

    // Configuration - Debug
    input  logic                     cfg_debug_enable,        // Enable debug packets
    input  logic                     cfg_trans_debug_enable,  // Enable transaction debug
    input  logic [3:0]               cfg_debug_level,         // ACCEPTED BUT UNIMPLEMENTED -- never referenced in the body

    // Configuration - Thresholds and Timeouts
    input  logic [15:0]              cfg_cmd_timeout_cnt,     // Command timeout (cycles)
    input  logic [15:0]              cfg_rsp_timeout_cnt,     // Response timeout (cycles)
    input  logic [31:0]              cfg_latency_threshold,   // Latency threshold (cycles)
    input  logic [15:0]              cfg_throughput_threshold, // ACCEPTED BUT UNIMPLEMENTED

    // Address-range checker (elaborated when N_ADDR_RANGES > 0)
    input  logic                                                       cfg_addr_check_enable,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0]         cfg_addr_range_enable,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0][AW-1:0] cfg_addr_range_low,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0][AW-1:0] cfg_addr_range_high,

    // Consolidated 128-bit event packet interface (monitor bus) + 64-bit side-band timestamp
    output logic                     monbus_valid,            // Monitor bus valid
    input  logic                     monbus_ready,            // Monitor bus ready
    output logic [127:0]             monbus_packet,           // Consolidated monitor packet (monitor_packet_t)
    output logic [63:0]              monbus_timestamp,        // Side-band timestamp (monbus_timestamp_t)
    input  logic [63:0]              i_mon_time,              // Free-running counter from monbus_group_core

    // Status outputs
    output logic [7:0]               active_count,            // Number of active transactions
    output logic [15:0]              error_count,             // Total error count
    output logic [31:0]              transaction_count        // Total transaction count
);
```

### Clock and Reset

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| aclk | 1 | Input | Monitor clock (matches cmd/rsp domain) |
| aresetn | 1 | Input | Active-low asynchronous reset |

### Command Interface Monitoring

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| cmd_valid | 1 | Input | Command valid signal |
| cmd_ready | 1 | Input | Command ready signal |
| cmd_pwrite | 1 | Input | Write/read indicator (1=write, 0=read) |
| cmd_paddr | AW | Input | Command address |
| cmd_pwdata | DW | Input | Write data |
| cmd_pstrb | SW | Input | Write strobe |
| cmd_pprot | 3 | Input | Protection attributes |

### Response Interface Monitoring

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| rsp_valid | 1 | Input | Response valid signal |
| rsp_ready | 1 | Input | Response ready signal |
| rsp_prdata | DW | Input | Read data |
| rsp_pslverr | 1 | Input | Slave error indicator |

### Configuration - Error Detection

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| cfg_error_enable | 1 | Input | Enable error event packet generation |
| cfg_timeout_enable | 1 | Input | Enable timeout detection |
| cfg_protocol_enable | 1 | Input | Enable protocol violation detection |
| cfg_slverr_enable | 1 | Input | Enable slave error reporting |

### Configuration - Performance Monitoring

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| cfg_perf_enable | 1 | Input | Enable performance packet generation |
| cfg_latency_enable | 1 | Input | Enable latency measurement |
| cfg_throughput_enable | 1 | Input | ACCEPTED BUT UNIMPLEMENTED: never referenced in the module body; no throughput event exists |

### Configuration - Debug

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| cfg_debug_enable | 1 | Input | Enable debug packet generation |
| cfg_trans_debug_enable | 1 | Input | Enable transaction-level debugging |
| cfg_debug_level | 4 | Input | ACCEPTED BUT UNIMPLEMENTED: never referenced in the module body |

### Configuration - Thresholds

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| cfg_cmd_timeout_cnt | 16 | Input | Command timeout threshold (clock cycles) |
| cfg_rsp_timeout_cnt | 16 | Input | Response timeout threshold (clock cycles) |
| cfg_latency_threshold | 32 | Input | Latency threshold for alerts (clock cycles) |
| cfg_throughput_threshold | 16 | Input | ACCEPTED BUT UNIMPLEMENTED: never referenced in the module body |
| cfg_addr_check_enable | 1 | Input | Enable the address-range checker (needs N_ADDR_RANGES > 0) |
| cfg_addr_range_enable | N_ADDR_RANGES | Input | Per-range enable |
| cfg_addr_range_low | N_ADDR_RANGES x AW | Input | Per-range low bound |
| cfg_addr_range_high | N_ADDR_RANGES x AW | Input | Per-range high bound |

### Monitor Bus Interface

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| monbus_valid | 1 | Output | Monitor packet valid |
| monbus_ready | 1 | Input | Monitor packet ready (backpressure) |
| monbus_packet | 128 | Output | Consolidated `monitor_packet_t` (see format below) |
| monbus_timestamp | 64 | Output | `monbus_timestamp_t` paired atomically with `monbus_packet` |
| i_mon_time | 64 | Input | Free-running counter from `monbus_group_core`, sampled at packet emission |

### Status Outputs

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| active_count | 8 | Output | Number of currently active transactions |
| error_count | 16 | Output | Cumulative error count |
| transaction_count | 32 | Output | Total transaction count |

## Functional Description

### Transaction Monitoring

The APB monitor tracks transactions through the command/response pipeline:

1. **Command Phase**: Monitors cmd_valid/cmd_ready handshake
   - Captures address, write/read type, data, strobe
   - Starts latency counter
   - Detects protocol violations

2. **Response Phase**: Monitors rsp_valid/rsp_ready handshake
   - Captures response data and error status
   - Calculates transaction latency
   - Matches response to command

### Event Detection

The monitor generates standardized 128-bit packets (paired with 64-bit side-band timestamps) for:

**Error Events** (when cfg_error_enable = 1):
- SLVERR responses (when cfg_slverr_enable = 1)
- Protocol violations (when cfg_protocol_enable = 1)
- Timeout conditions (when cfg_timeout_enable = 1)

**Performance Events** (when cfg_perf_enable = 1):
- Latency threshold violations (`cfg_latency_threshold` compare — the only
  perf event the RTL generates)

**Debug Events** (when cfg_debug_enable = 1):
- Transaction start/completion
- State transitions
- Internal status changes

### Monitor Packet Format

The 128-bit `monbus_packet` (paired with the 64-bit `monbus_timestamp` side-band signal) follows the standardized APB monitor bus format. The layout is identical across protocols:

```
Bits [127:124] - Packet Type:
  0x0 = ERROR      Error events (SLVERR, protocol violations)
  0x1 = COMPL      Completion events (transaction finished). NOTE: completion
                   packets are UNGATED -- one monbus packet per successful
                   transaction in EVERY configuration; there is no
                   cfg_compl_enable on this monitor. Budget the consumer for it.
  0x2 = THRESH     Threshold events
  0x3 = TIMEOUT    Timeout events
  0x4 = PERF       Performance metrics
  0x8 = ADDR_MATCH Address match events
  0x9 = APB        APB-specific events
  0xF = DEBUG      Debug events
Bits [123:109] - Reserved (15 bits, forward-compat slack)
Bits [108:105] - Protocol (4 bits): 0x0=AXI, 0x1=AXIS, 0x2=APB, 0x3=ARB, 0x4=CORE
Bits [104:97]  - Event Code (8 bits, protocol-specific)
Bits [96:88]   - Channel ID (9 bits)
Bits [87:72]   - Agent ID (16 bits, from AGENT_ID parameter)
Bits [71:64]   - Unit ID (8 bits, from UNIT_ID parameter)
Bits [63:0]    - Event Data (64 bits — full address, latency, etc.)
```

## Usage Example

### Functional Verification (Recommended)

```systemverilog
.cfg_error_enable(1'b1),          // Catch all errors
.cfg_timeout_enable(1'b1),        // Detect hangs
.cfg_protocol_enable(1'b1),       // Catch violations
.cfg_slverr_enable(1'b1),         // Report slave errors
.cfg_perf_enable(1'b0),           // Disable (reduces packet traffic)
.cfg_debug_enable(1'b0),          // Only if deep debugging needed
.cfg_cmd_timeout_cnt(16'd1000),   // 1000 cycle timeout
.cfg_rsp_timeout_cnt(16'd1000)
```

### Performance Analysis

```systemverilog
.cfg_error_enable(1'b1),          // Still catch errors
.cfg_timeout_enable(1'b0),        // Disable
.cfg_protocol_enable(1'b0),       // Disable
.cfg_slverr_enable(1'b1),         // Keep error reporting
.cfg_perf_enable(1'b1),           // Enable performance tracking
.cfg_latency_enable(1'b1),        // Track latencies
.cfg_throughput_enable(1'b0),     // unimplemented -- tie low
.cfg_latency_threshold(32'd100)   // Alert on >100 cycle latency
```

### Debug Mode

```systemverilog
.cfg_error_enable(1'b1),
.cfg_debug_enable(1'b1),          // Enable debug packets
.cfg_trans_debug_enable(1'b1),    // Transaction-level debug
.cfg_debug_level(4'd0),           // unimplemented -- tie low
.cfg_perf_enable(1'b0)            // Reduce traffic
```

### Full Integration

```systemverilog
// APB Master with integrated monitor
apb4_master #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32)
) u_apb4_master (
    .pclk(pclk),
    .presetn(presetn),
    // APB master interface
    .m_apb_PSEL(apb_psel),
    .m_apb_PENABLE(apb_penable),
    .m_apb_PADDR(apb_paddr),
    .m_apb_PWRITE(apb_pwrite),
    .m_apb_PWDATA(apb_pwdata),
    .m_apb_PREADY(apb_pready),
    .m_apb_PRDATA(apb_prdata),
    .m_apb_PSLVERR(apb_pslverr),
    // Command/Response interfaces
    .cmd_valid(cmd_valid),
    .cmd_ready(cmd_ready),
    .cmd_pwrite(cmd_pwrite),
    .cmd_paddr(cmd_paddr),
    .cmd_pwdata(cmd_pwdata),
    .cmd_pstrb(cmd_pstrb),     // floating these drives Z into the command FIFO
    .cmd_pprot(cmd_pprot),
    .rsp_valid(rsp_valid),
    .rsp_ready(rsp_ready),
    .rsp_prdata(rsp_prdata),
    .rsp_pslverr(rsp_pslverr)
);

// APB Monitor attached to cmd/rsp interfaces
apb4_monitor #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32),
    .UNIT_ID(1),
    .AGENT_ID(10),
    .MAX_TRANSACTIONS(4)
) u_apb4_monitor (
    .aclk(pclk),
    .aresetn(presetn),
    // Monitor cmd/rsp interfaces
    .cmd_valid(cmd_valid),
    .cmd_ready(cmd_ready),
    .cmd_pwrite(cmd_pwrite),
    .cmd_paddr(cmd_paddr),
    .cmd_pwdata(cmd_pwdata),
    .cmd_pstrb(cmd_pstrb),
    .cmd_pprot(cmd_pprot),
    .rsp_valid(rsp_valid),
    .rsp_ready(rsp_ready),
    .rsp_prdata(rsp_prdata),
    .rsp_pslverr(rsp_pslverr),
    // Configuration
    .cfg_error_enable(1'b1),
    .cfg_timeout_enable(1'b1),
    .cfg_protocol_enable(1'b1),
    .cfg_slverr_enable(1'b1),
    .cfg_perf_enable(1'b0),
    .cfg_debug_enable(1'b0),
    .cfg_cmd_timeout_cnt(16'd1000),
    .cfg_rsp_timeout_cnt(16'd1000),
    // Free-running time input -- leaving it unconnected floats the timestamp
    .i_mon_time(mon_time),
    // Monitor bus (128-bit packet + 64-bit side-band timestamp)
    .monbus_valid(mon_valid),
    .monbus_ready(mon_ready),
    .monbus_packet(mon_packet),
    .monbus_timestamp(mon_timestamp),
    // Status
    .active_count(mon_active),
    .error_count(mon_errors),
    .transaction_count(mon_trans_cnt)
);

// Downstream FIFO for monitor packets
gaxi_fifo_sync #(
    .DATA_WIDTH(128),   // FULL packet width -- 64 would truncate the entire
                        // header half (type, protocol, event code, IDs)
    .DEPTH(128)
) u_mon_fifo (
    .axi_aclk(pclk),
    .axi_aresetn(presetn),
    .wr_valid(mon_valid),
    .wr_data(mon_packet),
    .wr_ready(mon_ready),
    // Connect to system monitor consumer
    .rd_valid(sys_mon_valid),
    .rd_data(sys_mon_data),
    .rd_ready(sys_mon_ready)
);
```

## Design Notes

### Transaction Tracking

- APB is typically single-outstanding, so MAX_TRANSACTIONS=4 is usually sufficient
- Monitor tracks cmd→rsp matching to detect orphaned responses
- Separate timeout counters for command and response phases

### Packet Generation

- Internal FIFO buffers monitor packets (depth = MONITOR_FIFO_DEPTH)
- Backpressure on `monbus_ready` stops at the internal FIFO: packet
  generation fires purely from event conditions and does NOT consult the
  FIFO's ready — a full FIFO silently DROPS the packet (lossy-but-honest;
  size MONITOR_FIFO_DEPTH and drain promptly if you need every event)
- The slot is freed either way: terminal transaction-table entries retire
  unconditionally, packet delivered or not (the historical
  leak-until-wedged behavior was TASK-066, fixed and witnessed by
  `apb4_monitor_slot_retire_test`)

### Performance Considerations

- Disable unused packet types to reduce traffic
- Performance mode (cfg_perf_enable) can generate high packet rates
- Debug mode should only be used for targeted debugging

## Related Modules

- `apb4_master.sv` - APB master with cmd/rsp interfaces
- `apb4_slave.sv` - APB slave with cmd/rsp interfaces
- `monitor_common_pkg.sv` / `monitor_amba4_pkg.sv` - Monitor packet definitions and APB event codes
- `gaxi_fifo_sync.sv` - Recommended for monitor packet buffering

## References

- **Monitor Packet Specification**: [monitor_package_spec.md](../includes/monitor_package_spec.md)
- **APB Protocol**: AMBA APB Protocol Specification v2.0
- **Verification Guide**: See testbench in `val/amba/test_apb4_monitor.py`

---

## Navigation

- **[← Back to APB4 Book](README.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
