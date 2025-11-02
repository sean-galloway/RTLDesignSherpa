# apb_monitor

An Advanced Peripheral Bus (APB) transaction monitor that provides comprehensive error detection, performance tracking, and debug capabilities through a standardized monitor bus interface.

## Overview

The `apb_monitor` module monitors APB command/response interfaces to detect protocol violations, track performance metrics, and report events via the 64-bit monitor bus protocol. It attaches to APB master cmd/rsp interfaces (timing-convenient proxies for APB signals) and generates standardized event packets for error detection, latency analysis, and transaction debugging.

## Module Declaration

```systemverilog
module apb_monitor
    import monitor_pkg::*;
#(
    parameter int ADDR_WIDTH          = 32,
    parameter int DATA_WIDTH          = 32,
    parameter int UNIT_ID             = 1,     // 4-bit Unit ID
    parameter int AGENT_ID            = 10,    // 8-bit Agent ID
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
    input  logic                     cfg_throughput_enable,   // Enable throughput tracking

    // Configuration - Debug
    input  logic                     cfg_debug_enable,        // Enable debug packets
    input  logic                     cfg_trans_debug_enable,  // Enable transaction debug
    input  logic [3:0]               cfg_debug_level,         // Debug verbosity level

    // Configuration - Thresholds and Timeouts
    input  logic [15:0]              cfg_cmd_timeout_cnt,     // Command timeout (cycles)
    input  logic [15:0]              cfg_rsp_timeout_cnt,     // Response timeout (cycles)
    input  logic [31:0]              cfg_latency_threshold,   // Latency threshold (cycles)
    input  logic [15:0]              cfg_throughput_threshold, // Throughput threshold

    // Consolidated 64-bit event packet interface (monitor bus)
    output logic                     monbus_valid,            // Monitor bus valid
    input  logic                     monbus_ready,            // Monitor bus ready
    output logic [63:0]              monbus_packet,           // Consolidated monitor packet

    // Status outputs
    output logic [7:0]               active_count,            // Number of active transactions
    output logic [15:0]              error_count,             // Total error count
    output logic [31:0]              transaction_count        // Total transaction count
);
```

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| ADDR_WIDTH | int | 32 | APB address bus width |
| DATA_WIDTH | int | 32 | APB data bus width |
| UNIT_ID | int | 1 | 4-bit Unit identifier for monitor packets |
| AGENT_ID | int | 10 | 8-bit Agent identifier for monitor packets |
| MAX_TRANSACTIONS | int | 4 | Maximum concurrent transactions (APB typically 1-4) |
| MONITOR_FIFO_DEPTH | int | 8 | Internal FIFO depth for monitor packets |

## Ports

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
| cfg_throughput_enable | 1 | Input | Enable throughput tracking |

### Configuration - Debug

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| cfg_debug_enable | 1 | Input | Enable debug packet generation |
| cfg_trans_debug_enable | 1 | Input | Enable transaction-level debugging |
| cfg_debug_level | 4 | Input | Debug verbosity level (0-15) |

### Configuration - Thresholds

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| cfg_cmd_timeout_cnt | 16 | Input | Command timeout threshold (clock cycles) |
| cfg_rsp_timeout_cnt | 16 | Input | Response timeout threshold (clock cycles) |
| cfg_latency_threshold | 32 | Input | Latency threshold for alerts (clock cycles) |
| cfg_throughput_threshold | 16 | Input | Throughput threshold for alerts |

### Monitor Bus Interface

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| monbus_valid | 1 | Output | Monitor packet valid |
| monbus_ready | 1 | Input | Monitor packet ready (backpressure) |
| monbus_packet | 64 | Output | Consolidated 64-bit monitor packet |

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

The monitor generates standardized 64-bit packets for:

**Error Events** (when cfg_error_enable = 1):
- SLVERR responses (when cfg_slverr_enable = 1)
- Protocol violations (when cfg_protocol_enable = 1)
- Timeout conditions (when cfg_timeout_enable = 1)

**Performance Events** (when cfg_perf_enable = 1):
- Latency threshold violations
- Throughput degradation
- Transaction statistics

**Debug Events** (when cfg_debug_enable = 1):
- Transaction start/completion
- State transitions
- Internal status changes

### Monitor Packet Format

The 64-bit monitor bus packet follows the standard format:

```
[63:60] Packet Type  (0=ERROR, 1=COMPL, 2=TIMEOUT, 3=THRESH, 4=PERF, 5=DEBUG)
[59:57] Protocol     (1=APB)
[56:53] Event Code
[52:47] Channel ID
[46:43] Unit ID      (from UNIT_ID parameter)
[42:35] Agent ID     (from AGENT_ID parameter)
[34:0]  Event Data   (address, latency, error info, etc.)
```

## Configuration Strategies

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
.cfg_throughput_enable(1'b1),     // Track throughput
.cfg_latency_threshold(32'd100)   // Alert on >100 cycle latency
```

### Debug Mode

```systemverilog
.cfg_error_enable(1'b1),
.cfg_debug_enable(1'b1),          // Enable debug packets
.cfg_trans_debug_enable(1'b1),    // Transaction-level debug
.cfg_debug_level(4'd2),           // Medium verbosity
.cfg_perf_enable(1'b0)            // Reduce traffic
```

## Usage Example

```systemverilog
// APB Master with integrated monitor
apb_master #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32)
) u_apb_master (
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
    .rsp_valid(rsp_valid),
    .rsp_ready(rsp_ready),
    .rsp_prdata(rsp_prdata),
    .rsp_pslverr(rsp_pslverr)
);

// APB Monitor attached to cmd/rsp interfaces
apb_monitor #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32),
    .UNIT_ID(1),
    .AGENT_ID(10),
    .MAX_TRANSACTIONS(4)
) u_apb_monitor (
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
    // Monitor bus
    .monbus_valid(mon_valid),
    .monbus_ready(mon_ready),
    .monbus_packet(mon_packet),
    // Status
    .active_count(mon_active),
    .error_count(mon_errors),
    .transaction_count(mon_trans_cnt)
);

// Downstream FIFO for monitor packets
gaxi_fifo_sync #(
    .DATA_WIDTH(64),
    .DEPTH(128)
) u_mon_fifo (
    .i_clk(pclk),
    .i_rst_n(presetn),
    .i_valid(mon_valid),
    .i_data(mon_packet),
    .o_ready(mon_ready),
    // Connect to system monitor consumer
    .o_valid(sys_mon_valid),
    .o_data(sys_mon_data),
    .i_ready(sys_mon_ready)
);
```

## Design Notes

### Transaction Tracking

- APB is typically single-outstanding, so MAX_TRANSACTIONS=4 is usually sufficient
- Monitor tracks cmd→rsp matching to detect orphaned responses
- Separate timeout counters for command and response phases

### Packet Generation

- Internal FIFO buffers monitor packets (depth = MONITOR_FIFO_DEPTH)
- Backpressure on monbus_ready propagates to packet generation
- FIFO full condition prevents packet loss

### Performance Considerations

- Disable unused packet types to reduce traffic
- Performance mode (cfg_perf_enable) can generate high packet rates
- Debug mode should only be used for targeted debugging

## Related Modules

- `apb_master.sv` - APB master with cmd/rsp interfaces
- `apb_slave.sv` - APB slave with cmd/rsp interfaces
- `monitor_pkg.sv` - Monitor packet definitions and utilities
- `gaxi_fifo_sync.sv` - Recommended for monitor packet buffering

## References

- **Monitor Packet Specification**: [monitor_package_spec.md](../includes/monitor_package_spec.md)
- **APB Protocol**: AMBA APB Protocol Specification v2.0
- **Verification Guide**: See testbench in `val/amba/test_apb_monitor.py`

---

## Navigation

- **[← Back to APB Index](README.md)** (if exists, otherwise remove this line)
- **[← Back to RTLAmba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
