# MonBus AXIL Group Specification

**Module:** `monbus_axil_group.sv`
**Location:** `rtl/stream_macro/`
**Source:** Simplified from RAPIDS

---

## Overview

The MonBus AXIL Group provides monitoring and error reporting for STREAM. It receives monitor bus packets from STREAM channels and provides AXIL interfaces for error/interrupt handling and packet logging to memory.

### Key Features

- **Single MonBus input:** Simplified from RAPIDS (which has source + sink)
- **Error FIFO:** Buffers error packets for software polling
- **AXIL slave:** Read error/interrupt packets
- **AXIL master:** Write monitor packets to system memory
- **Interrupt output:** Asserted when error FIFO not empty
- **Protocol filtering:** Per-protocol packet type filtering (AXI, AXIS, CORE)

---

## Differences from RAPIDS

**CRITICAL DIFFERENCE:** STREAM has **ONE** monitor bus input (not two like RAPIDS)

**RAPIDS:**
- Source data path → source monitor bus
- Sink data path → sink monitor bus
- **TWO** inputs requiring arbitration

**STREAM:**
- Memory-to-memory only → single monitor bus
- **ONE** input, no arbitration needed
- Simpler, more efficient

**Other Changes:**
- Removed internal arbiter (not needed with single input)
- Direct connection from input to filter logic
- Reduced area and latency

---

## Interface

### Parameters

```systemverilog
parameter int FIFO_DEPTH_ERR    = 64;   // Error/interrupt FIFO depth
parameter int FIFO_DEPTH_WRITE  = 32;   // Master write FIFO depth
parameter int ADDR_WIDTH        = 32;   // AXI address width
parameter int DATA_WIDTH        = 32;   // AXI data width (32 or 64)
parameter int NUM_PROTOCOLS     = 3;    // Number of protocols (AXI, AXIS, CORE)
```

### Ports

**Clock and Reset:**
```systemverilog
input  logic                    axi_aclk;
input  logic                    axi_aresetn;
```

**Monitor Bus Input (single input):**
```systemverilog
input  logic                    monbus_valid;
output logic                    monbus_ready;
input  logic [63:0]             monbus_packet;
```

**AXIL Slave (Error/Interrupt FIFO Read):**
```systemverilog
// AR channel
input  logic [ADDR_WIDTH-1:0]   s_axil_araddr;
input  logic [2:0]              s_axil_arprot;
input  logic                    s_axil_arvalid;
output logic                    s_axil_arready;

// R channel
output logic [DATA_WIDTH-1:0]   s_axil_rdata;
output logic [1:0]              s_axil_rresp;
output logic                    s_axil_rvalid;
input  logic                    s_axil_rready;
```

**AXIL Master (Monitor Packet Writes to Memory):**
```systemverilog
// AW channel
output logic [ADDR_WIDTH-1:0]   m_axil_awaddr;
output logic [2:0]              m_axil_awprot;
output logic                    m_axil_awvalid;
input  logic                    m_axil_awready;

// W channel
output logic [DATA_WIDTH-1:0]   m_axil_wdata;
output logic [DATA_WIDTH/8-1:0] m_axil_wstrb;
output logic                    m_axil_wvalid;
input  logic                    m_axil_wready;

// B channel
input  logic [1:0]              m_axil_bresp;
input  logic                    m_axil_bvalid;
output logic                    m_axil_bready;
```

**Interrupt Output:**
```systemverilog
output logic                    irq_out;  // Asserted when error FIFO not empty
```

**Configuration Inputs:**
```systemverilog
input  logic [ADDR_WIDTH-1:0]   cfg_base_addr;   // Base address for master writes
input  logic [ADDR_WIDTH-1:0]   cfg_limit_addr;  // Limit address for master writes

// Per-protocol configuration (AXI, AXIS, CORE)
input  logic [15:0]             cfg_<proto>_pkt_mask;     // Drop mask
input  logic [15:0]             cfg_<proto>_err_select;   // Error FIFO select
input  logic [15:0]             cfg_<proto>_<type>_mask;  // Event-specific masks
```

---

## Operation

### Monitor Packet Flow (Simplified - No Arbitration)

```
MonBus Input -> Packet Classifier -> [Error FIFO | Write FIFO]
                                        |            |
                                  AXIL Slave   AXIL Master
                                  (CPU read)  (Memory write)
```

**STREAM Advantage:** Direct path from input to filter (no arbiter delay)

### Packet Classification

**Error Packets:**
- Packet type indicates error (descriptor error, AXI error, timeout, etc.)
- Routed to error FIFO
- Triggers interrupt if `cfg_error_irq_enable` asserted

**Normal Packets:**
- Completion, status, performance packets
- Routed to log FIFO (if `cfg_log_enable` asserted)
- Written to memory via AXIL master

### Error FIFO (AXIL Slave Interface)

**Software reads error packets:**

```c
// Software: Poll error FIFO
uint32_t error_pkt_low, error_pkt_high;

// Read lower 32 bits
error_pkt_low = read_axil(ERROR_FIFO_ADDR_LOW);

// Read upper 32 bits
error_pkt_high = read_axil(ERROR_FIFO_ADDR_HIGH);

// Combine into 64-bit packet
uint64_t error_packet = ((uint64_t)error_pkt_high << 32) | error_pkt_low;
```

**AXIL slave registers:**

| Address | Name | Access | Description |
|---------|------|--------|-------------|
| 0x00 | ERROR_PKT_LOW | RO | Error packet [31:0], auto-pop on read |
| 0x04 | ERROR_PKT_HIGH | RO | Error packet [63:32] |
| 0x08 | ERROR_FIFO_STATUS | RO | FIFO count, empty, full flags |
| 0x0C | IRQ_STATUS | RW1C | Interrupt status (write 1 to clear) |

### Log FIFO (AXIL Master Interface)

**Automatic packet logging:**

```systemverilog
// On normal monitor packet
if (monbus_valid && !is_error_packet) begin
    // Write to memory via AXIL master
    m_axil_awaddr <= cfg_log_base_addr + (log_wr_ptr << 3);
    m_axil_wdata <= monbus_packet[31:0];  // Lower word
    // ... followed by upper word write
    log_wr_ptr <= log_wr_ptr + 1;
end
```

**Memory layout:**

```
cfg_log_base_addr + 0x00: Packet 0 [31:0]
cfg_log_base_addr + 0x04: Packet 0 [63:32]
cfg_log_base_addr + 0x08: Packet 1 [31:0]
cfg_log_base_addr + 0x0C: Packet 1 [63:32]
...
```

### Interrupt Assertion

```systemverilog
// IRQ asserted when error FIFO not empty (if enabled)
assign irq_out = cfg_error_irq_enable && !error_fifo_empty;

// Software clears by reading error packets (drains FIFO)
// Or by writing to IRQ_STATUS register (W1C)
```

---

## MonBus Packet Format

**64-bit packet structure:**

```
[63:56] - Packet type (error, completion, status, etc.)
[55:48] - Channel ID
[47:40] - Reserved / packet-specific
[39:0]  - Packet-specific data
```

**Error packet types:**
- 0xE0: Descriptor error
- 0xE1: AXI read error
- 0xE2: AXI write error
- 0xE3: Timeout error

**Normal packet types:**
- 0x10: Descriptor fetched
- 0x20: Transfer complete
- 0x30: Performance metrics

---

## Usage in STREAM

### Integration Pattern

```systemverilog
monbus_axil_group #(
    .FIFO_DEPTH_ERR(64),
    .FIFO_DEPTH_WRITE(32),
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32),
    .NUM_PROTOCOLS(3)
) u_monbus (
    .axi_aclk(aclk),
    .axi_aresetn(aresetn),

    // Single monitor bus input (from STREAM channel arbiter)
    .monbus_valid(stream_mon_valid),
    .monbus_ready(stream_mon_ready),
    .monbus_packet(stream_mon_packet),

    // AXIL slave (CPU access to error FIFO)
    .s_axil_araddr(cpu_araddr),
    .s_axil_arprot(3'b000),
    .s_axil_arvalid(cpu_arvalid),
    .s_axil_arready(cpu_arready),
    .s_axil_rdata(cpu_rdata),
    .s_axil_rresp(cpu_rresp),
    .s_axil_rvalid(cpu_rvalid),
    .s_axil_rready(cpu_rready),

    // AXIL master (log to memory)
    .m_axil_awaddr(log_awaddr),
    .m_axil_awprot(log_awprot),
    .m_axil_awvalid(log_awvalid),
    .m_axil_awready(log_awready),
    .m_axil_wdata(log_wdata),
    .m_axil_wstrb(log_wstrb),
    .m_axil_wvalid(log_wvalid),
    .m_axil_wready(log_wready),
    .m_axil_bresp(log_bresp),
    .m_axil_bvalid(log_bvalid),
    .m_axil_bready(log_bready),

    // Interrupt
    .irq_out(stream_irq),

    // Configuration
    .cfg_base_addr(32'h8000_0000),
    .cfg_limit_addr(32'h8FFF_FFFF),
    .cfg_axi_pkt_mask(16'h0000),
    .cfg_axi_err_select(16'h0001),  // Route errors to error FIFO
    // ... other protocol configurations
);
```

---

## Error Handling Flow

**Example: AXI Read Error**

```
1. AXI Read Engine detects RRESP != OKAY
2. Engine generates MonBus error packet (type=0xE1, ch_id, error details)
3. Packet routed to error FIFO in monbus_axil_group
4. IRQ asserted (irq_out = 1)
5. Software ISR reads ERROR_PKT_LOW/HIGH via AXIL slave
6. Software logs error, takes recovery action
7. Error FIFO drains, IRQ deasserts
```

---

## Testing

**Test Location:** `projects/components/stream/dv/tests/integration_tests/`

**Test Scenarios:**
1. Normal packet logging to memory
2. Error packet routing to error FIFO
3. Interrupt assertion/deassertion
4. AXIL slave reads (error FIFO)
5. AXIL master writes (memory logging)
6. Multi-channel packet arbitration

**Reference:** RAPIDS monbus_axil_group tests can be reused directly.

---

## Performance

**Throughput:** 1 packet per cycle (per channel)

**Latency:**
- Error FIFO: 2 cycles (write to AXIL readable)
- Memory logging: 4-6 cycles (AXIL master write latency)

**Area:** ~1000 LUTs + 64 64-bit FIFO

---

## Related Documentation

- **RAPIDS Spec:** `projects/components/rapids/docs/rapids_spec/ch02_blocks/04_monbus_axil_group.md` (if available)
- **MonBus Protocol:** `rtl/amba/includes/monitor_pkg.sv`
- **Source:** `rtl/stream_macro/monbus_axil_group.sv`

---

**Last Updated:** 2025-10-17
