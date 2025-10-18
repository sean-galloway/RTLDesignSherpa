# MonBus AXIL Group Specification

**Module:** `monbus_axil_group.sv`
**Location:** `rtl/stream_macro/`
**Source:** Copied from RAPIDS (identical)

---

## Overview

The MonBus AXIL Group provides monitoring and error reporting for STREAM. It aggregates monitor bus packets from all channels and provides AXIL interfaces for error/interrupt handling and packet logging to memory.

### Key Features

- **Multiple MonBus inputs:** One per STREAM channel
- **Error FIFO:** Buffers error packets for software polling
- **AXIL slave:** Read error/interrupt packets
- **AXIL master:** Write monitor packets to system memory
- **Interrupt output:** Asserted when error FIFO not empty
- **Identical to RAPIDS:** Proven design, no modifications

---

## Differences from RAPIDS

**None.** This module is functionally identical to RAPIDS `monbus_axil_group.sv`.

**Only Change:**
- Header comment updated to mention STREAM
- Functionally unchanged

**Why Identical:**
- MonBus protocol standardized across all projects
- Error/interrupt handling proven in RAPIDS
- AXIL interface patterns reused

---

## Interface

### Parameters

```systemverilog
parameter int NUM_CHANNELS = 8;         // Number of monitor bus inputs
parameter int MONBUS_WIDTH = 64;        // Monitor bus packet width
parameter int AXIL_ADDR_WIDTH = 32;     // AXIL address width
parameter int AXIL_DATA_WIDTH = 32;     // AXIL data width
parameter int ERROR_FIFO_DEPTH = 64;    // Error packet FIFO depth
```

### Ports

**Clock and Reset:**
```systemverilog
input  logic                        aclk;
input  logic                        aresetn;
```

**Monitor Bus Inputs (per channel):**
```systemverilog
input  logic [NUM_CHANNELS-1:0]     ch_monbus_valid;
output logic [NUM_CHANNELS-1:0]     ch_monbus_ready;
input  logic [NUM_CHANNELS-1:0][MONBUS_WIDTH-1:0]
                                    ch_monbus_packet;
```

**AXIL Slave (Error/Interrupt FIFO Read):**
```systemverilog
// AR channel
input  logic [AXIL_ADDR_WIDTH-1:0]  s_axil_araddr;
input  logic                        s_axil_arvalid;
output logic                        s_axil_arready;

// R channel
output logic [AXIL_DATA_WIDTH-1:0]  s_axil_rdata;
output logic [1:0]                  s_axil_rresp;
output logic                        s_axil_rvalid;
input  logic                        s_axil_rready;
```

**AXIL Master (Monitor Packet Writes to Memory):**
```systemverilog
// AW channel
output logic [AXIL_ADDR_WIDTH-1:0]  m_axil_awaddr;
output logic                        m_axil_awvalid;
input  logic                        m_axil_awready;

// W channel
output logic [AXIL_DATA_WIDTH-1:0]  m_axil_wdata;
output logic [3:0]                  m_axil_wstrb;
output logic                        m_axil_wvalid;
input  logic                        m_axil_wready;

// B channel
input  logic [1:0]                  m_axil_bresp;
input  logic                        m_axil_bvalid;
output logic                        m_axil_bready;
```

**Interrupt Output:**
```systemverilog
output logic                        irq_out;
```

**Configuration:**
```systemverilog
input  logic [AXIL_ADDR_WIDTH-1:0]  cfg_log_base_addr;    // Base addr for logging
input  logic                        cfg_log_enable;       // Enable memory logging
input  logic                        cfg_error_irq_enable; // Enable error interrupts
```

---

## Operation

### Monitor Packet Flow

```
Channel MonBus -> Packet Classifier -> [Error FIFO | Log FIFO]
                                          |            |
                                    AXIL Slave   AXIL Master
                                    (CPU read)  (Memory write)
```

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
    .NUM_CHANNELS(8)
) u_monbus (
    .aclk(aclk),
    .aresetn(aresetn),

    // MonBus inputs from channels
    .ch_monbus_valid({ch7_mon_valid, ..., ch0_mon_valid}),
    .ch_monbus_ready({ch7_mon_ready, ..., ch0_mon_ready}),
    .ch_monbus_packet({ch7_mon_pkt, ..., ch0_mon_pkt}),

    // AXIL slave (CPU access to error FIFO)
    .s_axil_araddr(cpu_araddr),
    .s_axil_arvalid(cpu_arvalid),
    // ... AXIL slave signals

    // AXIL master (log to memory)
    .m_axil_awaddr(log_awaddr),
    .m_axil_awvalid(log_awvalid),
    // ... AXIL master signals

    // Interrupt
    .irq_out(stream_irq),

    // Configuration
    .cfg_log_base_addr(32'h8000_0000),
    .cfg_log_enable(1'b1),
    .cfg_error_irq_enable(1'b1)
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
