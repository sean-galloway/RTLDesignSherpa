# Descriptor Engine Specification

**Module:** `descriptor_engine.sv`
**Location:** `projects/components/stream/rtl/stream_fub/`
**Source:** Simplified from RAPIDS

---

## Overview

The Descriptor Engine fetches descriptors from system memory via AXI and parses them into structured fields for the Scheduler. This module is **simplified from RAPIDS** with a smaller descriptor format (256-bit vs 512-bit).

### Key Features

- AXI master for descriptor fetch (256-bit read interface)
- Descriptor FIFO buffering (depth configurable)
- Parsing of 256-bit descriptor format
- Handshake interface to Scheduler
- Error detection and reporting

---

## Interface

### Parameters

```systemverilog
parameter int ADDR_WIDTH = 64;        // Address bus width
parameter int DATA_WIDTH = 256;       // Descriptor width
parameter int AXI_ID_WIDTH = 8;       // AXI ID width
parameter int FIFO_DEPTH = 16;        // Descriptor FIFO depth
```

### Ports

**Clock and Reset:**
```systemverilog
input  logic                    aclk;
input  logic                    aresetn;
```

**Descriptor Request (from Scheduler):**
```systemverilog
input  logic                    desc_req_valid;
output logic                    desc_req_ready;
input  logic [ADDR_WIDTH-1:0]   desc_req_addr;
input  logic [3:0]              desc_req_channel_id;  // Channel ID for AXI ID
```

**Descriptor Output (to Scheduler):**
```systemverilog
output logic                    desc_valid;
input  logic                    desc_ready;
output descriptor_t             desc_packet;
```

**AXI Master (Descriptor Fetch):**
```systemverilog
// AXI AR (Address Read) Channel
output logic [ADDR_WIDTH-1:0]   m_axi_araddr;
output logic [7:0]              m_axi_arlen;
output logic [2:0]              m_axi_arsize;
output logic [1:0]              m_axi_arburst;
output logic [AXI_ID_WIDTH-1:0] m_axi_arid;       // Transaction ID
output logic                    m_axi_arvalid;
input  logic                    m_axi_arready;

// AXI R (Read Data) Channel
input  logic [AXI_ID_WIDTH-1:0] m_axi_rid;        // Transaction ID
input  logic [DATA_WIDTH-1:0]   m_axi_rdata;
input  logic [1:0]              m_axi_rresp;
input  logic                    m_axi_rlast;
input  logic                    m_axi_rvalid;
output logic                    m_axi_rready;
```

**Critical AXI ID Requirement:**

The lower bits of `m_axi_arid` **MUST** contain the channel ID from the arbiter:

```systemverilog
// Lower bits = channel ID (from arbiter grant)
// Upper bits = transaction counter (for multiple outstanding)
assign m_axi_arid = {transaction_counter, desc_req_channel_id[3:0]};
```

**Rationale:**
- Allows responses to be routed back to correct channel
- Enables MonBus packet generation with channel ID
- Critical for debugging and transaction tracking
- Channel ID comes from arbiter (whichever scheduler won arbitration for descriptor fetch)

**MonBus Output:**
```systemverilog
output logic                    monbus_valid;
input  logic                    monbus_ready;
output logic [63:0]             monbus_packet;
```

---

## Descriptor Format

See `projects/components/stream/rtl/includes/stream_pkg.sv` for complete `descriptor_t` definition.

**256-bit structure:**
- `[63:0]` src_addr - Source address
- `[127:64]` dst_addr - Destination address
- `[159:128]` length - Transfer length in BEATS
- `[191:160]` next_descriptor_ptr - Next descriptor address
- `[192]` valid - Valid flag
- `[193]` interrupt - Interrupt enable
- `[194]` last - Last descriptor flag
- `[199:196]` channel_id - Channel ID
- `[207:200]` priority - Transfer priority

---

## Operation

### Fetch Sequence

1. **Request:** Scheduler asserts `desc_req_valid` with `desc_req_addr`
2. **AXI Read:** Engine issues AXI AR transaction for descriptor
3. **Receive:** AXI R channel delivers 256-bit descriptor
4. **Parse:** Descriptor fields extracted into `descriptor_t` structure
5. **Buffer:** Descriptor stored in FIFO
6. **Handoff:** Descriptor presented to Scheduler via `desc_valid`/`desc_ready`

### Error Handling

- **AXI Error:** RRESP != OKAY -> MonBus error packet
- **Invalid Descriptor:** valid flag = 0 -> MonBus error packet
- **FIFO Overflow:** Request rejected if FIFO full

---

## Differences from RAPIDS

**Descriptor Size:**
- **RAPIDS:** 512-bit descriptor (8 x 64-bit words)
- **STREAM:** 256-bit descriptor (4 x 64-bit words) - **Half the size!**

**Key Simplifications:**
1. **Smaller descriptor:** 256 bits vs 512 bits
2. **Simpler fields:** No alignment metadata, no chunk information
3. **Length in beats:** Not chunks (4-byte units)
4. **No circular buffers:** Explicit chain termination only

**Import Change:**
```systemverilog
// RAPIDS:
`include "rapids_imports.svh"

// STREAM:
`include "stream_imports.svh"
```

**Why Half Size:**
- RAPIDS handles complex alignment (requires extra metadata)
- RAPIDS uses chunk-based length (4-byte units)
- STREAM requires aligned addresses (no fixup metadata needed)
- STREAM uses beat-based length (simpler, no conversion needed)

---

## Testing

**Test Location:** `projects/components/stream/dv/tests/fub_tests/descriptor_engine/`

**Test Scenarios:**
1. Single descriptor fetch
2. Back-to-back fetches
3. FIFO full backpressure
4. AXI error response
5. Invalid descriptor handling

**Reference:** RAPIDS descriptor_engine tests can be reused with minimal adaptation.

---

## Related Documentation

- **RAPIDS Spec:** `projects/components/rapids/docs/rapids_spec/ch02_blocks/01_02_descriptor_engine.md`
- **Package:** `projects/components/stream/rtl/includes/stream_pkg.sv` - Descriptor format
- **Source:** `projects/components/stream/rtl/stream_fub/descriptor_engine.sv`

---

**Last Updated:** 2025-10-17
