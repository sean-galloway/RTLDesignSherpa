# AXI4-Stream (AXIS4) Interface Specification and Assumptions

## Overview

This document defines the formal specification and assumptions for AXI4-Stream (AXIS4) interface implementations used in the RAPIDS system. AXIS4 provides high-bandwidth, unidirectional streaming data transfer with built-in flow control and packet framing capabilities.

## Interface Summary

### Number of Interfaces

- **2 Master (Transmit) Interfaces**: Source data path and network master output
- **2 Slave (Receive) Interfaces**: Sink data path and network slave input

### Interface Parameters

| Parameter | Description | Valid Values | Default |
|-----------|-------------|--------------|---------|
| `TDATA_WIDTH` | Stream data bus width in bits | 32, 64, 128, 256, 512, 1024 | 512 |
| `TID_WIDTH` | Stream ID width in bits (optional) | 0-8 | 0 |
| `TDEST_WIDTH` | Stream destination width in bits (optional) | 0-8 | 0 |
| `TUSER_WIDTH` | User-defined sideband width in bits (optional) | 0-128 | 0 |
| `TKEEP_ENABLE` | Enable TKEEP byte qualifier signals | 0, 1 | 1 |
| `TSTRB_ENABLE` | Enable TSTRB byte strobe signals | 0, 1 | 0 |

### Interface Configuration Summary

| Interface Type | Direction | TDATA Width | TID | TDEST | TUSER | TKEEP | Purpose |
|----------------|-----------|-------------|-----|-------|-------|-------|---------|
| **Network Master (TX)** | Output | 512 bits | No | Optional | Optional | Yes | Transmit packets to network |
| **Network Slave (RX)** | Input | 512 bits | No | Optional | Optional | Yes | Receive packets from network |
| **Source Data Stream** | Output | 512 bits | No | No | Optional | Yes | Memory-to-network streaming |
| **Sink Data Stream** | Input | 512 bits | No | No | Optional | Yes | Network-to-memory streaming |

---

## Core Protocol Assumptions

### AXI4-Stream Fundamentals

| Aspect | Requirement |
|--------|-------------|
| **Transfer Protocol** | Valid-ready handshake on every transfer |
| **Data Flow** | Unidirectional streaming (master -> slave) |
| **Packet Framing** | TLAST signal indicates packet boundaries |
| **Flow Control** | Backpressure via TREADY signal |
| **Byte Granularity** | TKEEP indicates valid bytes within transfer |

### Implementation Assumptions

#### Assumption 1: TKEEP-Based Byte Qualification

| Aspect | Requirement |
|--------|-------------|
| **Byte Validity Rule** | TKEEP indicates which bytes of TDATA contain valid data |
| **512-bit bus (64 bytes)** | TKEEP[63:0] - one bit per byte |
| **Contiguous Bytes** | Valid bytes are always contiguous (no gaps) |
| **Alignment** | Valid bytes always start from TDATA[7:0] (byte 0) |
| **Rationale** | Simplifies data alignment and reduces complexity |
| **Benefit** | Eliminates data steering logic for non-contiguous bytes |

**TKEEP Encoding Examples (64-byte bus):**

| Transfer Size | TKEEP Value | Description |
|---------------|-------------|-------------|
| **64 bytes** | 64'hFFFFFFFFFFFFFFFF | All bytes valid (full transfer) |
| **32 bytes** | 64'h00000000FFFFFFFF | First 32 bytes valid |
| **16 bytes** | 64'h000000000000FFFF | First 16 bytes valid |
| **8 bytes** | 64'h00000000000000FF | First 8 bytes valid |
| **4 bytes** | 64'h000000000000000F | First 4 bytes valid |
| **1 byte** | 64'h0000000000000001 | First byte valid |

#### Assumption 2: TLAST for Packet Boundaries

| Aspect | Requirement |
|--------|-------------|
| **Packet Delimiter** | TLAST=1 on final transfer of packet |
| **Single-Beat Packets** | TLAST=1 for single-transfer packets |
| **Multi-Beat Packets** | TLAST=0 for all transfers except last |
| **Mandatory Signal** | TLAST required for all packet-based protocols |
| **Rationale** | Enables downstream packet processing and buffering |

#### Assumption 3: No TSTRB Usage

| Aspect | Requirement |
|--------|-------------|
| **TSTRB Disabled** | TSTRB signals not used (TSTRB_ENABLE=0) |
| **Byte Qualification** | TKEEP provides sufficient byte-level control |
| **Rationale** | RAPIDS data is always read-oriented (no write strobes needed) |
| **Benefit** | Reduces interface width and complexity |

#### Assumption 4: Optional TID and TDEST

| Aspect | Requirement |
|--------|-------------|
| **TID Usage** | Transaction ID not required for RAPIDS use cases |
| **TDEST Usage** | Destination routing optional (set by interface type) |
| **Default Configuration** | TID_WIDTH=0, TDEST_WIDTH=0 for simple streaming |
| **Rationale** | RAPIDS uses point-to-point connections, no routing needed |

---

## Master (Transmit) Interface Specification

### AXIS Master Signals

| Signal | Width | Direction | Required | Description |
|--------|-------|-----------|----------|-------------|
| `m_axis_tdata` | `TDATA_WIDTH` | Master->Slave | Yes | Stream data payload |
| `m_axis_tvalid` | 1 | Master->Slave | Yes | Data valid indicator |
| `m_axis_tready` | 1 | Slave->Master | Yes | Ready for data (backpressure) |
| `m_axis_tlast` | 1 | Master->Slave | Yes | Last transfer in packet |
| `m_axis_tkeep` | `TDATA_WIDTH/8` | Master->Slave | Yes | Byte qualifier (valid bytes) |
| `m_axis_tid` | `TID_WIDTH` | Master->Slave | Optional | Transaction ID |
| `m_axis_tdest` | `TDEST_WIDTH` | Master->Slave | Optional | Routing destination |
| `m_axis_tuser` | `TUSER_WIDTH` | Master->Slave | Optional | User sideband data |

### Master Transfer Rules

| Rule | Requirement | Description |
|------|-------------|-------------|
| **Transfer Occurrence** | Transfer occurs when `TVALID=1 AND TREADY=1` | Standard AXIS handshake |
| **TVALID Assertion** | Master can assert TVALID independently of TREADY | Master controls data availability |
| **TVALID Stability** | Once TVALID=1, all T* signals must remain stable until TREADY=1 | Data integrity requirement |
| **TREADY Dependency** | Slave can assert TREADY based on TVALID state | Backpressure control |
| **TKEEP Alignment** | Valid bytes start from byte 0, must be contiguous | Per Assumption 1 |
| **TLAST Requirement** | TLAST=1 on final beat of every packet | Per Assumption 2 |

---

## Slave (Receive) Interface Specification

### AXIS Slave Signals

| Signal | Width | Direction | Required | Description |
|--------|-------|-----------|----------|-------------|
| `s_axis_tdata` | `TDATA_WIDTH` | Master->Slave | Yes | Stream data payload |
| `s_axis_tvalid` | 1 | Master->Slave | Yes | Data valid indicator |
| `s_axis_tready` | 1 | Slave->Master | Yes | Ready for data (backpressure) |
| `s_axis_tlast` | 1 | Master->Slave | Yes | Last transfer in packet |
| `s_axis_tkeep` | `TDATA_WIDTH/8` | Master->Slave | Yes | Byte qualifier (valid bytes) |
| `s_axis_tid` | `TID_WIDTH` | Master->Slave | Optional | Transaction ID |
| `s_axis_tdest` | `TDEST_WIDTH` | Master->Slave | Optional | Routing destination |
| `s_axis_tuser` | `TUSER_WIDTH` | Master->Slave | Optional | User sideband data |

### Slave Flow Control

| Aspect | Behavior | Description |
|--------|----------|-------------|
| **TREADY=1** | Slave ready to accept data | Normal operation |
| **TREADY=0** | Slave cannot accept data (backpressure) | Flow control active |
| **TREADY Timing** | Can be asserted/deasserted on any cycle | Dynamic flow control |
| **Buffer Management** | TREADY reflects downstream buffer availability | Prevents overflow |

---

## Packet Structure and Framing

### Single-Beat Packet

**Packet with data <= 64 bytes (fits in one transfer):**

```
Clock:      -+ +-+ +-
            +-+ +-+

TVALID:     --+ +---
            +-+

TREADY:     --------
            (always ready)

TDATA:      [Packet Data (64 bytes max)]

TKEEP:      [Valid byte mask (e.g., 64'h00000000FFFFFFFF for 32 bytes)]

TLAST:      --+ +---
            +-+

Transfer: Single beat completes entire packet
```

### Multi-Beat Packet

**Packet with data > 64 bytes (requires multiple transfers):**

```
Clock:      -+ +-+ +-+ +-+ +-
            +-+ +-+ +-+ +-+

TVALID:     --+       +---
            +---------+

TREADY:     ----------------
            (always ready)

TDATA:      [Beat 0][Beat 1][Beat 2][Beat 3]
            64B     64B     64B     32B (partial)

TKEEP:      [64'hFFFF...][64'hFFFF...][64'hFFFF...][64'h00000000FFFFFFFF]
            All valid   All valid   All valid   32 bytes valid

TLAST:      --------------+ +---
            +-+

Transfer: 4 beats (256 bytes total)
- Beats 0-2: Full 64-byte transfers, TLAST=0
- Beat 3: Partial 32-byte transfer, TLAST=1
```

### Packet with Backpressure

**Backpressure applied mid-packet:**

```
Clock:      -+ +-+ +-+ +-+ +-+ +-+ +-
            +-+ +-+ +-+ +-+ +-+ +-+

TVALID:     --+               +---
            +-------------------+

TREADY:     --+ +-+ +---+ +-----
            +-+ +-+ +-+

TDATA:      [Beat 0]  (stall) [Beat 1]  (stall) [Beat 2]

TKEEP:      [Valid]   (held)  [Valid]   (held)  [Valid]

TLAST:      --------------------------+ +---
                                    +-+

Transfer: 3 beats with backpressure
- Beat 0: Transfers immediately
- Stall: TREADY=0, TVALID held high, data held stable
- Beat 1: Transfers after 2 stall cycles
- Stall: Another 1-cycle stall
- Beat 2: Final beat transfers, TLAST=1
```

**Key Observations:**
1. Master must hold TVALID=1 and all T* signals stable during backpressure
2. Slave controls flow via TREADY signal
3. Transfer only occurs when both TVALID=1 AND TREADY=1

---

## TUSER Sideband Signaling

### Purpose and Usage

| Aspect | Description |
|--------|-------------|
| **Purpose** | Carry packet metadata alongside data stream |
| **Scope** | Valid on first beat of packet only (when new packet starts) |
| **Width** | Application-specific (0-128 bits) |
| **Examples** | Packet type, priority, timestamp, sequence number |

### RAPIDS-Specific TUSER Encoding (Delta Network Integration)

**TUSER[1:0] - Delta Network Packet Type Encoding:**

RAPIDS enforces strict packet type filtering based on TUSER[1:0] encoding as defined by the Delta Network specification:

| TUSER[1:0] | Packet Type | Full Name | Accepted By | Sent By | Purpose |
|------------|-------------|-----------|-------------|---------|---------|
| **2'b00** | **PKT_DATA** | Data Packet | RAPIDS, Compute Tiles | RAPIDS, Compute Tiles | Compute data transfers |
| **2'b01** | **CDA** | Compute Direct Access | RAPIDS only | HIVE-C only | Descriptor injection |
| **2'b10** | **PKT_CONFIG** | Configuration Packet | Tile Routers | HIVE-C, SERV | Configuration |
| **2'b11** | **PKT_STATUS** | Status Packet | HIVE-C | SERV monitors | Monitoring/status |

**RAPIDS Interface Packet Type Rules:**

| RAPIDS Interface | Direction | Accepts | Sends | Rejects |
|------------------|-----------|---------|-------|---------|
| **AXIS CDA Input** | Slave | CDA (2'b01) | - | PKT_DATA, PKT_CONFIG, PKT_STATUS |
| **AXIS Data Output (MM2S)** | Master | - | PKT_DATA (2'b00) | CDA, PKT_CONFIG, PKT_STATUS |
| **AXIS Data Input (S2MM)** | Slave | PKT_DATA (2'b00) | - | CDA, PKT_CONFIG, PKT_STATUS |

**Packet Type Validation:**
- **Invalid packet rejection:** RAPIDS asserts TREADY=0 when invalid TUSER value detected
- **Error reporting:** Sets error flag in status register
- **Interrupt generation:** Generates interrupt (if enabled) on packet type violation
- **Hardware enforcement:** RAPIDS cannot transmit invalid packet types (design constraint)

**Additional TUSER Fields (RAPIDS-Specific):**

For PKT_DATA and CDA packets, RAPIDS may use additional TUSER bits beyond [1:0]:

| Bits | Field | Description | Usage |
|------|-------|-------------|-------|
| `[1:0]` | **Packet Type** | PKT_DATA or CDA | **Mandatory** - Delta Network routing |
| `[5:2]` | **Priority** | 0-15 priority level | Optional - Descriptor scheduling |
| `[7:6]` | **Reserved** | Future use | - |

**Usage Pattern:**
- TUSER valid on **every beat** of packet (Delta Network requirement)
- TUSER[1:0] must be consistent across all beats of same packet
- Downstream logic validates TUSER[1:0] on every beat for protocol compliance
- Priority field (TUSER[5:2]) used for CDA packet scheduling in descriptor engine

---

## Flow Control and Backpressure

### Backpressure Mechanisms

| Mechanism | Implementation | Description |
|-----------|----------------|-------------|
| **Immediate Backpressure** | TREADY=0 for N cycles | Slave cannot accept data |
| **Conditional Backpressure** | TREADY toggles based on buffer state | Dynamic flow control |
| **Sustained Backpressure** | TREADY=0 for extended period | Upstream buffer fills |

### Backpressure Propagation

```
Source SRAM Control -> AXIS Master -> AXIS Slave -> Sink SRAM Control
                         ↑              ↓
                      TREADY      Backpressure
                   (flow control)
```

**Propagation Rules:**
1. Slave asserts TREADY=0 when downstream buffer nearly full
2. Master stops sending data (TVALID may remain high, data held)
3. Backpressure propagates to source (SRAM read stalls)
4. System self-regulates to prevent buffer overflow

### Buffer Depth Considerations

| Buffer Type | Recommended Depth | Rationale |
|-------------|-------------------|-----------|
| **AXIS Input FIFO** | 16-32 beats | Absorb backpressure latency |
| **AXIS Output FIFO** | 16-32 beats | Smooth bursty traffic |
| **Packet Buffer** | 4-8 packets | Handle multi-packet scenarios |

---

## Reset Behavior

### Reset Requirements

| Reset Phase | Requirement | Description |
|-------------|-------------|-------------|
| **Active Reset** | `aresetn` is active-low reset signal | Standard AXI reset |
| **TVALID During Reset** | TVALID=0 when aresetn=0 | No spurious transfers |
| **TREADY During Reset** | TREADY can be 0 or 1 (don't care) | Slave state undefined |
| **State Clearing** | All FIFOs/buffers flushed during reset | Clean startup |
| **Post-Reset** | TVALID=0 for at least 1 cycle after reset release | Stable initialization |

### Reset Timing

```
Clock:      -+ +-+ +-+ +-+ +-+ +-+ +-
            +-+ +-+ +-+ +-+ +-+ +-+

aresetn:    ------+           +-----
                +-----------+

TVALID:     ------------------+ +---
                            +-+
                            (stable after reset)

TREADY:     ------------------? ? ?--
                            (don't care initially)

Note: TVALID must be 0 during and immediately after reset
```

---

## Implementation Benefits

### Streaming Efficiency

| Benefit Area | Advantage | Impact |
|-------------|-----------|---------|
| **Continuous Streaming** | No address overhead (unlike AXI4) | Maximum throughput |
| **Simple Handshake** | Valid-ready protocol only | Minimal control logic |
| **Burst Transfers** | Multi-beat packets for efficiency | High bandwidth utilization |
| **Flow Control** | Built-in backpressure mechanism | Prevents data loss |

### Packet-Based Processing

| Benefit Area | Advantage | Impact |
|-------------|-----------|---------|
| **Packet Framing** | TLAST delimits packets | Enables packet-level processing |
| **Byte Granularity** | TKEEP handles partial transfers | Supports variable-length packets |
| **Metadata Support** | TUSER carries packet info | Rich packet classification |

### Resource Efficiency

| Benefit Area | Simplification | Impact |
|-------------|----------------|---------|
| **No Address Logic** | Streaming-only interface | Reduced logic complexity |
| **No Transaction IDs** | Point-to-point connections | Simplified state machines |
| **Optional Signals** | TID/TDEST/TUSER as needed | Minimal interface width |
| **Byte Alignment** | Contiguous bytes only | No complex data steering |

---

## Timing Requirements

### Setup and Hold Times

| Timing Parameter | Requirement | Description |
|------------------|-------------|-------------|
| **TVALID to TREADY** | Setup time: 0 ns | Combinational ready allowed |
| **TREADY to TVALID** | Setup time: 1 clock cycle | TVALID registered before TREADY check |
| **T* Signal Stability** | Hold until TREADY=1 | Data integrity during backpressure |

### Clock Domain Considerations

| Scenario | Requirement | Solution |
|----------|-------------|----------|
| **Synchronous Operation** | Single clock domain | Direct connection |
| **Asynchronous Operation** | Different clock domains | Insert AXIS async FIFO |
| **Clock Frequency Ratio** | Producer faster than consumer | Backpressure handles rate mismatch |

---

## Validation Requirements

### Functional Validation

| Validation Area | Requirements |
|----------------|-------------|
| **Valid-Ready Handshake** | Verify all transfers occur only when TVALID=1 AND TREADY=1 |
| **TKEEP Encoding** | Verify byte validity matches TKEEP pattern |
| **TLAST Assertion** | Verify TLAST=1 on final beat of every packet |
| **Backpressure Handling** | Verify master holds TVALID and T* signals during TREADY=0 |
| **Packet Integrity** | Verify multi-beat packets reconstruct correctly |
| **Byte Alignment** | Verify valid bytes are contiguous starting from byte 0 |

### Timing Validation

| Validation Area | Requirements |
|----------------|-------------|
| **Signal Stability** | Verify T* signals stable when TVALID=1 until TREADY=1 |
| **Reset Behavior** | Verify TVALID=0 during and after reset |
| **Clock Crossing** | Verify async FIFO metastability protection (if used) |

### Stress Testing

| Test Type | Description | Expected Behavior |
|-----------|-------------|-------------------|
| **Sustained Backpressure** | TREADY=0 for 100+ cycles | Master waits without data corruption |
| **Rapid Backpressure Toggle** | TREADY toggles every cycle | Transfer rate adapts correctly |
| **Maximum Throughput** | TREADY=1 always | Full bandwidth utilization |
| **Single-Beat Packets** | All packets fit in one beat | TLAST=1 on every transfer |
| **Large Multi-Beat Packets** | Packets spanning 100+ beats | Correct packet reconstruction |

---

## Example Transactions

### Example 1: Single-Beat Packet (32 bytes)

**Configuration:**
- TDATA_WIDTH = 512 bits (64 bytes)
- Packet size = 32 bytes
- Single transfer

**Signals:**
```
Clock cycle:    -+ +-
                +-+

TVALID:         --+ +---
                +-+

TREADY:         ----------
                (ready)

TDATA:          [32 bytes of packet data | 32 bytes unused]

TKEEP:          64'h00000000FFFFFFFF  (first 32 bytes valid)

TLAST:          --+ +---
                +-+

TUSER:          [Packet metadata - type, priority, etc.]
```

**Result:** Entire packet transfers in single beat.

### Example 2: Multi-Beat Packet with Backpressure (200 bytes)

**Configuration:**
- TDATA_WIDTH = 512 bits (64 bytes)
- Packet size = 200 bytes
- Requires 4 beats: 64 + 64 + 64 + 8 bytes

**Signals:**
```
Clock cycle:    -+ +-+ +-+ +-+ +-+ +-+ +-
                +-+ +-+ +-+ +-+ +-+ +-+

TVALID:         --+                   +---
                +-----------------------+

TREADY:         --+ +-----+ +-+ +-+ +---
                +-+     +-+ +-+ +-+
                (backpressure cycles 2-3, 5)

Beat 0:         [64 bytes] TKEEP=64'hFFFF..., TLAST=0
                Transfers immediately

Stall:          (cycles 2-3, TREADY=0, master holds data)

Beat 1:         [64 bytes] TKEEP=64'hFFFF..., TLAST=0
                Transfers after stall

Stall:          (cycle 5, TREADY=0 again)

Beat 2:         [64 bytes] TKEEP=64'hFFFF..., TLAST=0
                Transfers after stall

Beat 3:         [8 bytes] TKEEP=64'h00000000000000FF, TLAST=1
                Final beat transfers

TUSER:          [Valid on beat 0 only]
```

**Result:** 200-byte packet transfers across 4 beats with intermittent backpressure. Total transfer takes 7 clock cycles (4 beats + 3 stall cycles).

### Example 3: Back-to-Back Packets

**Configuration:**
- Two packets: Packet A (64 bytes), Packet B (128 bytes)
- No gaps between packets

**Signals:**
```
Clock cycle:    -+ +-+ +-+ +-
                +-+ +-+ +-+

TVALID:         --+       +---
                +---------+

TREADY:         ----------------

Beat 0:         [Packet A - 64 bytes] TKEEP=64'hFFFF..., TLAST=1
                TUSER=[Packet A metadata]

Beat 1:         [Packet B beat 0 - 64 bytes] TKEEP=64'hFFFF..., TLAST=0
                TUSER=[Packet B metadata]

Beat 2:         [Packet B beat 1 - 64 bytes] TKEEP=64'hFFFF..., TLAST=1
                TUSER=(ignored, mid-packet)
```

**Result:** Back-to-back packets transfer efficiently without idle cycles. TUSER updates on first beat of each new packet.

---

## Common Use Cases

### Network Interface Applications

| Use Case | Configuration | Description |
|----------|---------------|-------------|
| **Packet Transmission** | 512-bit TDATA, TKEEP, TLAST, TUSER | High-bandwidth network TX |
| **Packet Reception** | 512-bit TDATA, TKEEP, TLAST, TUSER | High-bandwidth network RX |
| **Streaming DMA** | 512-bit TDATA, TKEEP, TLAST | Memory-to-network data transfer |
| **Flow-Controlled Streaming** | Dynamic TREADY | Backpressure-aware streaming |

### Data Path Integration

| Integration Pattern | Description |
|---------------------|-------------|
| **Source Path** | AXI4 Read -> SRAM -> AXIS Master -> Network |
| **Sink Path** | Network -> AXIS Slave -> SRAM -> AXI4 Write |
| **Loopback** | AXIS Master -> AXIS Slave (testing) |
| **Multi-Stage Pipeline** | AXIS -> Processing -> AXIS (chained) |

### Performance Characteristics

| Metric | Typical Value | Description |
|--------|---------------|-------------|
| **Latency** | 1-2 cycles | TVALID assertion to TREADY response |
| **Throughput** | 1 beat per clock | Sustained rate (no backpressure) |
| **Efficiency** | 95-100% | With occasional backpressure |
| **Packet Rate** | Dependent on size | 64-byte packets: ~10Gbps @ 200MHz |

---

## RAPIDS-Specific Considerations (Delta Network Integration)

### Interface Assignments

| RAPIDS Interface | AXIS Role | Direction | Width | Packet Types | Delta Network Connection |
|------------------|-----------|-----------|-------|--------------|--------------------------|
| **AXIS CDA Input** | Slave (RX) | Input | 128-bit | CDA (2'b01) only | From HIVE-C via Delta Network |
| **AXIS Data Output (MM2S)** | Master (TX) | Output | 128-bit | PKT_DATA (2'b00) only | To compute tiles via Delta Network |
| **AXIS Data Input (S2MM)** | Slave (RX) | Input | 128-bit | PKT_DATA (2'b00) only | From compute tiles via Delta Network |
| **Internal Source Stream** | Master (TX) | Internal | 512-bit | N/A - Internal datapath | SRAM to MM2S engine |
| **Internal Sink Stream** | Slave (RX) | Internal | 512-bit | N/A - Internal datapath | S2MM engine to SRAM |

**Key Points:**
- **Delta Network interfaces:** 128-bit TDATA width (standard Delta Network data width)
- **Internal datapaths:** 512-bit TDATA width (high-bandwidth SRAM access)
- **TUSER enforcement:** Hardware validates packet types on all Delta Network interfaces
- **Virtual Tile 16:** RAPIDS addressed as tile 16 in Delta Network topology

### Packet Processing Flow

**CDA Descriptor Path (HIVE-C -> RAPIDS):**
```
HIVE-C (VexRiscv RISC-V)
    ↓ CDA packet (TUSER=2'b01)
Delta Network (routes to tile 16)
    ↓ 128-bit AXIS
RAPIDS AXIS CDA Input (packet type validation)
    ↓ Descriptor extraction
Descriptor FIFO (256-bit descriptors)
    ↓ Parsed descriptors
Scheduler (executes MM2S or S2MM operations)
```

**S2MM Path (Compute Tiles -> Memory):**
```
Compute Tiles (0-15)
    ↓ PKT_DATA packet (TUSER=2'b00, TID=source tile)
Delta Network (routes to tile 16)
    ↓ 128-bit AXIS
RAPIDS AXIS Data Input (S2MM)
    ↓ Packet type validation (TUSER=2'b00)
    ↓ TID → Channel routing (TID[3:0] = channel ID)
S2MM Channel FIFO (per-channel buffering)
    ↓ Internal 512-bit datapath
Sink SRAM Control (buffering)
    ↓ AXI4 Write
DDR Memory
```

**MM2S Path (Memory -> Compute Tiles):**
```
DDR Memory
    ↓ AXI4 Read
Source SRAM Control (buffering)
    ↓ Internal 512-bit datapath
MM2S Data FIFO
    ↓ Packet formation
RAPIDS AXIS Data Output (MM2S)
    ↓ PKT_DATA packet (TUSER=2'b00, TDEST=target tile)
Delta Network (routes to tile 0-15)
    ↓ 128-bit AXIS
Compute Tiles (destination tile)
```

### Buffer Sizing Guidelines

| Buffer Location | Recommended Size | Rationale |
|-----------------|------------------|-----------|
| **Network Input FIFO** | 32 beats (2KB) | Absorb network burst traffic |
| **Network Output FIFO** | 32 beats (2KB) | Smooth AXI4 read latency |
| **SRAM Depth** | 1024-4096 entries | Match typical packet sizes |

---

## Comparison with Other AXIS Variants

### AXIS vs Full AXI4

| Feature | AXIS | Full AXI4 |
|---------|------|-----------|
| **Addressing** | No addressing (streaming) | Full address bus |
| **Channels** | Single data channel | 5 independent channels (AR, R, AW, W, B) |
| **Transaction IDs** | Optional (rarely used) | Mandatory for out-of-order |
| **Burst Support** | Continuous streaming | Fixed-length bursts |
| **Complexity** | Low | High |
| **Use Case** | Streaming data | Random-access memory |

### AXIS Configuration Trade-offs

| Configuration | Advantages | Disadvantages |
|---------------|------------|---------------|
| **Wide Data Path (512-bit)** | High throughput, fewer transfers | More routing resources |
| **Narrow Data Path (64-bit)** | Simpler routing, lower resource | Lower throughput, more transfers |
| **With TUSER** | Rich metadata support | Increased interface width |
| **Without TUSER** | Minimal interface | Limited metadata capability |

---

## Appendix: Signal Quick Reference

### Mandatory Signals

| Signal | Width | Source | Description |
|--------|-------|--------|-------------|
| `TDATA` | `TDATA_WIDTH` | Master | Streaming data payload |
| `TVALID` | 1 | Master | Data valid indicator |
| `TREADY` | 1 | Slave | Ready for data (backpressure) |
| `TLAST` | 1 | Master | Last transfer in packet |

### Optional Signals

| Signal | Width | Source | When to Use |
|--------|-------|--------|-------------|
| `TKEEP` | `TDATA_WIDTH/8` | Master | Byte-level data validity (recommended) |
| `TSTRB` | `TDATA_WIDTH/8` | Master | Write strobes (rarely used) |
| `TID` | `TID_WIDTH` | Master | Transaction routing/identification |
| `TDEST` | `TDEST_WIDTH` | Master | Destination routing |
| `TUSER` | `TUSER_WIDTH` | Master | User-defined sideband metadata |

### Signal Relationships

```
TVALID=1 + TREADY=1 -> Transfer occurs
TVALID=1 + TREADY=0 -> Master waits (holds all T* signals)
TVALID=0 + TREADY=? -> No transfer (TREADY don't care)
TLAST=1              -> Final beat of packet
TKEEP[n]=1           -> Byte n of TDATA is valid
TKEEP[n]=0           -> Byte n of TDATA is invalid (ignored)
```

---

**Next:** [Chapter 3 - Interface 5: MonBus](05_monbus_interface_spec.md)
