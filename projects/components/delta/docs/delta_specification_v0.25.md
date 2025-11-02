# DELTA Network Specification
**Distributed Execution Layer for Tensor Acceleration**  
Version 0.3 - Early Proof of Concept (Draft)

---

## 1. Executive Summary

DELTA is a configurable mesh Network-on-Chip (NoC) that routes four distinct packet types between the RAPIDS DMA engine, HIVE control system, and compute tiles. The network implements intelligent packet filtering and routing based on AXIS TUSER encoding, ensuring protocol isolation between data, control, and monitoring traffic.

**Key Features:**
- 4×4 mesh topology (16 compute tiles) for proof-of-concept
- Four packet types: DATA, DESC, CONFIG, STATUS
- Virtual configuration contexts for topology reconfiguration
- Wormhole flow control with virtual channels
- XY dimension-ordered routing (deadlock-free)
- Per-tile packet filtering and forwarding rules
- AXIS protocol throughout

---

## 2. System Integration

### 2.1 Network Position

```
┌──────────────────────────────────────────────────────────┐
│                    HIVE Control Plane                    │
│                                                          │
│  ┌─────────────┐          ┌─────────────────────────┐   │
│  │   HIVE-C    │          │  16× SERV Monitors      │   │
│  │ (VexRiscv)  │          │  (one per tile)         │   │
│  └──────┬──────┘          └────┬─────────────┬──────┘   │
│         │                      │             │          │
│    PKT_DESC              PKT_CONFIG    PKT_STATUS       │
│         │                      │             │          │
└─────────┼──────────────────────┼─────────────┼──────────┘
          │                      │             │
          ▼                      ▼             ▼
┌─────────────────────────────────────────────────────────┐
│              DELTA Network (AXIS Mesh NoC)              │
│                                                         │
│  Packet Routing Based on TUSER[1:0]:                   │
│  - PKT_DATA   (00) → Compute Tiles                     │
│  - PKT_DESC   (01) → RAPIDS DMA                        │
│  - PKT_CONFIG (10) → Target Tile(s) Config Registers   │
│  - PKT_STATUS (11) → HIVE-C Monitoring Aggregator      │
│                                                         │
│   ┌────┬────┬────┬────┐                                │
│   │R0  │R1  │R2  │R3  │  R = Router + Tile             │
│   ├────┼────┼────┼────┤  Each has:                     │
│   │R4  │R5  │R6  │R7  │  - 5-port router (N/S/E/W/L)  │
│   ├────┼────┼────┼────┤  - Network Interface (NI)      │
│   │R8  │R9  │R10 │R11 │  - SERV monitor                │
│   ├────┼────┼────┼────┤  - Compute element             │
│   │R12 │R13 │R14 │R15 │  - Packet filter               │
│   └────┴────┴────┴────┘                                │
│                                                         │
│  Special Routing:                                       │
│  - RAPIDS attached as virtual tile 16 (external)       │
│  - HIVE-C attached as virtual tile 17 (external)       │
└─────────┬───────────────────────────────────┬───────────┘
          │                                   │
     PKT_DATA                            PKT_DATA
   (to tiles)                          (from tiles)
          │                                   │
          ▼                                   ▼
    ┌──────────┐                       ┌──────────┐
    │  RAPIDS  │◄──PKT_DESC────────────┤  HIVE-C  │
    │   DMA    │                       │ (VexRiscv)
    └──────────┘                       └──────────┘
         ▲
         │ AXI4
         ▼
     [DDR Memory]
```

### 2.2 Packet Flow Matrix

| Source | Packet Type | Destination(s) | Path Through DELTA |
|--------|-------------|----------------|-------------------|
| HIVE-C | PKT_DESC | RAPIDS | Direct route to virtual tile 16 |
| HIVE-C | PKT_CONFIG | Tile(s) 0-15 | Multicast via tile mask |
| RAPIDS | PKT_DATA | Tile(s) 0-15 | XY route to TDEST tile |
| Tile N | PKT_DATA | RAPIDS | XY route to virtual tile 16 |
| Tile N | PKT_DATA | Tile M | XY route peer-to-peer |
| SERV N | PKT_CONFIG | Tile N (local) | Direct to local config registers |
| SERV N | PKT_STATUS | HIVE-C | XY route to virtual tile 17 |

**Never Occurs (Hardware Prevents):**
- RAPIDS sending PKT_DESC (only receives)
- Compute Tiles sending PKT_DESC (not authorized)
- PKT_DATA routed to HIVE-C (filtered)
- PKT_CONFIG routed to RAPIDS (filtered)

---

## 3. Packet Type Routing

### 3.1 AXIS TUSER Encoding

```verilog
// All AXIS interfaces use this encoding
typedef enum logic [1:0] {
    PKT_DATA   = 2'b00,  // Compute data (activations, weights, results)
    PKT_DESC   = 2'b01,  // DMA descriptor (HIVE-C → RAPIDS only)
    PKT_CONFIG = 2'b10,  // Configuration command (HIVE-C/SERV → Tiles)
    PKT_STATUS = 2'b11   // Status/monitoring (SERV → HIVE-C)
} packet_type_t;
```

### 3.2 Routing Decision Logic

Each router examines TUSER[1:0] and TDEST[3:0]:

```verilog
always_comb begin
    case (pkt_tuser)
        PKT_DATA: begin
            // Route to compute tile or RAPIDS
            if (pkt_tdest == 4'd16) begin
                route_to_rapids();  // Virtual tile 16
            end else if (pkt_tdest < 4'd16) begin
                route_to_tile(pkt_tdest);  // Tile 0-15
            end else begin
                drop_packet();  // Invalid destination
            end
        end
        
        PKT_DESC: begin
            // Always route to RAPIDS (only valid destination)
            route_to_rapids();
        end
        
        PKT_CONFIG: begin
            // Route to tile(s) based on mask in payload
            // Supports multicast for broadcast configs
            route_by_tile_mask();
        end
        
        PKT_STATUS: begin
            // Always route to HIVE-C monitoring aggregator
            route_to_hive_c();  // Virtual tile 17
        end
    endcase
end
```

### 3.3 Virtual Tile Mapping

DELTA extends the 4×4 physical mesh with virtual tiles:

| Tile ID | Type | Location | Purpose |
|---------|------|----------|---------|
| 0-15 | Physical | Mesh positions (0,0) to (3,3) | Compute tiles |
| 16 | Virtual | External (south of tile 12) | RAPIDS DMA |
| 17 | Virtual | External (north of tile 3) | HIVE-C controller |

**Routing to Virtual Tiles:**
- Tile 16 (RAPIDS): Reached via tile 12 south port
- Tile 17 (HIVE-C): Reached via tile 3 north port
- Physical routing unaffected (XY still works)

---

## 4. Router Architecture

### 4.1 Five-Port Router Design

```
         North (to tile i-4)
            ▲
            │
West ◄──────┼──────► East
  (i-1)     │       (i+1)
            │
            ▼
         South (to tile i+4)
            
            │
            ▼
        Local Port
    (to compute tile i)
```

**Port Functions:**
- **North/South/East/West:** Inter-router links (128-bit AXIS)
- **Local:** Connection to tile's Network Interface (NI)

### 4.2 Router Block Diagram

```
┌────────────────────────────────────────────────────────┐
│                  Router i                              │
│                                                        │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐            │
│  │  Input   │  │  Input   │  │  Input   │  (×5 ports)│
│  │  Buffer  │  │  Buffer  │  │  Buffer  │            │
│  │  (8 flits)│ │  (8 flits)│ │  (8 flits)│           │
│  └─────┬────┘  └─────┬────┘  └─────┬────┘            │
│        │             │             │                  │
│        └─────────────┼─────────────┘                  │
│                      ▼                                │
│           ┌──────────────────────┐                    │
│           │  Packet Classifier   │                    │
│           │  - Reads TUSER[1:0]  │                    │
│           │  - Reads TDEST[3:0]  │                    │
│           │  - Computes next hop │                    │
│           └──────────┬───────────┘                    │
│                      ▼                                │
│           ┌──────────────────────┐                    │
│           │  Virtual Channel     │                    │
│           │  Allocator           │                    │
│           │  - 2 VCs per port    │                    │
│           │  - Credit-based FC   │                    │
│           └──────────┬───────────┘                    │
│                      ▼                                │
│           ┌──────────────────────┐                    │
│           │   Crossbar Switch    │                    │
│           │   5×5 non-blocking   │                    │
│           └──────────┬───────────┘                    │
│                      │                                │
│        ┌─────────────┼─────────────┐                  │
│        ▼             ▼             ▼                  │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐            │
│  │  Output  │  │  Output  │  │  Output  │  (×5 ports)│
│  │  Buffer  │  │  Buffer  │  │  Buffer  │            │
│  │  (4 flits)│ │  (4 flits)│ │  (4 flits)│           │
│  └────┬─────┘  └────┬─────┘  └────┬─────┘            │
│       │            │            │                     │
└───────┼────────────┼────────────┼─────────────────────┘
        │            │            │
       AXIS         AXIS         AXIS
     (to next)    (to next)    (to next)
```

### 4.3 XY Routing Algorithm

```verilog
function [2:0] compute_output_port(
    input [3:0] current_tile,  // 0-15 for mesh, 16=RAPIDS, 17=HIVE-C
    input [3:0] dest_tile,
    input [1:0] pkt_type
);
    logic [1:0] curr_x, curr_y;
    logic [1:0] dest_x, dest_y;
    
    // Extract coordinates (4x4 mesh)
    curr_x = current_tile[1:0];  // Column
    curr_y = current_tile[3:2];  // Row
    
    // Handle virtual tiles
    if (dest_tile == 16) begin  // RAPIDS
        dest_x = 2'd0;  // Column 0
        dest_y = 2'd4;  // Virtual row 4 (south of row 3)
    end else if (dest_tile == 17) begin  // HIVE-C
        dest_x = 2'd3;  // Column 3
        dest_y = 2'd255; // Virtual row -1 (north of row 0)
    end else begin
        dest_x = dest_tile[1:0];
        dest_y = dest_tile[3:2];
    end
    
    // XY routing: X-dimension first
    if (dest_x < curr_x) begin
        return PORT_WEST;
    end else if (dest_x > curr_x) begin
        return PORT_EAST;
    end else if (dest_y < curr_y) begin
        return PORT_NORTH;
    end else if (dest_y > curr_y) begin
        return PORT_SOUTH;
    end else begin
        return PORT_LOCAL;  // Arrived at destination
    end
endfunction
```

---

## 5. Network Interface (NI)

### 5.1 Per-Tile Network Interface

Each tile has a Network Interface connecting the compute element to the router:

```
┌────────────────────────────────────────────────┐
│         Network Interface (Tile i)             │
│                                                │
│  From Compute Element / SERV Monitor:         │
│  ┌──────────────────────────────────┐         │
│  │  Injection Port (AXIS Master)    │         │
│  │  - Accepts from local sources    │         │
│  │  - Packetizes if needed          │         │
│  │  - Sets TUSER based on source:   │         │
│  │    • Compute → PKT_DATA          │         │
│  │    • SERV → PKT_CONFIG/STATUS    │         │
│  │  - Sets TDEST from local logic   │         │
│  └────────────┬─────────────────────┘         │
│               │                               │
│               ▼                               │
│  ┌──────────────────────────────────┐         │
│  │  Packet Filter & Validator       │         │
│  │  - Checks local permissions       │         │
│  │  - Prevents unauthorized types    │         │
│  │  - Rate limits if configured      │         │
│  └────────────┬─────────────────────┘         │
│               │                               │
│               ▼                               │
│          To Router                            │
│               │                               │
│               ▼                               │
│  From Router:                                 │
│  ┌──────────────────────────────────┐         │
│  │  Reception Port (AXIS Slave)      │         │
│  │  - Receives packets for this tile │         │
│  │  - Filters by TUSER:              │         │
│  │    • PKT_DATA → Compute Element   │         │
│  │    • PKT_CONFIG → Config Regs     │         │
│  │    • Others → Drop/Error          │         │
│  └────────────┬─────────────────────┘         │
│               │                               │
└───────────────┼───────────────────────────────┘
                │
                ▼
    To Compute Element / Config Registers
```

### 5.2 Packet Filtering Rules

Each NI enforces these rules:

**Injection (Tile → Network):**
```verilog
// Compute elements can only send PKT_DATA
if (source == COMPUTE && pkt_tuser != PKT_DATA) begin
    reject_packet();
    set_error_flag(ERR_UNAUTHORIZED_TYPE);
end

// CRITICAL: Compute elements MUST set TID to own tile ID
// This allows RAPIDS to route incoming data to correct S2MM channel
if (source == COMPUTE && pkt_tuser == PKT_DATA) begin
    // Hardware enforces TID = MY_TILE_ID for data from compute
    pkt_tid_override = MY_TILE_ID[3:0];
end

// SERV monitors can send PKT_CONFIG (local) or PKT_STATUS (to HIVE-C)
if (source == SERV && !(pkt_tuser inside {PKT_CONFIG, PKT_STATUS})) begin
    reject_packet();
    set_error_flag(ERR_UNAUTHORIZED_TYPE);
end
```

**Reception (Network → Tile):**
```verilog
case (pkt_tuser)
    PKT_DATA: begin
        // Route to compute element
        forward_to_compute();
    end
    
    PKT_CONFIG: begin
        // Route to configuration registers
        forward_to_config_regs();
    end
    
    PKT_DESC, PKT_STATUS: begin
        // Not valid for regular tiles
        drop_packet();
        set_error_flag(ERR_INVALID_DEST);
    end
endcase
```

---

## 6. Virtual Configuration Contexts

### 6.1 Supported Topologies

DELTA supports multiple routing modes via virtual contexts:

**Context 0 - Mesh (XY Routing):**
- Standard 2D mesh with XY dimension-ordered routing
- Default mode, always available
- Deadlock-free by construction

**Context 1 - Systolic:**
- Direct nearest-neighbor communication only
- Router bypass for lowest latency (1-2 cycles/hop)
- North→South and West→East data flow
- Used for matrix multiplication, convolution

**Context 2 - Tree Reduction:**
- Hierarchical aggregation topology
- Bottom row (tiles 12-15) as leaf nodes
- Top row (tiles 0-3) as aggregators
- Optimized for global reduction operations (sum, max)

**Context 3 - Custom/Debug:**
- User-programmable routing tables
- Supports arbitrary topologies
- Enables experimentation with novel routing algorithms

### 6.2 Context Switching Mechanism

```
1. HIVE-C issues CONFIG_PREPARE command (PKT_CONFIG broadcast)
   - All tiles flush in-flight packets
   - Routers enter quiescent state
   - FIFOs drain (5-10 cycles)

2. HIVE-C broadcasts SET_ROUTING_MODE with context ID
   - Mode register updated: MODE_SELECT ← context_id
   - Routing table pointer switched
   - All routers update simultaneously (1 cycle)

3. HIVE-C issues CONFIG_ACTIVATE command
   - Tiles resume packet injection
   - Network operational in new mode

Total switching time: 10-20 cycles (deterministic)
```

### 6.3 Configuration Register Bank

Each router/tile has configuration registers:

```
Base + 0x00: MODE_SELECT       (RW) - Active context [1:0]
Base + 0x04: ROUTE_TABLE_BASE  (RO) - Current routing table address
Base + 0x08: CUSTOM_ROUTE_0    (RW) - User routing entry 0
Base + 0x0C: CUSTOM_ROUTE_1    (RW) - User routing entry 1
     ...
Base + 0x20: FILTER_ENABLE     (RW) - Enable packet type filtering
Base + 0x24: ALLOWED_TYPES     (RW) - Permitted TUSER values (bitmask)
Base + 0x28: RATE_LIMIT        (RW) - Max injection rate (pkts/1000 cyc)
Base + 0x2C: STATUS            (RO) - Router state, buffer occupancy
Base + 0x30: ERROR_FLAGS       (RW1C) - Protocol violations, overflows
Base + 0x34: PKT_COUNT_TX      (RO) - Packets transmitted (this tile)
Base + 0x38: PKT_COUNT_RX      (RO) - Packets received (this tile)
```

---

## 7. Flow Control

### 7.1 Credit-Based Virtual Channels

Each router uses credit-based flow control to prevent buffer overflow:

**Initialization:**
- Downstream router has 8-flit input buffer per VC
- Upstream router initialized with 8 credits per VC
- Credits represent available buffer slots

**Operation:**
```
1. Upstream wants to send flit
   - Check if credits[vc] > 0
   - If yes: send flit, decrement credits[vc]
   - If no: stall (wait for credit return)

2. Downstream receives flit
   - Store in input buffer
   - Process/forward flit
   - Send credit back upstream (increment credits[vc])

3. Steady state:
   - Credits flow opposite to flits
   - No overflow possible (guaranteed by credits)
   - Backpressure propagates naturally
```

### 7.2 Virtual Channel Allocation

Two virtual channels per physical link:

**VC0 - High Priority:**
- PKT_DESC, PKT_CONFIG, PKT_STATUS
- Control/monitoring traffic has priority
- Lower buffer depth (4 flits) - less latency critical

**VC1 - Standard Priority:**
- PKT_DATA
- Bulk data transfers
- Larger buffer depth (8 flits) - more throughput critical

**Arbitration:**
```verilog
// VC0 has strict priority over VC1
if (vc0_has_packet && vc0_credits > 0) begin
    grant_vc0();
end else if (vc1_has_packet && vc1_credits > 0) begin
    grant_vc1();
end else begin
    idle();
end
```

---

## 8. Packet Format and Framing

### 8.1 AXIS Signal Mapping

All network links use AXIS with these signals:

```verilog
// 128-bit data path
logic [127:0] TDATA;   // Payload (flit data)
logic [15:0]  TKEEP;   // Byte enables (usually all 1's)
logic         TLAST;   // End of packet marker
logic [1:0]   TUSER;   // Packet type (PKT_DATA/DESC/CONFIG/STATUS)
logic [3:0]   TID;     // Source tile ID (for PKT_DATA) or priority/sequence
logic [3:0]   TDEST;   // Destination tile (0-17)
logic         TVALID;  // Data valid
logic         TREADY;  // Receiver ready (backpressure)
```

**CRITICAL: TID Field Usage**

The TID field serves different purposes based on packet type:

| Packet Type | TID Meaning | Set By | Preserved By Router |
|-------------|-------------|--------|---------------------|
| PKT_DATA (to RAPIDS) | Source Tile ID (0-15) | Tile NI (enforced) | Yes - never modified |
| PKT_DATA (to Tiles) | Priority/Sequence | RAPIDS MM2S | Yes |
| PKT_DESC | Priority Level | HIVE-C | Yes |
| PKT_CONFIG | Broadcast ID | HIVE-C/SERV | Yes |
| PKT_STATUS | Reporting Tile ID | SERV (= MY_TILE_ID) | Yes |

**Router TID Handling:**
```verilog
// Routers NEVER modify TID field
// It flows end-to-end from source to destination
always_ff @(posedge clk) begin
    if (input_valid && output_ready) begin
        output_tid <= input_tid;  // Pass through unchanged
    end
end
```

### 8.2 Multi-Flit Packets

**Single-Flit Packet (≤128 bits):**
```
Beat 0: TDATA[127:0] = payload
        TLAST = 1
        TUSER = packet type
        TDEST = destination
```

**Multi-Flit Packet (>128 bits):**
```
Beat 0: TDATA[127:0] = payload[127:0]
        TLAST = 0
        
Beat 1: TDATA[127:0] = payload[255:128]
        TLAST = 0
        
Beat N: TDATA[127:0] = payload[...]
        TLAST = 1  (final beat)

Note: TUSER, TDEST carried only on first beat
      Router caches for subsequent beats
```

### 8.3 Packet Examples

**PKT_DATA (Activation Transfer from RAPIDS to Tile):**
```
TDATA  = {activation_data}  (128 bits per beat)
TKEEP  = 16'hFFFF            (all bytes valid)
TLAST  = 1                   (single flit, or =1 on final)
TUSER  = 2'b00               (PKT_DATA)
TID    = 4'd2                (priority level - set by RAPIDS MM2S)
TDEST  = 4'd5                (destination: tile 5)
```

**PKT_DATA (Results from Tile 7 back to RAPIDS):**
```
TDATA  = {result_data}       (128 bits per beat)
TKEEP  = 16'hFFFF            
TLAST  = 1                   
TUSER  = 2'b00               (PKT_DATA)
TID    = 4'd7                (CRITICAL: source tile ID - set by Tile 7 NI)
TDEST  = 4'd16               (destination: RAPIDS virtual tile)

// RAPIDS receives this and uses TID=7 to route to S2MM Channel 7
```

**PKT_DESC (DMA Descriptor from HIVE-C):**
```
Beat 0:
TDATA  = descriptor[127:0]
TLAST  = 0
TUSER  = 2'b01               (PKT_DESC)
TID    = 4'd0                (high priority)
TDEST  = 4'd16               (destination: RAPIDS)

Beat 1:
TDATA  = descriptor[255:128]
TLAST  = 1
```

**PKT_CONFIG (Broadcast to All Tiles):**
```
TDATA  = {tile_mask[31:0], command[31:0], payload[63:0]}
TLAST  = 1
TUSER  = 2'b10               (PKT_CONFIG)
TID    = 4'd0                (broadcast identifier)
TDEST  = 4'd15               (doesn't matter for broadcast)
                              (tile_mask determines actual targets)
```

**PKT_STATUS (SERV Report from Tile 3 to HIVE-C):**
```
TDATA  = {tile_id[7:0], status_type[7:0], timestamp[47:0], data[63:0]}
TLAST  = 1
TUSER  = 2'b11               (PKT_STATUS)
TID    = 4'd3                (reporting tile ID - matches TDATA[127:120])
TDEST  = 4'd17               (destination: HIVE-C)
```

---

## 9. Special Routing Cases

### 9.1 Broadcast Configuration

PKT_CONFIG packets can target multiple tiles simultaneously:

```verilog
// Packet payload contains 32-bit tile mask
logic [31:0] tile_mask = pkt_data[127:96];

// Each router checks if it's targeted
if (tile_mask[my_tile_id] == 1'b1) begin
    // Accept packet locally
    forward_to_local_config();
    
    // Also forward to next hop if other tiles targeted
    if (tile_mask & ~(1 << my_tile_id)) begin
        continue_forwarding();
    end
end
```

**Example: Configure all tiles in row 2:**
```
tile_mask = 32'h0000_0F00  // Bits 8-11 set (tiles 8-11)
Each router 8-11 accepts locally and forwards
```

### 9.2 Peer-to-Peer Data

Tiles can send PKT_DATA directly to each other:

```
Scenario: Tile 3 sends result to Tile 10

1. Tile 3 compute element generates result
2. NI sets TUSER=PKT_DATA, TDEST=10
3. Router 3 routes: East (to tile 4)
4. Router 4 routes: East (to tile 5, wait...)
   
Actually, let me recalculate XY routing:
Tile 3 is at (3,0) - column 3, row 0
Tile 10 is at (2,2) - column 2, row 2

X-dimension first: 3 → 2 (go West)
3. Router 3 routes West to tile 2
4. Router 2 routes West to tile 1
   
Wait, that's wrong. Let me redo:
Tile 3 coords: col=3, row=0
Tile 10 coords: col=2, row=2

Step 1: X-dimension (col 3 → col 2): go WEST
  R3 sends to R2
Step 2: Still X-dimension (col 2 == col 2): done with X
Step 3: Y-dimension (row 0 → row 2): go SOUTH
  R2 sends to R6 (row 1)
  R6 sends to R10 (row 2)
Step 4: Arrived at R10, send to local port

Total hops: 3 (R3→R2, R2→R6, R6→R10)
Latency: 3 hops × 3 cycles = 9 cycles (mesh mode)
```

### 9.3 External Entity Routing

RAPIDS and HIVE-C are not in the mesh but have dedicated connections:

**RAPIDS (Virtual Tile 16):**
- Physically connected to Router 12 (tile 12) south port
- All PKT_DESC packets routed to tile 12 first, then south
- PKT_DATA from RAPIDS enters at tile 12, routes normally

**HIVE-C (Virtual Tile 17):**
- Physically connected to Router 3 (tile 3) north port
- All PKT_STATUS packets routed to tile 3 first, then north
- PKT_DESC/CONFIG from HIVE-C enters at tile 3, routes normally

```
Tile Layout:
      HIVE-C (virtual 17)
         ▲
         │ (north port)
    ┌────┼────┬────┬────┐
    │ T0 │ T1 │ T2 │ T3 │
    ├────┼────┼────┼────┤
    │ T4 │ T5 │ T6 │ T7 │
    ├────┼────┼────┼────┤
    │ T8 │ T9 │ T10│ T11│
    ├────┼────┼────┼────┤
    │ T12│ T13│ T14│ T15│
    └────┼────┴────┴────┘
         │ (south port)
         ▼
    RAPIDS (virtual 16)
```

---

## 10. Performance Characteristics

### 10.1 Latency Model

**Single-hop latency:**
- Input buffering: 1 cycle
- Routing decision: 1 cycle
- Crossbar traversal: 1 cycle
- Output buffering: 1 cycle (optional)
- **Total: 3-4 cycles per hop**

**Multi-hop examples (4×4 mesh):**
| Source → Dest | Hops | Latency (cycles) |
|---------------|------|------------------|
| T0 → T1 | 1 | 3-4 |
| T0 → T5 | 2 | 6-8 |
| T0 → T15 | 6 | 18-24 (worst case) |
| Any → RAPIDS (avg) | 3.5 | 10-14 |
| Any → HIVE-C (avg) | 3.5 | 10-14 |

**Context switching overhead:**
- Systolic mode: 1-2 cycles per hop (bypass routing)
- Tree mode: Variable (depends on position in tree)

### 10.2 Throughput Analysis

**Per-Link Bandwidth:**
- 128 bits @ 100 MHz = 1.6 GB/s per direction
- Full-duplex: 3.2 GB/s aggregate per link

**Bisection Bandwidth (4×4 mesh):**
- Horizontal cuts: 4 links × 1.6 GB/s = 6.4 GB/s
- Vertical cuts: 4 links × 1.6 GB/s = 6.4 GB/s
- **Total: 6.4 GB/s bisection**

**Network Aggregate:**
- 40 total links (24 H + 16 V) in 4×4 mesh
- 40 × 1.6 GB/s = 64 GB/s aggregate
- Actual sustained: 60-70% (38-45 GB/s) due to contention

### 10.3 Resource Utilization

**Per Router (LUTs/FFs/BRAM):**
- Input buffers (5 ports × 8 flits): 2,000 LUTs, 64 BRAM bits
- Routing logic: 200 LUTs, 150 FFs
- VC allocator: 150 LUTs, 100 FFs
- Crossbar (5×5): 400 LUTs, 200 FFs
- Output buffers (5 ports × 4 flits): 800 LUTs, 32 BRAM bits
- **Total per router: ~500 LUTs, 450 FFs, 2 BRAM (36Kb)**

**Full 4×4 Network:**
- 16 routers × 500 LUTs = 8,000 LUTs
- 16 routers × 450 FFs = 7,200 FFs
- 16 routers × 2 BRAM = 32 BRAM blocks
- **Plus NI overhead: +1,200 LUTs, +800 FFs, +4 BRAM**
- **Total DELTA: 9,200 LUTs, 8,000 FFs, 36 BRAM**

---

## 11. Traffic Monitoring Integration

### 11.1 SERV Monitor Visibility

Each SERV monitor observes local router traffic:

```
SERV Monitor N has read access to:
- Router N input buffer occupancy (all 5 ports)
- Router N output credit counts (all 5 ports)
- Packet counters (per port, per type)
- Congestion flags
- Error status

SERV can inject PKT_STATUS to HIVE-C when:
- Buffer occupancy > threshold (congestion)
- Error condition detected
- Periodic reporting timer expires
```

### 11.2 Status Reporting Example

```c
// SERV firmware: Detect and report congestion
void serv_monitor_loop(void) {
    while (1) {
        // Read router status
        uint8_t north_buf = ROUTER_STATUS.north_occupancy;
        
        if (north_buf > CONGESTION_THRESHOLD) {
            // Build status packet
            status_pkt_t pkt;
            pkt.tile_id = MY_TILE_ID;
            pkt.type = STATUS_CONGESTION;
            pkt.timestamp = get_cycle_count();
            pkt.data = north_buf;
            
            // Inject via AXIS (TUSER=PKT_STATUS, TDEST=17)
            inject_status_packet(&pkt);
        }
        
        delay(MONITOR_INTERVAL);
    }
}
```

---

## 12. Educational Features

### 12.1 Experimentation Hooks

**Modify routing algorithm:**
```systemverilog
// File: delta_router_routing.sv
parameter ROUTING_ALGO = "XY";  // or "YX", "WEST_FIRST", "CUSTOM"

// Students can implement custom routing:
function [2:0] custom_routing(
    input [3:0] src, dst,
    input [1:0] pkt_type
);
    // Your algorithm here
endfunction
```

**Adjust buffer depths:**
```systemverilog
// Trade latency for area
parameter INPUT_BUF_DEPTH = 8;   // Increase for more buffering
parameter OUTPUT_BUF_DEPTH = 4;  // Decrease to save BRAM
parameter NUM_VIRTUAL_CHANNELS = 2; // More VCs = more QoS
```

**Add custom packet type:**
```systemverilog
// Extend to 3-bit TUSER for more types
typedef enum logic [2:0] {
    PKT_DATA = 3'b000,
    PKT_DESC = 3'b001,
    PKT_CONFIG = 3'b010,
    PKT_STATUS = 3'b011,
    PKT_DEBUG = 3'b100,   // Student addition
    PKT_TRACE = 3'b101    // Student addition
} pkt_type_extended_t;
```

### 12.2 Visualization and Debug

**Packet Trace Capture:**
```systemverilog
// Each router can export trace data
output logic [127:0] debug_trace;
output logic         debug_trace_valid;

always_ff @(posedge clk) begin
    if (pkt_valid && debug_enable) begin
        debug_trace <= {
            src_tile, dst_tile, pkt_type,
            timestamp, payload_preview
        };
        debug_trace_valid <= 1;
    end
end
```

**Web Visualizer Integration:**
- Real-time packet animation (source → destination)
- Buffer occupancy heatmap (color-coded by utilization)
- Throughput graphs per link
- Congestion hotspot detection

---

## 13. System Integration Summary

### 13.1 Complete Packet Flow

```
Use Case: HIVE-C loads activations into Tile 7, Tile 7 computes, returns results

1. HIVE-C generates MM2S descriptor (load activations)
   - src_addr = 0x1000_0000 (DDR activation buffer)
   - dst_addr = 0 (unused for MM2S)
   - length = 0x1000 (4 KB)
   - dest_tile_id = 7
   - type = MM2S (Memory→Network)

2. HIVE-C injects descriptor:
   TDATA = descriptor (256 bits, 2 beats)
   TUSER = PKT_DESC (2'b01)
   TID = 0 (high priority)
   TDEST = 16 (RAPIDS)

3. DELTA routes PKT_DESC to RAPIDS:
   R3 (HIVE-C entry) → R2 → R1 → R0 → R4 → R8 → R12 → RAPIDS

4. RAPIDS MM2S engine executes:
   - Reads 0x1000 bytes from DDR starting at 0x1000_0000
   - Formats AXIS packets:
     TDATA = activation_data
     TUSER = PKT_DATA (2'b00)
     TID = 0 (priority from descriptor)
     TDEST = 7 (destination tile)
   - Sends to DELTA

5. DELTA routes PKT_DATA to Tile 7:
   R12 → R13 → R14 → R15 → R11 → R7

6. Tile 7 receives activations, performs computation

7. HIVE-C pre-programs S2MM descriptor for results:
   - src_addr = 0 (unused for S2MM)
   - dst_addr = 0x2000_0000 (DDR result buffer for tile 7)
   - length = 0x800 (2 KB results)
   - source_tile_id = 7 (CRITICAL - expect TID=7)
   - type = S2MM (Network→Memory)

8. HIVE-C injects S2MM descriptor:
   TDATA = descriptor
   TUSER = PKT_DESC
   TDEST = 16 (RAPIDS)

9. RAPIDS receives S2MM descriptor:
   - Reads source_tile_id = 7
   - Queues descriptor on S2MM Channel 7
   - Channel 7 now waiting for data with TID=7

10. Tile 7 completes computation, sends results:
    - Compute element sends to NI
    - NI enforces: TID ← 7 (MY_TILE_ID)
    - Packet created:
      TDATA = result_data
      TUSER = PKT_DATA (2'b00)
      TID = 7 (ENFORCED by NI - source tile ID)
      TDEST = 16 (RAPIDS)

11. DELTA routes PKT_DATA from Tile 7 to RAPIDS:
    R7 → R11 → R15 → R14 → R13 → R12 → RAPIDS
    (TID=7 preserved throughout)

12. RAPIDS S2MM receives packet:
    - Examines TID = 7
    - Routes to S2MM Channel 7
    - Channel 7 has queued descriptor ready
    - Writes 2 KB to DDR at 0x2000_0000
    - Generates completion interrupt

13. HIVE-C receives interrupt, proceeds to next operation
```

**Key Points:**
- TID=7 set by Tile 7 NI (hardware enforced)
- TID preserved through entire DELTA routing path
- RAPIDS uses TID=7 to select S2MM Channel 7
- Descriptor on Channel 7 specifies DDR write address
- Complete isolation: each tile's results go to separate channel/memory region

### 13.2 Packet Type Routing Summary

| Packet Type | Generated By | Consumed By | Path |
|-------------|--------------|-------------|------|
| PKT_DATA | RAPIDS, Tiles | RAPIDS, Tiles | DELTA mesh (XY routing) |
| PKT_DESC | HIVE-C only | RAPIDS only | DELTA → R12 → RAPIDS |
| PKT_CONFIG | HIVE-C, SERV | Tile routers | DELTA mesh (broadcast or unicast) |
| PKT_STATUS | SERV only | HIVE-C only | DELTA → R3 → HIVE-C |

---

## Appendix A: Tile Coordinate Mapping

```
Tile ID to (Column, Row) mapping:

ID   Col  Row  |  ID   Col  Row
-----|----------|---------------
 0    0    0   |   8    0    2
 1    1    0   |   9    1    2
 2    2    0   |  10    2    2
 3    3    0   |  11    3    2
 4    0    1   |  12    0    3
 5    1    1   |  13    1    3
 6    2    1   |  14    2    3
 7    3    1   |  15    3    3

Virtual tiles:
16   0    4  (RAPIDS - south of tile 12)
17   3   -1  (HIVE-C - north of tile 3)

Coordinate extraction:
  column = tile_id[1:0]
  row    = tile_id[3:2]
```

---

## Appendix B: Configuration Commands

```
Common PKT_CONFIG commands:

0x0001: SET_ROUTING_MODE
  Payload[1:0] = context_id (0-3)
  
0x0002: UPDATE_ROUTE_TABLE
  Payload[7:0]  = table_index
  Payload[39:8] = route_entry
  
0x0004: SET_PRIORITY_WEIGHTS
  Payload[7:0]   = vc0_weight
  Payload[15:8]  = vc1_weight
  
0x0008: FLUSH_BUFFERS
  No payload
  
0x0010: RESET_STATISTICS
  No payload
  
0x0020: SET_CONGESTION_THRESHOLD
  Payload[7:0] = threshold (buffer occupancy)
```

---

**Document Version:** 0.3 (Early Draft - Proof of Concept)  
**Last Updated:** 2025-10-18  
**Status:** Preliminary specification, subject to significant change  
**Maintained By:** DELTA Development Team