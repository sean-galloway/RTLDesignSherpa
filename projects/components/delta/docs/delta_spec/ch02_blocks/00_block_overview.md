# Chapter 2: Block Overview

DELTA's 4x4 mesh consists of 16 router/tile combinations, each containing several functional blocks working together to route packets and execute computation.

## Block Hierarchy

```
Per-Tile Architecture
+---------------------------------------------------------------+
|                       Tile i                                  |
|                                                               |
|  +---------------------------+  +-------------------------+   |
|  |     Router Block          |  |   Compute Element       |   |
|  |  - Input Buffers (5×8)    |  |   - Processing logic    |   |
|  |  - Packet Classifier      |  |   - Local memory        |   |
|  |  - VC Allocator           |  |   - Instruction decode  |   |
|  |  - Crossbar Switch (5×5)  |  +------------+------------+   |
|  |  - Output Buffers (5×4)   |               |                |
|  +------------+--------------+               |                |
|               |                              |                |
|               |        +---------------------+                |
|               |        |                                      |
|  +------------v--------v----------+  +--------------------+   |
|  |   Network Interface (NI)       |  |   SERV Monitor     |   |
|  |   - Injection Port             |  |   - Traffic stats  |   |
|  |   - Reception Port             |  |   - Error detect   |   |
|  |   - Packet Filter & Validator  |  |   - Status report  |   |
|  +--------------------------------+  +--------------------+   |
|               |  AXIS (128-bit)                               |
+---------------+-----------------------------------------------+
                |
                v
        To North/South/East/West neighbors
```

## Major Functional Blocks

### 1. Router Block
- **Purpose**: Route packets between five ports (N/S/E/W/Local)
- **Key Components**:
  - Input buffers (8 flits per port)
  - Packet classifier (TUSER/TDEST decode)
  - Virtual channel allocator (2 VCs per link)
  - 5×5 non-blocking crossbar
  - Output buffers (4 flits per port)
- **Details**: [Router Architecture](01_router_architecture.md)

### 2. Network Interface (NI)
- **Purpose**: Connect compute element to router
- **Key Functions**:
  - Packetization of local data
  - Injection rate control
  - Packet type enforcement
  - Reception filtering
- **Details**: [Network Interface](02_network_interface.md)

### 3. Packet Classifier
- **Purpose**: Determine routing based on packet type and destination
- **Key Functions**:
  - Read TUSER[1:0] (packet type)
  - Read TDEST[3:0] (destination tile)
  - Compute output port via XY routing
  - Handle virtual tile mapping
- **Details**: [Packet Classifier](03_packet_classifier.md)

### 4. Virtual Channel Allocator
- **Purpose**: Arbitrate between virtual channels for output port access
- **Key Functions**:
  - Manage credit-based flow control
  - Prioritize control traffic (VC0) over data (VC1)
  - Prevent deadlock via VC separation
- **Details**: [Virtual Channel Allocator](04_virtual_channel_allocator.md)

### 5. Crossbar Switch
- **Purpose**: Connect any input port to any output port
- **Key Functions**:
  - 5×5 non-blocking routing
  - Single-cycle traversal
  - Conflict-free simultaneous transfers
- **Details**: [Crossbar Switch](05_crossbar_switch.md)

## Block Interaction Flow

```
Packet arrives at North input port:

1. Input Buffer receives packet
   - Stores 8 flits deep
   - Sends credit back to upstream

2. Packet Classifier examines header
   - Reads TUSER = PKT_DATA
   - Reads TDEST = 5 (tile 5)
   - Computes: current tile = 1, dest = 5
   - XY routing: go East (column 1 -> 2)

3. VC Allocator checks East output
   - PKT_DATA uses VC1
   - Credits available for VC1? Yes (6/8)
   - Grant packet to crossbar

4. Crossbar routes North -> East
   - Single cycle transfer
   - No conflicts with other ports

5. Output Buffer stages packet
   - Dequeues from East buffer
   - Sends to East neighbor
   - Returns credit to North input
```

## Resource Budget (Per Router)

| Component | LUTs | FFs | BRAM (36Kb) |
|-----------|------|-----|-------------|
| Input Buffers (5×8 flits) | 2,000 | 1,600 | 64 bits |
| Packet Classifier | 200 | 150 | 0 |
| VC Allocator | 150 | 100 | 0 |
| Crossbar (5×5) | 400 | 200 | 0 |
| Output Buffers (5×4 flits) | 800 | 600 | 32 bits |
| **Total per router** | **~3,550** | **~2,650** | **~2** |

**Full 4×4 Network (16 routers):**
- 16 × 3,550 = 56,800 LUTs
- 16 × 2,650 = 42,400 FFs
- 16 × 2 = 32 BRAM blocks

---

**Next:** [Router Architecture](01_router_architecture.md)
