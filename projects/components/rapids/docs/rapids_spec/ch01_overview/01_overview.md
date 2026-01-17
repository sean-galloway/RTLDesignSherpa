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

# Chapter 1.1: RAPIDS Overview

## 1.1.1 Executive Summary

RAPIDS (Rapid AXI Programmable In-band Descriptor System) is a high-performance DMA engine designed to bridge AXI4 memory-mapped interfaces with the Delta Network compute fabric. It operates under control of the HIVE-C master controller (VexRiscv RISC-V core) which provides inband descriptor injection through the Delta Network. RAPIDS intelligently routes data between external DDR memory and compute tiles while enforcing strict packet type filtering to maintain protocol integrity.

**Key Features:**
- **Scatter-gather DMA** with linked descriptor chains
- **Inband descriptor reception** via CDA (Compute Direct Access) packets - no memory polling
- **Multi-priority descriptor scheduling** for efficient task execution
- **16-channel S2MM architecture** (one channel per compute tile in 4×4 mesh)
- **Packet type filtering** on all AXIS interfaces
- **Performance monitoring** and statistics collection
- **Completion interrupt** generation

## 1.1.2 Position in System Architecture

RAPIDS serves as the critical bridge between the memory subsystem and the Delta Network compute fabric:

```
┌─────────────────────────────────────────────────────────────┐
│                         HIVE-C                              │
│                  (VexRiscv RISC-V Master)                   │
│                                                             │
│  Generates CDA descriptors, injects via AXIS               │
└──────────────────────┬──────────────────────────────────────┘
                       │ AXIS TX (CDA packets)
                       ▼
              ┌────────────────────┐
              │   Delta Network    │
              │   Routes packets   │
              │   based on TUSER   │
              └────────┬───────────┘
                       │ CDA -> RAPIDS (tile 16)
                       │ PKT_DATA -> Compute Tiles (0-15)
                       ▼
┌──────────────────────────────────────────────────────────────┐
│                      RAPIDS DMA Engine                       │
│                    (Virtual Tile 16)                         │
│  ┌─────────────────────────────────────────────────────┐    │
│  │  AXIS CDA Input (Slave)                             │    │
│  │  - Accepts: CDA packets only                        │    │
│  │  - Rejects: PKT_DATA, PKT_CONFIG, PKT_STATUS        │    │
│  │  - Routes to: Descriptor FIFO                       │    │
│  └──────────────────┬──────────────────────────────────┘    │
│                     ▼                                        │
│  ┌─────────────────────────────────────────────────────┐    │
│  │  Descriptor Processing Engine                       │    │
│  │  - Parses 256-bit descriptors                       │    │
│  │  - Schedules by priority                            │    │
│  │  - Generates AXI4 transactions                      │    │
│  └──────────────────┬──────────────────────────────────┘    │
│                     ▼                                        │
│  ┌─────────────────────────────────────────────────────┐    │
│  │  AXI4 Memory Interface (Master)                     │    │
│  │  - Reads from DDR (activations, weights)            │    │
│  │  - Writes to DDR (results)                          │    │
│  └──────────────────┬──────────────────────────────────┘    │
│                     ▼                                        │
│  ┌─────────────────────────────────────────────────────┐    │
│  │  AXIS Data Output (Master)                          │    │
│  │  - Sends: PKT_DATA only                             │    │
│  │  - Never sends: CDA, PKT_CONFIG, PKT_STATUS         │    │
│  │  - Routes to: Delta Network -> Compute Tiles         │    │
│  └──────────────────┬──────────────────────────────────┘    │
└────────────────────┼────────────────────────────────────────┘
                     │
                     ▼
            ┌─────────────────┐
            │ Delta Network   │
            │ (PKT_DATA only) │
            └─────────┬───────┘
                      ▼
            Compute Tiles (0-15)

Memory: DDR2/DDR3 ◄──AXI4──┤ RAPIDS ├──AXIS──► Delta Network
```

## 1.1.3 Virtual Tile Concept

Within the Delta Network topology, RAPIDS is addressed as **Virtual Tile 16**:

```
Delta Network 4×4 Physical Mesh (Tiles 0-15)
┌────┬────┬────┬────┐
│ T0 │ T1 │ T2 │ T3 │  Row 0
├────┼────┼────┼────┤
│ T4 │ T5 │ T6 │ T7 │  Row 1
├────┼────┼────┼────┤
│ T8 │ T9 │T10 │T11 │  Row 2
├────┼────┼────┼────┤
│T12 │T13 │T14 │T15 │  Row 3
└────┴────┴────┴────┘
         │
         └─── Virtual Tile 16 (RAPIDS) connected via Router 12 south port

Virtual Tile 17 (HIVE-C) connected via Router 3 north port
```

**Routing Implications:**
- **To RAPIDS:** TDEST = 16 routes packets from compute tiles to RAPIDS
- **From RAPIDS:** TDEST = 0-15 routes data to specific compute tiles
- **CDA packets:** Automatically routed to RAPIDS (tile 16) by Delta Network

## 1.1.4 Packet Type Handling

RAPIDS enforces strict packet type filtering based on TUSER encoding:

| Interface | Direction | Accepts | Sends | Rejects |
|-----------|-----------|---------|-------|---------|
| **AXIS CDA Input** | Slave | CDA packets | - | PKT_DATA, PKT_CONFIG, PKT_STATUS |
| **AXIS Data Out** | Master | - | PKT_DATA | CDA, PKT_CONFIG, PKT_STATUS |
| **AXIS Data In** | Slave | PKT_DATA | - | CDA, PKT_CONFIG, PKT_STATUS |

### Packet Type Encoding (TUSER[1:0])

| TUSER[1:0] | Packet Type | Generated By | Accepted By |
|------------|-------------|--------------|-------------|
| 2'b00 | PKT_DATA | RAPIDS, Compute Tiles | RAPIDS, Compute Tiles |
| 2'b01 | CDA (Compute Direct Access) | HIVE-C only | RAPIDS only |
| 2'b10 | PKT_CONFIG | HIVE-C, SERV monitors | Tile Routers |
| 2'b11 | PKT_STATUS | SERV monitors | HIVE-C |

**Rejection Behavior:**
- **Invalid packet type on input:** Assert TREADY=0, set error flag, generate interrupt
- **Transmission enforcement:** Hardware prevents transmission of invalid packet types

## 1.1.5 Data Flow: Memory to Compute (MM2S)

```
1. HIVE-C generates CDA descriptor in firmware
2. HIVE-C writes descriptor to AXIS TX FIFO with TUSER=CDA (2'b01)
3. Delta Network routes CDA packet to RAPIDS (tile 16)
4. RAPIDS validates TUSER == CDA, writes to descriptor FIFO
5. Scheduler prioritizes and fetches descriptor
6. MM2S engine:
   a. Reads data from DDR via AXI4
   b. Buffers in internal FIFO
   c. Formats AXIS packets with TUSER=PKT_DATA (2'b00)
   d. Sets TDEST to target compute tile (from descriptor)
   e. Transmits to Delta Network
7. Delta Network routes PKT_DATA to destination tile
8. Completion interrupt generated (if enabled)
```

## 1.1.6 Data Flow: Compute to Memory (S2MM)

RAPIDS implements **16 independent S2MM channels**, one per compute tile:

```
1. HIVE-C pre-programs S2MM descriptors (one per active tile)
2. Compute tiles generate results, send as PKT_DATA with:
   - TUSER = PKT_DATA (2'b00)
   - TID = source tile ID (0-15)  <- CRITICAL for channel routing
   - TDEST = 16 (RAPIDS virtual tile)
3. Delta Network routes to RAPIDS
4. RAPIDS S2MM channel router:
   channel_id = TID[3:0]  // Direct mapping: TID -> Channel
5. Selected S2MM channel:
   a. Validates TUSER == PKT_DATA
   b. Buffers in per-channel FIFO
   c. Fetches descriptor from per-channel queue
   d. Writes to DDR via AXI4 (address from descriptor)
6. Completion interrupt generated (if enabled)
```

**Multi-Channel Benefits:**
- **Concurrent writes:** Multiple tiles write simultaneously
- **Independent addressing:** Each tile's data goes to different DDR region
- **Per-tile flow control:** Backpressure on one tile doesn't affect others
- **Simplified routing:** Direct TID -> Channel mapping (no lookup table)

## 1.1.7 CDA Packet Format

CDA (Compute Direct Access) packets carry descriptor information from HIVE-C to RAPIDS:

**Format:** 256 bits (2 AXIS beats at 128-bit width)

```
Beat 0:
TUSER[1:0] = 2'b01        // CDA packet type
TDATA[127:0] = Desc[127:0] // Descriptor bits [127:0]
TLAST = 0                 // More beats follow
TID[3:0] = Priority       // 0=highest, 15=lowest
TDEST[3:0] = 4'h0         // Always RAPIDS (routed to tile 16)

Beat 1:
TUSER[1:0] = 2'b01        // CDA packet type
TDATA[127:0] = Desc[255:128] // Descriptor bits [255:128]
TLAST = 1                 // Final beat
TID[3:0] = Priority       // Same as beat 0
TDEST[3:0] = 4'h0         // Always RAPIDS
```

**Descriptor Fields (256 bits total):**
- Bits [255:192]: Source Address (64-bit DDR address)
- Bits [191:128]: Destination Address (64-bit DDR address)
- Bits [127:96]: Transfer Length (32-bit bytes)
- Bits [95:64]: Control/Configuration (stride, tile ID, etc.)
- Bits [63:32]: Control Flags (type, priority, interrupts)
- Bits [31:0]: Next Descriptor Pointer (scatter-gather chaining)

See Chapter 2 (Descriptor Engine) for complete descriptor field definitions.

## 1.1.8 System Integration Summary

**RAPIDS Never Generates:**
- CDA packets (only HIVE-C generates these)
- PKT_CONFIG (only HIVE-C or SERV monitors generate)
- PKT_STATUS (only SERV monitors generate)

**RAPIDS Always Validates:**
- CDA input packets must have TUSER = 2'b01
- Data input packets must have TUSER = 2'b00
- Any other TUSER value triggers error condition and packet rejection

**Control Plane:**
- HIVE-C uses AXI4-Lite to access RAPIDS control/status registers
- CDA packets provide descriptor injection (inband, low latency)
- Interrupts notify HIVE-C of completion/errors

**Data Plane:**
- AXI4 master interface to DDR memory (read/write)
- AXIS master interface to Delta Network (PKT_DATA out)
- AXIS slave interface from Delta Network (PKT_DATA in)
- Multi-channel architecture supports concurrent tile operations

---

**Next:** [Architectural Requirements](02_architectural_requirements.md)

**Back to:** [Index](../rapids_index.md)
