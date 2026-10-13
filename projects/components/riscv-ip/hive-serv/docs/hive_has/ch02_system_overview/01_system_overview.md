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

# System Overview and Context

## Executive Summary

HIVE is a distributed control and monitoring subsystem coordinating the RAPIDS
DMA engine and the Delta Network compute fabric. A hierarchical RISC-V
architecture provides it: one VexRiscv master controller manages global
operations, and sixteen lightweight SERV cores — one per Delta compute tile —
provide per-tile traffic monitoring and inband descriptor/configuration
injection.

**Primary design goals:**
- Low-latency, inband control of RAPIDS DMA through AXIS-native descriptor
  injection (~10-20 cycles vs. 100+ for memory-mapped polling)
- Distributed traffic monitoring across the Delta compute network
- Reconfigurable network topologies through virtual configuration switching
- A comprehensive educational platform with performance models and modular design

**Target platforms:**
- **Proof of Concept:** Digilent NexysA7 100T (Xilinx Artix-7 XC7A100T)
- **Production target:** Digilent Genesys2 (Xilinx Kintex-7 325T)
- **Alternative:** Terasic DE10 Standard (Cyclone V SX, Quartus toolchain)

---

## Hierarchical Organization

```
┌─────────────────────────────────────────────────────────────┐
│                     HIVE Control Plane                      │
│  ┌────────────────────────────────────────────────────┐    │
│  │         VexRiscv Master Controller (HIVE-C)        │    │
│  │  - Global RAPIDS DMA coordination                  │    │
│  │  - Network reconfiguration management              │    │
│  │  - Performance monitoring aggregation              │    │
│  │  - External host interface (UART/AXI4-Lite)        │    │
│  └──────────────────┬─────────────────────────────────┘    │
│                     │ Control Network                       │
│          ┌──────────┴──────────┬──────────────┐           │
│          ▼          ▼          ▼              ▼           │
│  ┌──────────┐ ┌──────────┐ ... ┌──────────┐ (16 tiles)   │
│  │ SERV-0   │ │ SERV-1   │     │ SERV-15  │              │
│  │ Monitor  │ │ Monitor  │     │ Monitor  │              │
│  └────┬─────┘ └────┬─────┘     └────┬─────┘              │
└───────┼────────────┼──────────────────┼───────────────────┘
        │            │                  │
        ▼            ▼                  ▼
┌───────────────────────────────────────────────────────────┐
│              Delta Network (4×4 Mesh)                     │
│   ┌────┬────┬────┬────┐                                  │
│   │T0  │T1  │T2  │T3  │  T = Compute Tile               │
│   ├────┼────┼────┼────┤  Each tile has:                 │
│   │T4  │T5  │T6  │T7  │  - SERV monitor                 │
│   ├────┼────┼────┼────┤  - Compute elements (DSPs)      │
│   │T8  │T9  │T10 │T11 │  - Local BRAM buffers           │
│   ├────┼────┼────┼────┤  - Router/Network Interface     │
│   │T12 │T13 │T14 │T15 │                                  │
│   └────┴────┴────┴────┘                                  │
└───────────────┬───────────────────────────────────────────┘
                ▼
        ┌──────────────┐
        │    RAPIDS    │
        │  DMA Engine  │
        │ (Virtual     │
        │  Tile 16)    │
        └──────────────┘
```

The compute tiles, routers, and network interfaces belong to Delta (see the
Delta HAS). HIVE owns the control plane above them: HIVE-C, the sixteen SERV
monitors, the Control Network, and the Configuration Manager.

---

## Position in the RAPIDS / Delta / HIVE Ecosystem

> **Delta relationship (owner, 2026-10-13):** the delta component
> (`projects/components/fabric-gen-ip/delta/`) — the AXIS fabric
> generator — *is* the fabric HIVE communicates with. The archived
> NoC-mesh draft (`noc-ip/delta_spec/`) and the generator describe the
> same fabric; the 2026-10-12 re-home from `noc-ip/` was organizational.
> HIVE's architecture stands as specified against delta, and HIVE talks
> to it exclusively over AXI4-Stream (§4.1).

```
┌──────────────────────────────────────────────────────────┐
│                      Host System                         │
│              (x86 CPU, ARM SoC, etc.)                    │
└────────────────┬─────────────────────────────────────────┘
                 │ UART / AXI4-Lite
                 ▼
┌──────────────────────────────────────────────────────────┐
│                    HIVE-C Controller                     │
│             (VexRiscv RISC-V @ 100 MHz)                  │
│  ┌────────────────────────────────────────────────┐     │
│  │  Firmware:                                     │     │
│  │  - Parse host commands                         │     │
│  │  - Generate RAPIDS descriptors                 │     │
│  │  - Inject CDA packets to Delta Network         │     │
│  │  - Aggregate SERV statistics                   │     │
│  │  - Manage network reconfiguration              │     │
│  └────────────────────────────────────────────────┘     │
└──────────┬───────────────────────────────┬───────────────┘
           │ CDA packets (AXIS)            │ Control Network
           │ TUSER=2'b01                   │ to SERVs
           ▼                               ▼
┌────────────────────────┐    ┌──────────────────────────┐
│   Delta Network        │    │   16× SERV Monitors      │
│   Routes CDA packets   │◄───┤   - Traffic counters     │
│   to RAPIDS (tile 16)  │    │   - Congestion detection │
│                        │    │   - Packet injection     │
└──────────┬─────────────┘    └──────────────────────────┘
           │ CDA → RAPIDS
           │ PKT_DATA ↔ Tiles
           ▼
┌──────────────────────────────────────────────────────────┐
│                    RAPIDS DMA Engine                     │
│                    (Virtual Tile 16)                     │
│  ┌────────────────────────────────────────────────┐     │
│  │  Descriptor Engine:                            │     │
│  │  - Receives CDA packets from HIVE-C            │     │
│  │  - Parses 256-bit descriptors                  │     │
│  │  - Executes MM2S / S2MM transfers              │     │
│  └────────────────────────────────────────────────┘     │
└──────────┬───────────────────────────────┬───────────────┘
           │ AXI4                          │ AXIS PKT_DATA
           ▼                               ▼
   ┌──────────────┐              ┌─────────────────────┐
   │ DDR Memory   │              │ Compute Tiles 0-15  │
   │ (Activations,│              │ (DSP MACs, BRAM)    │
   │  Weights,    │              │                     │
   │  Results)    │              └─────────────────────┘
   └──────────────┘
```

---

## Control Flow Example: Matrix Multiply

The end-to-end flow that exercises every HIVE block:

1. **Setup (HIVE-C):** Host sends "matmul layer N, tiles 0-7". HIVE-C switches
   Delta to mesh mode if needed, then generates MM2S descriptors (DDR → tiles)
   and S2MM descriptors (tiles → DDR).
2. **Descriptor injection (HIVE-C → RAPIDS):** 256-bit descriptors are sent as
   CDA packets (TUSER=2'b01, TDEST=16); Delta routes them to the RAPIDS
   descriptor engine.
3. **Data movement (RAPIDS → tiles):** RAPIDS executes MM2S descriptors, reads
   activations from DDR over AXI4, and emits PKT_DATA (TUSER=2'b00, TDEST=0-7).
4. **Computation (tiles):** Compute elements produce results and send
   PKT_DATA with TID = source tile. The tile Network Interface overrides TID
   with the local tile ID (hardware-enforced, see §4.2).
5. **Result collection (tiles → RAPIDS → DDR):** PKT_DATA routed to RAPIDS
   (TDEST=16); S2MM channels match on TID; results written to DDR; completion
   interrupt to HIVE-C.
6. **Monitoring (SERV → HIVE-C):** SERV monitors track packet counts and buffer
   occupancy, alert on congestion, and send PKT_STATUS to HIVE-C (TDEST=17).

---

## Virtual Tile Addressing

HIVE participates in the Delta topology as two virtual tiles:

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
         │           │
         ▼           ▼
Virtual Tile 16   Virtual Tile 17
   (RAPIDS)         (HIVE-C)
    DMA Engine      Master Controller
```

**Routing implications:**
- TDEST = 16 routes to the RAPIDS DMA engine
- TDEST = 17 routes to the HIVE-C status aggregator
- From HIVE-C: CDA packets (TUSER=2'b01) route to RAPIDS
- From tiles: PKT_STATUS (TUSER=2'b11) routes to HIVE-C

---

## Packet Type Usage by Component

| Component | Sends | Receives | Purpose |
|-----------|-------|----------|---------|
| **HIVE-C** | CDA (2'b01), PKT_CONFIG (2'b10) | PKT_STATUS (2'b11) | Descriptor injection, network config, monitoring |
| **RAPIDS** | PKT_DATA (2'b00) | CDA (2'b01), PKT_DATA (2'b00) | DMA data transfers |
| **Compute Tiles** | PKT_DATA (2'b00) | PKT_DATA (2'b00), PKT_CONFIG (2'b10) | Computation, reconfiguration |
| **SERV Monitors** | PKT_STATUS (2'b11), PKT_CONFIG (2'b10) | PKT_CONFIG (2'b10) | Traffic reporting, tile control |
| **Delta Routers** | - | PKT_CONFIG (2'b10) | Routing table updates |

: Packet type usage by component

**Validation rules** (checkable by protocol checkers at tile interfaces):
- HIVE-C never sends PKT_DATA or PKT_STATUS
- RAPIDS never sends CDA, PKT_CONFIG, or PKT_STATUS
- Compute tiles never send CDA, PKT_CONFIG, or PKT_STATUS
- SERV monitors send PKT_STATUS and PKT_CONFIG only

---

## Key Architectural Features

**1. Hierarchical control.** HIVE-C is the single global coordinator; the 16
SERV monitors are lightweight agents. One powerful core where decisions are
made, sixteen tiny cores where the data is.

**2. Inband control.** HIVE-C pushes descriptors as CDA packets through the
Delta data fabric — no polling, no sideband descriptor bus. The control path
reuses the network that already exists.

**3. Distributed monitoring.** Each SERV tracks its local router's traffic and
autonomously injects PKT_STATUS on trigger conditions (congestion, errors,
periodic reporting). HIVE-C aggregates rather than polls.

**4. Reconfigurable topology.** Four pre-loaded routing contexts (systolic,
mesh, tree, custom) switch atomically in 10-20 cycles under the Configuration
Manager's quiesce protocol.

**5. Zero data-path ownership.** HIVE carries control and status traffic only;
the Delta data plane and the RAPIDS AXI4 path never traverse HIVE logic.

---

**Last Updated:** 2026-10-13
