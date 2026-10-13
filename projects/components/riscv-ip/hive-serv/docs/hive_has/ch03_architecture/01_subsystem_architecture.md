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

# Subsystem Architecture

HIVE consists of four primary functional blocks. Each has one clear purpose;
together they provide distributed control and monitoring for the RAPIDS/Delta
system.

---

## Block 1: HIVE-C Master Controller

Single VexRiscv RISC-V processor serving as the global coordinator.

**Key specifications:**

| Attribute | Value |
|-----------|-------|
| Core | VexRiscv "Small" configuration |
| ISA | RV32IM (no compressed, no floating point) |
| Pipeline | 5-stage |
| Frequency | 100 MHz (PoC), 150+ MHz (optimized target) |
| Memory | 32 KB tightly-coupled I-mem + 32 KB tightly-coupled D-mem (BRAM) |
| External interfaces | UART/AXI4-Lite slave (host), AXIS master (CDA injection), control network master (SERVs) |

: HIVE-C key specifications

**Responsibilities:**
1. Parse high-level transfer commands from the host
2. Generate RAPIDS DMA descriptors (256-bit CDA packets)
3. Inject descriptors into Delta via AXIS (TUSER=2'b01, TDEST=16)
4. Aggregate traffic statistics from the 16 SERV monitors
5. Manage network reconfiguration sequences
6. Handle interrupt routing and exception processing

**Performance targets:** descriptor injection < 30 cycles (HIVE-C → RAPIDS);
command response < 1 µs @ 100 MHz; all-16-SERV status aggregation < 100 cycles.

---

## Block 2: SERV Monitors (16 instances)

Lightweight per-tile traffic monitors built on SERV bit-serial RISC-V cores.

**Key specifications (per instance):**

| Attribute | Value |
|-----------|-------|
| Core | SERV (Small Embedded RISC-V) |
| ISA | RV32I, bit-serial execution (1 bit/cycle) |
| Frequency | 50-100 MHz (shared `serv_clk`) |
| Resources | ~125 LUTs, 164 FFs, 1 BRAM (2 KB I-mem + 2 KB D-mem) |
| Interfaces | Control network slave (from HIVE-C), AXIS master (PKT_CONFIG/PKT_STATUS), router monitoring taps |

: SERV monitor key specifications

**Responsibilities (per tile):**
1. Monitor local router traffic (packet counts, buffer occupancy)
2. Detect congestion and anomalies against programmable thresholds
3. Generate inband control packets on trigger conditions
4. Inject configuration updates into the local tile
5. Report statistics to HIVE-C via the control network
6. Support debug/trace packet injection

**Monitored metrics (exposed to firmware):**
- Counters (32-bit, wrapping): `pkt_rx_count[4]`, `pkt_tx_count[4]` (per
  direction N/S/E/W), `pkt_local_inject`, `pkt_local_consume`,
  `buffer_overflow_count`, `stall_cycles`
- Real-time: `buffer_occupancy[4]` (8-bit per direction), `congestion_flag`,
  `error_flags` (parity, protocol violations)

**Performance targets:** monitoring overhead < 5% of compute time; congestion
detection < 10 cycles; periodic reporting interval 1000 cycles (configurable).

---

## Block 3: Control Network

Dedicated low-bandwidth infrastructure for HIVE-C ↔ SERV command and status
exchange. Deliberately separate from the Delta data path: control traffic must
not contend with compute traffic, and must remain live during data-plane
quiesce.

| Attribute | Value |
|-----------|-------|
| Topology | Star (HIVE-C master, 16 SERV slaves) |
| Data width | 32 bits (commands and status responses) |
| Arbitration | Round-robin (SERV → HIVE-C uplink) |
| Protocol | Valid/ready handshake, in-order, lossless |

: Control network key specifications

**Responsibilities:**
1. Deliver control commands from HIVE-C to individual SERV monitors
2. Aggregate status reports from SERVs to HIVE-C
3. Provide reliable, in-order delivery (no packet loss)
4. Prioritize urgent alerts over periodic statistics

**Communication patterns:**
- HIVE-C → SERV (multicast or unicast): configuration commands, threshold
  updates, firmware control (soft reset, debug mode)
- SERV → HIVE-C (uplink): periodic statistics (every 1000 cycles), congestion
  alerts (immediate), error notifications

**Performance targets:** command delivery < 10 cycles; status aggregation
< 20 cycles across all 16 SERVs; round-robin fairness (no SERV starvation).

---

## Block 4: Configuration Manager

Manages virtual configuration contexts and orchestrates network topology
switching.

| Attribute | Value |
|-----------|-------|
| Virtual contexts | 4 pre-loaded routing configurations |
| Context storage | BRAM-based context memory (routing tables per tile) |
| Switching protocol | Atomic context switch with packet draining (quiesce) |
| Distribution | PKT_CONFIG broadcast via Delta Network |

: Configuration Manager key specifications

**The four contexts:**

| Context | Name | Character |
|---------|------|-----------|
| 0 | Systolic | Nearest-neighbor N/S/E/W fixed routing; router bypass; 1-2 cycles/hop |
| 1 | Packet-switched mesh | Full XY dimension-ordered routing; credit flow control; 2 virtual channels; 3-4 cycles/hop |
| 2 | Tree reduction | Hierarchical aggregation; tiles 12-15 as roots; E-W reduction tree |
| 3 | Custom/debug | User-programmable routing tables; per-tile independent configuration |

: Virtual configuration contexts

**Responsibilities:**
1. Store multiple virtual configuration contexts
2. Coordinate atomic topology switching across all tiles
3. Manage the quiesce protocol (drain in-flight packets)
4. Broadcast configuration updates via PKT_CONFIG packets
5. Verify successful context-switch completion

**Switching sequence** (detailed protocol in §5.4):
`CONFIG_PREPARE` → drain/quiesce (5-10 cycles) → `SET_ROUTING_MODE` broadcast
→ `CONFIG_ACTIVATE`. Total latency 10-20 cycles, deterministic; budgeted
< 25 cycles including quiesce.

---

## Inter-Block Communication

| Path | Medium | Direction | Bandwidth | Latency |
|------|--------|-----------|-----------|---------|
| HIVE-C ↔ SERVs | Control Network | Bidirectional | Low (32-bit command/status) | < 10 cycles |
| HIVE-C → Delta | AXIS (CDA) | Master | High (256-bit descriptors) | ~10-20 cycles to RAPIDS |
| SERVs → Delta | AXIS (PKT_CONFIG/STATUS) | Master (per SERV) | Medium (128-bit) | ~10-20 cycles through Delta |
| Config Manager → routers | PKT_CONFIG broadcast | Broadcast | Low (infrequent) | < 5 cycles |

: Inter-block communication summary

---

## Resource Budget (NexysA7 100T)

**FPGA target:** Xilinx Artix-7 XC7A100T-1CSG324C — 63,400 LUTs, 126,800 FFs,
240 DSPs, 135 BRAM (36Kb) blocks.

| Component | LUTs | FFs | DSPs | BRAM (36Kb) | Notes |
|-----------|------|-----|------|-------------|-------|
| Block 1: HIVE-C Controller | 1,400 | 900 | 0 | 8 | VexRiscv "Small" config |
| Block 2: SERV Monitors (16×) | 2,000 | 2,624 | 0 | 16 | ~125 LUTs per SERV |
| Block 3: Control Network | 1,200 | 800 | 0 | 4 | HIVE-C ↔ SERV comm |
| Block 4: Configuration Manager | 1,500 | 1,200 | 0 | 2 | Virtual contexts |
| **HIVE control plane subtotal** | **6,100** | **5,524** | **0** | **30** | 9.6% LUT, 22% BRAM |
| Delta Network 4×4 mesh (16 routers) | 8,000 | 6,000 | 0 | 32 | Delta-owned; see Delta HAS |
| **HIVE + NoC total** | **14,100** | **11,524** | **0** | **62** | 22% LUT, 46% BRAM |
| Available for compute/RAPIDS | 49,300 | 115,276 | 240 | 73 | Remaining resources |

: Resource budget, NexysA7 100T

> **Correction note (v0.1):** earlier drafts presented the 14,100-LUT subtotal
> as "HIVE" while omitting the Delta NoC row from the table — the NoC's 8,000
> LUTs / 6,000 FFs / 32 BRAMs were silently included in the subtotal. The table
> above separates the HIVE control plane (6,100 LUTs) from the Delta NoC it
> configures, then gives the combined figure. The "22% LUT / 46% BRAM"
> occupancy that motivated the PoC budget refers to the combined figure.

**Key design constraints:**
- HIVE consumes **zero DSP blocks** (all 240 available to compute)
- HIVE uses no AXI4 master of its own — it never touches DDR directly
- The combined control plane leaves **78% of logic resources** for RAPIDS and
  Delta compute elements

---

**Last Updated:** 2026-10-12
