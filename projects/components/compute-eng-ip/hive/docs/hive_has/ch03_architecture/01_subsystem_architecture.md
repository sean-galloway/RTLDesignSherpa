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
| Frequency | 75 MHz, the HIVE target for every domain (owner, 2026-11-25) |
| Memory | 32 KB tightly-coupled I-mem + 32 KB tightly-coupled D-mem (BRAM) |
| External interfaces | UART/AXI4-Lite slave (host), AXIS master (CDA injection), control network master (engine monitor) |

: HIVE-C key specifications

**Responsibilities:**
1. Parse high-level transfer commands from the host
2. Generate RAPIDS DMA descriptors (256-bit CDA packets)
3. Inject descriptors into Delta via AXIS (TUSER=2'b01, TDEST=16)
4. Aggregate traffic statistics from the four engine-monitor contexts
5. Manage network reconfiguration sequences
6. Handle interrupt routing and exception processing

**Performance targets:** descriptor injection < 30 cycles (HIVE-C → RAPIDS);
command response < 1 µs @ 75 MHz (75 cycles); status aggregation over all four engines < 100 cycles.

---

## Block 2: Engine Monitor (one gatling, four contexts)

One gatling core monitors the four compute engines. gatling
(`projects/components/riscv-ip/gatling-rv32i`) is a 4-context barrel RV32I:
its contexts take turns, one pipeline step each, so each context retires
one instruction every four cycles and the core retires one per cycle while
all four run. Context *n* monitors compute engine *n*. This replaces the
v0.2 design of sixteen SERV bit-serial cores, one per tile of a 4x4 mesh
(owner, 2026-11-25).

**Key specifications:**

| Attribute | Value |
|-----------|-------|
| Core | gatling (`gatling_core` + `gatling_mem_bram`) |
| ISA | RV32I; no CSRs (every CSR reads 0), no interrupts, no trap vector |
| Contexts | 4, strict rotation; context *n* monitors engine *n* |
| Throughput | 1 instruction per 4 cycles per context (18.75 MIPS per engine at 75 MHz) |
| Frequency | 75 MHz, HIVE's target (gatling's own board build closes at 100 MHz on the Nexys A7) |
| Memory | one private program/data bank per context, 4 KB each (`MEM_WORDS=1024`), loaded and started per context over the bank's AXI4-Lite port |
| Resources | about 1,900 LUTs (core 1,066 + memory 799, gatling board build), 5 BRAM at 4 KB per context |
| Interfaces | per engine: control-network slave (from HIVE-C), AXIS master (PKT_CONFIG/PKT_STATUS), router monitoring tap |

: Engine monitor key specifications

**Per-engine peripherals.** Each engine keeps the peripheral set the SERV
design had: `traffic_counter`, `trigger_logic`, `axis_injector` and
`ctrl_net_slave` (`rtl/engine_monitor/`). gatling's data port carries the
issuing context (`dmem_ctx`), so the monitor top routes a context's
accesses to the peripheral window to that context's engine. All four
contexts run the same firmware image and each sees its own engine's
peripherals at the same addresses, which keeps gatling's rule that binaries
are uniform (gatling PRD §7 item 2).

**Responsibilities (per engine, per context):**
1. Monitor the engine's router traffic (packet counts, buffer occupancy)
2. Detect congestion and anomalies against programmable thresholds
3. Generate inband control packets on trigger conditions
4. Inject configuration updates into the engine's tile
5. Report statistics to HIVE-C via the control network
6. Support debug/trace packet injection

gatling has no interrupts, so firmware polls the trigger flags;
`trigger_logic` detects congestion in hardware, so the detection budget does
not depend on the core. A trap halts only its own context (gatling's
context-lock); the other three engines stay monitored.

**Monitored metrics (exposed to firmware, per engine):**
- Counters (32-bit, wrapping): `pkt_rx_count[4]`, `pkt_tx_count[4]` (per
  direction N/S/E/W), `pkt_local_inject`, `pkt_local_consume`,
  `buffer_overflow_count`, `stall_cycles`
- Real-time: `buffer_occupancy[4]` (8-bit per direction), `congestion_flag`,
  `error_flags` (parity, protocol violations)

**Performance targets:** monitoring overhead < 5% of compute-engine time;
congestion detection < 10 cycles; periodic reporting interval 1000 cycles
(configurable), timed on the `TIME` register, which reads the Ocelus time
base (the monitor's local timer now, the global usync timer once
rtl/amba/monitors TASK-005 lands).

---

## Block 3: Control Network

Dedicated low-bandwidth infrastructure for HIVE-C ↔ engine-monitor command and status
exchange. Deliberately separate from the Delta data path: control traffic must
not contend with compute traffic, and must remain live during data-plane
quiesce.

| Attribute | Value |
|-----------|-------|
| Topology | Star (HIVE-C master, 4 slave ports, one per engine) |
| Data width | 32 bits (commands and status responses) |
| Arbitration | Round-robin (engine → HIVE-C uplink) |
| Protocol | Valid/ready handshake, in-order, lossless |

: Control network key specifications

**Responsibilities:**
1. Deliver control commands from HIVE-C to an individual engine's monitor
2. Aggregate status reports from the four engines to HIVE-C
3. Provide reliable, in-order delivery (no packet loss)
4. Prioritize urgent alerts over periodic statistics

**Communication patterns:**
- HIVE-C → engine (multicast or unicast): configuration commands, threshold
  updates, firmware control (soft reset, debug mode)
- Engine → HIVE-C (uplink): periodic statistics (every 1000 cycles), congestion
  alerts (immediate), error notifications

**Performance targets:** command delivery < 10 cycles; status aggregation
< 20 cycles across all four engines; round-robin fairness (no engine starved).

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
| 2 | Tree reduction | Hierarchical aggregation over the 2x2 mesh; the root and tree edges come from the context's routing table (the v0.2 4x4 tree, rooted at tiles 12-15, no longer applies) |
| 3 | Custom/debug | User-programmable routing tables; per-tile independent configuration |

: Virtual configuration contexts

**Responsibilities:**
1. Store multiple virtual configuration contexts
2. Coordinate atomic topology switching across all four engines' routers
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
| HIVE-C ↔ engine monitor | Control Network | Bidirectional | Low (32-bit command/status) | < 10 cycles |
| HIVE-C → Delta | AXIS (CDA) | Master | High (256-bit descriptors) | ~10-20 cycles to RAPIDS |
| Engine monitor → Delta | AXIS (PKT_CONFIG/STATUS) | Master (per engine) | Medium (128-bit) | ~10-20 cycles through Delta |
| Config Manager → routers | PKT_CONFIG broadcast | Broadcast | Low (infrequent) | < 5 cycles |

: Inter-block communication summary

---

## Resource Budget (NexysA7 100T)

**FPGA target:** Xilinx Artix-7 XC7A100T-1CSG324C — 63,400 LUTs, 126,800 FFs,
240 DSPs, 135 BRAM (36Kb) blocks.

| Component | LUTs | FFs | DSPs | BRAM (36Kb) | Notes |
|-----------|------|-----|------|-------------|-------|
| Block 1: HIVE-C Controller | 1,400 | 900 | 0 | 8 | VexRiscv "Small" config |
| Block 2: Engine Monitor (1 gatling) | 1,900 | 1,750 | 0 | 5 | gatling board build: core 1,066 + memory 799 LUTs; FFs bounded by the board top's 1,742; 4 KB per context. Per-engine peripherals not included |
| Block 3: Control Network | 300 | 200 | 0 | 1 | 4 slave ports; scaled from the 16-slave estimate |
| Block 4: Configuration Manager | 1,500 | 1,200 | 0 | 2 | Virtual contexts (v0.2 estimate, not re-derived) |
| **HIVE control plane subtotal** | **5,100** | **4,050** | **0** | **16** | 8.0% LUT, 12% BRAM |
| Delta Network 2x2 mesh (4 routers) | 2,000 | 1,500 | 0 | 8 | Delta-owned; a quarter of the 4x4 estimate; see Delta HAS |
| **HIVE + NoC total** | **7,100** | **5,550** | **0** | **24** | 11% LUT, 18% BRAM |
| Available for compute/RAPIDS | 56,300 | 121,250 | 240 | 111 | Remaining resources |

: Resource budget, NexysA7 100T

Only the gatling row is measured (the gatling board build); the others are
estimates. The v0.2 table (sixteen SERVs, a 4x4 mesh) totalled 14,100 LUTs
and 62 BRAM with the NoC.

**Key design constraints:**
- HIVE consumes **zero DSP blocks** (all 240 available to compute)
- HIVE uses no AXI4 master of its own — it never touches DDR directly
- The combined control plane leaves **89% of logic resources** for RAPIDS and
  the four compute engines

---

**Last Updated:** 2026-11-25
