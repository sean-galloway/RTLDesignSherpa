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

# Chapter 1.3: Clocks and Reset

## 1.3.1 Clock Domains

RAPIDS operates within a multi-clock domain system due to its integration with Delta Network and DDR memory:

### Primary Clock Domains

**1. APB Control Clock (`pclk`)**
- **Frequency:** Typically 50-100 MHz
- **Purpose:** Control/status register access by HIVE-C
- **Interface:** AXI4-Lite slave
- **Requirements:** Synchronous to HIVE-C system clock

**2. AXI4 Memory Clock (`aclk`)**
- **Frequency:** Typically 200-400 MHz (DDR2/DDR3/DDR4 dependent)
- **Purpose:** High-performance memory access
- **Interfaces:**
  - AXI4 master (read/write to DDR)
  - Internal RAPIDS core logic
- **Requirements:** Synchronous to memory controller clock

**3. Delta Network Clock (`network_clk`)**
- **Frequency:** Typically 250-500 MHz
- **Purpose:** Packet routing and network communication
- **Interfaces:**
  - AXIS CDA input (slave)
  - AXIS Data output (master)
  - AXIS Data input (slave)
- **Requirements:** Synchronous to Delta Network fabric

### Clock Domain Relationships

```
┌─────────────────────────────────────────────────────────────────┐
│                           HIVE-C                                │
│                   (Control Plane Clock)                         │
│                         50-100 MHz                              │
└──────────────────────────┬──────────────────────────────────────┘
                           │ pclk
                           ▼
              ┌────────────────────────────┐
              │   APB Control Interface    │
              │   (AXI4-Lite Slave)       │
              └────────────┬───────────────┘
                           │ CDC if async
                           ▼
┌─────────────────────────────────────────────────────────────────┐
│                        RAPIDS Core                              │
│                    (aclk - Memory Clock)                        │
│                       200-400 MHz                               │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐         │
│  │ Descriptor   │  │    MM2S      │  │    S2MM      │         │
│  │   Engine     │  │   Engine     │  │  Channels    │         │
│  └──────────────┘  └──────────────┘  └──────────────┘         │
└────────────┬────────────────┬─────────────────┬────────────────┘
             │                │                 │
             ▼                ▼                 ▼
    ┌────────────────┐  ┌─────────────┐  ┌─────────────┐
    │ AXI4 Memory    │  │  CDC FIFO   │  │  CDC FIFO   │
    │   Interface    │  │  MM2S→AXIS  │  │  AXIS→S2MM  │
    │ (aclk domain)  │  └──────┬──────┘  └──────┬──────┘
    └────────┬───────┘         │ CDC            │ CDC
             │                 ▼                 ▼
             ▼         ┌───────────────────────────────────┐
    ┌────────────┐    │      Delta Network               │
    │    DDR     │    │   (network_clk - 250-500 MHz)    │
    │  Memory    │    │                                   │
    └────────────┘    │  AXIS TX (PKT_DATA)              │
                      │  AXIS RX (PKT_DATA)              │
                      │  AXIS CDA (descriptors)          │
                      └───────────────────────────────────┘
```

## 1.3.2 Clock Domain Crossing (CDC)

### CDC Requirements

RAPIDS requires CDC for these interface crossings:

**1. APB ↔ Core (Optional)**
- **When:** If HIVE-C APB clock differs from RAPIDS core clock
- **Method:** APB slave CDC (handshake synchronization)
- **Latency Impact:** 4-6 clock cycles for register access
- **Parameter:** `CDC_ENABLE` (0=synchronous, 1=async)

**2. Core ↔ Delta Network (Typical)**
- **Crossing:** `aclk` (memory) ↔ `network_clk` (Delta Network)
- **Method:** Asynchronous FIFOs with gray-coded pointers
- **Locations:**
  - MM2S data FIFO (memory → network)
  - S2MM data FIFOs (network → memory, per-channel)
  - CDA descriptor FIFO (network → core)
- **Depth:** Minimum 32 entries to absorb clock ratio variations

**3. Core ↔ Memory (Synchronous)**
- **Assumption:** RAPIDS core runs at memory clock (`aclk`)
- **No CDC Required:** Direct AXI4 connection
- **Benefit:** Lowest latency for memory access

### CDC FIFO Specifications

**MM2S Data FIFO:**
```
Write Side: aclk (RAPIDS core)
Read Side: network_clk (Delta Network)
Depth: 512 entries × DATA_WIDTH
Empty/Full: Gray-coded flags with multi-stage synchronization
```

**S2MM Data FIFO (per channel):**
```
Write Side: network_clk (Delta Network)
Read Side: aclk (RAPIDS core)
Depth: 32 entries × DATA_WIDTH
Empty/Full: Gray-coded flags with multi-stage synchronization
```

**CDA Descriptor FIFO:**
```
Write Side: network_clk (Delta Network CDA packets)
Read Side: aclk (RAPIDS descriptor processing)
Depth: 8 descriptors × 256 bits
Empty/Full: Gray-coded flags with multi-stage synchronization
```

## 1.3.3 Reset Strategy

### Reset Signals

RAPIDS uses **synchronous active-low reset** for all clock domains:

**1. APB Reset (`presetn`)**
- **Domain:** APB control interface
- **Type:** Active-low synchronous
- **Source:** HIVE-C system reset
- **Scope:** APB slave interface only

**2. Core Reset (`aresetn`)**
- **Domain:** RAPIDS core logic + AXI4 memory interface
- **Type:** Active-low synchronous (AXI4 standard)
- **Source:** System reset
- **Scope:** All RAPIDS internal state, descriptor engine, scheduler, data paths

**3. Network Reset (`network_rst_n`)**
- **Domain:** Delta Network interfaces (AXIS)
- **Type:** Active-low synchronous
- **Source:** Delta Network fabric reset
- **Scope:** AXIS interfaces, CDC FIFOs (network side)

### Reset Sequencing

Recommended power-on reset sequence:

```
1. Assert all resets (presetn=0, aresetn=0, network_rst_n=0)
   - Hold for minimum 10 cycles in slowest domain

2. Deassert network_rst_n (Delta Network reset)
   - Allow Delta Network fabric to initialize
   - Wait 100 cycles (network_clk)

3. Deassert aresetn (RAPIDS core reset)
   - RAPIDS core initializes
   - CDC FIFOs reset
   - Wait 50 cycles (aclk)

4. Deassert presetn (APB control reset)
   - APB interface ready
   - HIVE-C can access control registers

5. Software initialization
   - HIVE-C configures RAPIDS via APB
   - Enable engines, set initial credits
```

### Reset Requirements

**RI-1: Synchronous Reset**
- All reset signals synchronized to respective clock domains
- No asynchronous reset (metastability risk)

**RI-2: Graceful Reset**
- RAPIDS completes in-flight AXI4 transactions before internal reset (when possible)
- CDC FIFOs flushed cleanly (no partial packets)

**RI-3: FIFO Flush**
- Selective FIFO flushing via control register:
  - Descriptor FIFO flush
  - MM2S data FIFO flush
  - S2MM data FIFO flush (per-channel)

**RI-4: Initialization State**

After reset deassertion, RAPIDS guarantees:
- ✅ All FIFOs empty
- ✅ All engines disabled (MM2S, S2MM channels)
- ✅ All error flags cleared
- ✅ Performance counters reset to 0
- ✅ Descriptor queue empty
- ✅ AXI4 interfaces idle

## 1.3.4 Clock Constraints

### Frequency Relationships

**Minimum Ratios:**
- `network_clk` : `aclk` ≥ 1:1 (network can be slower, same, or faster)
- `aclk` : `pclk` ≥ 2:1 (core typically 2-4× faster than APB)

**Recommended:**
- `pclk` = 50-100 MHz (APB control)
- `aclk` = 200-400 MHz (DDR3/DDR4 memory)
- `network_clk` = 250-500 MHz (Delta Network fabric)

**CDC FIFO Sizing:**
- For `network_clk` : `aclk` = 2:1 (network faster): Larger write-side headroom
- For `network_clk` : `aclk` = 1:2 (memory faster): Larger read-side headroom

### Jitter and Skew

**Clock Jitter Tolerance:**
- ±100 ps peak-to-peak jitter (typical for on-chip PLLs)
- CDC FIFOs absorb jitter via async crossing

**Clock Skew:**
- Same-domain: <200 ps (within RAPIDS core on `aclk`)
- Cross-domain: Not applicable (async FIFOs tolerate arbitrary skew)

## 1.3.5 Power Management (Optional)

**Clock Gating:**
- Individual engine clock gating when disabled
- Descriptor engine clock gated when queue empty
- S2MM channel clock gating when inactive

**Power Domains:**
- Core domain: aclk (always on during operation)
- Control domain: pclk (can be gated when HIVE-C idle)
- Network domain: network_clk (controlled by Delta Network fabric)

---

**Next:** [Acronyms](04_acronyms.md)

**Previous:** [Architectural Requirements](02_architectural_requirements.md)

**Back to:** [Index](../rapids_index.md)
