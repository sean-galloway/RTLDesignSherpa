# Chapter 1.3: Clocks and Reset

## 1.3.1 Clock Domains

HIVE system operates across multiple clock domains to optimize power and performance for different subsystems.

### Primary Clock Domains

**Domain 1: HIVE-C Controller (hive_c_clk)**
- **Frequency:** 100 MHz (proof of concept), 150+ MHz (optimized)
- **Source:** VexRiscv master controller clock
- **Components:**
  - VexRiscv processor core
  - Instruction and data memory
  - Descriptor generation logic
  - Control network master interface
  - AXIS master for CDA packet injection

**Domain 2: SERV Monitors (serv_clk)**
- **Frequency:** 50-100 MHz
- **Source:** Shared clock for all 16 SERV monitors
- **Components:**
  - SERV RISC-V cores (16 instances)
  - Traffic counters and trigger logic
  - Control network slave interfaces
  - AXIS packet injection FIFOs

**Domain 3: Delta Network (delta_clk)**
- **Frequency:** 100 MHz (synchronized with HIVE-C or independent)
- **Source:** Delta Network mesh router clock
- **Components:**
  - Network routers (16 routers in 4×4 mesh)
  - Router buffers and flow control
  - Network interfaces
  - Configuration registers

**Domain 4: Host Interface (host_clk)**
- **Frequency:** Variable (typically 50-100 MHz)
- **Source:** External host system clock
- **Components:**
  - UART receiver/transmitter
  - AXI4-Lite slave interface
  - Command parser and response generator

---

## 1.3.2 Clock Domain Crossing (CDC)

### CDC Strategy

HIVE implements robust clock domain crossing using standard techniques:

#### HIVE-C ↔ Delta Network
```
hive_c_clk → delta_clk
  Method: Asynchronous FIFO (dual-clock FIFO)
  Width: 256 bits (CDA packet)
  Depth: 8 entries
  Handshake: AXIS valid/ready protocol with CDC

delta_clk → hive_c_clk
  Method: Asynchronous FIFO (PKT_STATUS packets)
  Width: 128 bits (status packet)
  Depth: 16 entries (aggregate from 16 SERV monitors)
  Handshake: AXIS valid/ready protocol with CDC
```

#### SERV Monitors ↔ Delta Network
```
serv_clk → delta_clk
  Method: Asynchronous FIFO per SERV monitor
  Width: 128 bits (PKT_CONFIG, PKT_STATUS)
  Depth: 4 entries per monitor
  Handshake: AXIS valid/ready protocol with CDC

delta_clk → serv_clk
  Method: Asynchronous FIFO per SERV monitor
  Width: 128 bits (PKT_CONFIG from HIVE-C)
  Depth: 4 entries per monitor
  Handshake: AXIS valid/ready protocol with CDC
```

#### Host Interface ↔ HIVE-C
```
host_clk → hive_c_clk
  Method: Dual-clock synchronizer for control signals
  Method: Asynchronous FIFO for data transfers (AXI4-Lite)
  Width: 32 bits (AXI4-Lite data width)
  Depth: 8 entries
  Handshake: AXI4-Lite protocol with CDC
```

#### Control Network (HIVE-C ↔ SERV)
```
hive_c_clk → serv_clk
  Method: Dedicated control network with asynchronous handshaking
  Width: 32 bits (control commands)
  Depth: 2 entries per SERV monitor (low bandwidth)

serv_clk → hive_c_clk
  Method: Round-robin arbiter with asynchronous FIFOs
  Width: 32 bits (status responses)
  Depth: 4 entries per SERV monitor
```

### CDC Implementation Guidelines

**Rule 1: Never Cross Clock Domains with Combinational Logic**
- All CDC paths must use registered signals
- Asynchronous FIFOs for data transfer
- Dual-flop synchronizers for control signals

**Rule 2: AXIS Protocol Across CDC**
- Use standard AXI-Stream async FIFO IP
- Gray-coded pointers for FIFO full/empty generation
- Minimum FIFO depth: 4 entries (prevent underflow/overflow)

**Rule 3: Metastability Protection**
- Two-stage synchronizers for all control signals
- Three-stage synchronizers for critical paths
- MTBF analysis for high-reliability requirements

**Rule 4: Reset Synchronization**
- Reset assertions asynchronous
- Reset deassertion synchronized to destination clock domain

---

## 1.3.3 Reset Architecture

### Reset Strategy

HIVE implements a hierarchical reset architecture with multiple reset domains.

#### Global Reset (system_rst_n)
- **Type:** Active-low asynchronous assertion, synchronous deassertion
- **Source:** External reset input (from FPGA reset pin or host)
- **Scope:** All clock domains
- **Duration:** Minimum 16 cycles at slowest clock frequency (serv_clk)

#### Domain-Specific Resets

**HIVE-C Reset (hive_c_rst_n)**
- **Source:** Synchronized from system_rst_n to hive_c_clk
- **Scope:** VexRiscv controller, instruction/data memory, control network master
- **Special:** Memory initialization required after reset

**SERV Resets (serv_rst_n[15:0])**
- **Source:** Synchronized from system_rst_n to serv_clk, independently controllable
- **Scope:** Individual SERV monitors (16 independent resets)
- **Special:** Allows selective SERV monitor reset without affecting system
- **Use Case:** Debug, reconfiguration, error recovery

**Delta Network Reset (delta_rst_n)**
- **Source:** Synchronized from system_rst_n to delta_clk
- **Scope:** All routers, network interfaces, configuration logic
- **Special:** Must drain in-flight packets before asserting router resets

**Host Interface Reset (host_rst_n)**
- **Source:** Synchronized from system_rst_n to host_clk
- **Scope:** UART, AXI4-Lite slave, command parser
- **Special:** Asynchronous to HIVE-C, requires handshake for commands

### Reset Sequencing

```
Reset Assertion (Global)
1. system_rst_n asserted (external signal)
2. All domain resets assert asynchronously
3. All state machines enter IDLE/RESET states
4. FIFOs flush (pointers reset to 0)
5. Configuration registers hold reset values

Reset Deassertion (Staged)
1. system_rst_n deasserted (external signal)
2. Synchronize to each clock domain (2-cycle delay per domain)
3. Domain resets deassert in order:
   a. Host Interface (host_rst_n)  ← First
   b. HIVE-C Controller (hive_c_rst_n)
   c. Delta Network (delta_rst_n)
   d. SERV Monitors (serv_rst_n[15:0])  ← Last
4. Initialization sequence begins:
   a. HIVE-C loads firmware from instruction memory
   b. Delta Network enters default routing context (Context 0)
   c. SERV monitors enter monitoring mode
5. System ready after ~100 cycles (at slowest clock)
```

### Soft Reset Capability

HIVE supports selective soft resets via configuration registers:

**Soft Reset Register (offset 0x0000 in config space)**
```
Bits [31:16] - SERV Reset Mask (one bit per SERV monitor)
Bit  [8]     - Delta Network Soft Reset
Bit  [4]     - Control Network Soft Reset
Bit  [0]     - HIVE-C Soft Reset (use with caution!)

Write 1 to assert soft reset, write 0 to deassert
Soft resets are synchronous to component clock domains
```

**Soft Reset Use Cases:**
- **SERV monitor hang recovery:** Reset individual SERV without system disruption
- **Network reconfiguration:** Soft reset Delta Network to clear state
- **Debug:** Reset specific components while maintaining system visibility

---

## 1.3.4 Reset Synchronizers

### Synchronizer Implementation

All reset synchronizers follow this pattern:

```systemverilog
// Reset synchronizer: Asynchronous assertion, synchronous deassertion
module reset_synchronizer (
    input  logic clk,           // Destination clock domain
    input  logic async_rst_n,   // Asynchronous reset input
    output logic sync_rst_n     // Synchronized reset output
);

    logic [1:0] sync_chain;

    // Asynchronous assertion, synchronous deassertion
    always_ff @(posedge clk or negedge async_rst_n) begin
        if (!async_rst_n) begin
            sync_chain <= 2'b00;
        end else begin
            sync_chain <= {sync_chain[0], 1'b1};
        end
    end

    assign sync_rst_n = sync_chain[1];

endmodule
```

**Key Properties:**
- Reset assertion: Immediate (asynchronous)
- Reset deassertion: 2 clock cycles (synchronous)
- Metastability protection: 2-stage synchronizer
- Reset duration: Guaranteed ≥ 2 destination clocks

---

## 1.3.5 Clock Gating (Optional Optimization)

### Power Optimization

For power-constrained designs, HIVE supports clock gating:

**SERV Monitor Clock Gating**
- **Condition:** SERV idle (no monitoring activity)
- **Savings:** ~5% total system power (SERV monitors ~20% of logic)
- **Latency:** 1-2 cycle wake-up when monitoring needed

**Delta Network Router Clock Gating**
- **Condition:** Tile disabled via configuration
- **Savings:** ~10% total system power (disabled tiles)
- **Latency:** Context switch to re-enable

**HIVE-C Clock Gating**
- **Condition:** Not recommended (always active)
- **Rationale:** HIVE-C must remain responsive for interrupts

---

## 1.3.6 Clock Distribution

### On-FPGA Clock Distribution

**Primary Clocks:**
- Use global clock buffers (BUFG on Xilinx)
- Low skew across die
- Dedicated clock routing resources

**Derived Clocks:**
- Generate from PLLs/MMCMs for frequency scaling
- Phase-locked for deterministic relationships
- Jitter requirements: < 100ps (typical FPGA capability)

**Clock Tree:**
```
External Clock Input (100 MHz)
  ├─ BUFG → hive_c_clk (100 MHz or PLL to 150 MHz)
  ├─ BUFG → delta_clk (100 MHz)
  ├─ PLL → serv_clk (50 MHz or 100 MHz, configurable)
  └─ BUFG → host_clk (external, typically 50-100 MHz)
```

---

**Next:** [Acronyms](04_acronyms.md)

**Back to:** [Index](../hive_index.md) | [Architectural Requirements](02_architectural_requirements.md)
