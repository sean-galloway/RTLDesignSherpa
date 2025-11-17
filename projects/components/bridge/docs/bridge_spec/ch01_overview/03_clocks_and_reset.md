### Bridge - Clocks and Reset

#### Overview

The Bridge component operates in a **single clock domain** by default, using a single AXI4-compatible clock (`aclk`) and active-low asynchronous reset (`aresetn`). This chapter describes clock domain strategies, reset behavior, timing requirements, and future CDC (Clock Domain Crossing) support.

**Default Configuration:** Single clock, simplest integration, lowest latency.

---

#### Clock Domains

**Default: Single Clock Domain**

```systemverilog
module bridge_top (
    input  logic        aclk,          // AXI4 clock
    input  logic        aresetn,       // AXI4 active-low reset
    
    // All master interfaces
    input  logic [3:0]  cpu_m_axi_awid,
    // ... all masters use aclk
    
    // All slave interfaces  
    output logic [3:0]  ddr_s_axi_awid,
    // ... all slaves use aclk
);

    // All internal logic synchronous to aclk
    // - Adapters
    // - Crossbar
    // - Arbiters
    // - CAMs
    // - Skid buffers
```

**Key Properties:**
- **Latency:** Minimal (2-3 cycles)
- **Complexity:** Simple, no CDC logic
- **Use Case:** All masters and slaves in same clock domain
- **Fmax:** 300-400 MHz (typical on UltraScale+)

---

#### Clock Signal Specifications

**Primary Clock: `aclk`**

| Parameter | Specification | Notes |
|-----------|---------------|-------|
| **Name** | `aclk` | AXI4 standard naming |
| **Type** | Single-ended | No differential clock support |
| **Frequency** | 50 MHz - 500 MHz | Typical: 200-400 MHz |
| **Duty Cycle** | 50% ± 5% | Standard requirement |
| **Jitter** | < 100 ps | For high-frequency operation |
| **Domain** | Global | All bridge logic shares this clock |

**Clock Routing Recommendations:**
- Use dedicated clock buffers (BUFG on Xilinx)
- Minimize clock skew across large designs
- Consider clock tree synthesis for >200 MHz
- Monitor clock utilization in synthesis reports

---

#### Reset Signal Specifications

**Primary Reset: `aresetn`**

| Parameter | Specification | Notes |
|-----------|---------------|-------|
| **Name** | `aresetn` | AXI4 standard naming |
| **Polarity** | Active-low | Reset when `aresetn = 0` |
| **Type** | Asynchronous assert | Can assert anytime |
|  | Synchronous de-assert | Must de-assert on clock edge |
| **Duration** | ≥ 10 clock cycles | Minimum reset assertion |
| **Edge** | De-assert on rising edge | Synchronized to `aclk` |

**Reset Behavior:**

```systemverilog
always_ff @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        // Async reset - enters immediately
        state <= IDLE;
        counter <= '0;
        valid_reg <= 1'b0;
    end else begin
        // Normal operation - synchronous to aclk
        // ...
    end
end
```

---

#### Reset Sequence

**Recommended Reset Sequence:**

```
1. Assert aresetn = 0
   ├─ All registers clear to reset values
   ├─ Arbiters reset to master 0 priority
   ├─ CAMs flush all entries
   └─ Skid buffers empty

2. Hold for ≥10 clock cycles
   └─ Ensure all flip-flops have settled

3. De-assert aresetn = 1 (on rising aclk edge)
   └─ Synchronized release across all logic

4. Wait 2-3 cycles
   └─ Allow internal state machines to initialize

5. Bridge ready for transactions
   └─ All *_ready signals now respond correctly
```

**Timing Diagram:**

```
aclk:     __|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_
aresetn:  ________|‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
          <reset> <─ 10 cycles ─><ready>
Internal: XXXXX    RESET STATE    IDLE  → READY
```

---

#### Reset State Values

**All Registers Reset To:**

| Component | Register | Reset Value | Purpose |
|-----------|----------|-------------|---------|
| **Adapters** | Address decoder | Inactive | No slave selected |
|  | Valid/ready regs | 0 | No transactions |
|  | Width converter | 0 | Counter cleared |
| **Crossbar** | Arbiter grant | Master 0 | Deterministic start |
|  | Arbiter priority | 0 | Reset to first master |
|  | Mux select | 0 | Default select |
| **CAMs** | All entries | Invalid | No active transactions |
|  | Entry valid bits | 0 | All entries free |
| **Skid Buffers** | Data registers | 0 (or X) | Empty state |
|  | Valid bits | 0 | No stored data |
|  | Count | 0 | Buffer empty |

**Post-Reset Verification:**
```systemverilog
// After reset, bridge should be in known state:
assert property (@(posedge aclk) $rose(aresetn) |-> ##3 bridge_idle);

// All arbiters should grant master 0 initially
assert property (@(posedge aclk) $rose(aresetn) |-> ##2 (ar_grant[DDR] == 3'b001));
```

---

#### Clock Frequency Recommendations

**By Bridge Configuration:**

| Configuration | Masters×Slaves | Recommended Fmax | Notes |
|---------------|----------------|------------------|-------|
| **Small** | 2×2, 4×4 | 400+ MHz | Minimal logic depth |
| **Medium** | 8×8, 16×16 | 300-350 MHz | May need skid buffers |
| **Large** | 32×256 | 250-300 MHz | Requires pipeline stages |

**By FPGA Family:**

| FPGA | Typical Fmax | Optimization Notes |
|------|-------------|-------------------|
| **Xilinx UltraScale+** | 400 MHz | Use BUFGCE for clock gating |
| **Xilinx 7-Series** | 300 MHz | Consider pipeline stages |
| **Intel Stratix 10** | 450 MHz | Excellent for crossbars |
| **Intel Cyclone V** | 250 MHz | May need relaxed timing |

**Fmax Optimization:**
- Add skid buffers to break combinatorial paths
- Register arbiter outputs (+1 cycle latency)
- Pipeline address decode for large slave counts
- See Chapter 6: Performance for deep pipeline options

---

#### Multiple Clock Domain Support (Future)

**Planned Enhancement: Optional CDC**

```systemverilog
module bridge_top #(
    parameter CDC_ENABLE = 0    // 0=single clock, 1=CDC enabled
)(
    // Master-side clock domain
    input  logic        master_aclk,
    input  logic        master_aresetn,
    
    // Slave-side clock domain (if CDC_ENABLE=1)
    input  logic        slave_aclk,
    input  logic        slave_aresetn,
    
    // Master interfaces (master_aclk domain)
    input  logic [3:0]  cpu_m_axi_awid,
    // ...
    
    // Slave interfaces (slave_aclk domain if CDC_ENABLE=1)
    output logic [3:0]  ddr_s_axi_awid,
    // ...
);
```

**CDC Strategy (When Implemented):**

```
Master Domain (fast)     CDC Boundary        Slave Domain (slow)
====================     ============        ===================

Masters → Adapters       AsyncFIFO per       Slave Logic
                         AXI channel
         
         aclk=400MHz     ←→ Gray code    ←→  aclk=200MHz
                            counters
                            Handshake
```

**CDC Specifications (Future):**
- Handshake-based synchronization
- Independent clock frequencies
- Gray code counters for pointer crossing
- 2-4 cycle latency penalty
- Configurable FIFO depth per channel

**Use Cases for CDC:**
- Fast CPU clock, slow memory clock
- Independent peripheral clock domains
- Power-optimized slave domains
- Legacy IP with fixed clocks

**Status:** CDC support is planned but not yet implemented. Current version requires single clock domain.

---

#### Clock Domain Crossing Considerations

**If You Need CDC Today:**

Use external CDC components between bridge and slaves:

```systemverilog
// Bridge in fast domain
bridge_top u_bridge (
    .aclk       (fast_clk),      // 400 MHz
    .aresetn    (fast_rst_n),
    // ... master interfaces (fast_clk)
    // ... slave interfaces output (fast_clk)
    .ddr_s_axi_*(ddr_fast_*),    // Fast clock domain
);

// External CDC FIFO
axi_async_fifo u_cdc (
    .s_aclk     (fast_clk),
    .s_aresetn  (fast_rst_n),
    .s_axi_*    (ddr_fast_*),    // From bridge
    
    .m_aclk     (slow_clk),      // 200 MHz
    .m_aresetn  (slow_rst_n),
    .m_axi_*    (ddr_slow_*),    // To DDR controller
);

// DDR controller in slow domain
ddr_controller u_ddr (
    .clk        (slow_clk),
    .rst_n      (slow_rst_n),
    .s_axi_*    (ddr_slow_*),
);
```

**Available CDC Components:**
- Xilinx AXI4 Clock Converter IP
- Intel Avalon Clock Crossing Bridge
- Custom async FIFO with AXI4 wrappers

---

#### Power Considerations

**Clock Gating (Future Enhancement):**

```systemverilog
// Per-adapter clock gating (not yet implemented)
logic cpu_adapter_clk_en;
assign cpu_adapter_clk_en = cpu_m_axi_arvalid | 
                            cpu_m_axi_awvalid | 
                            internal_busy;

BUFGCE cpu_clk_gate (
    .I(aclk),
    .CE(cpu_adapter_clk_en),
    .O(cpu_adapter_gated_clk)
);
```

**Dynamic Voltage and Frequency Scaling (DVFS):**
- Not currently supported
- Would require CDC between domains
- Future consideration for low-power designs

---

#### Timing Constraints (SDC Example)

**For Synthesis:**

```tcl
# Create primary clock
create_clock -period 2.500 -name aclk [get_ports aclk]

# Set input delay (relative to aclk)
set_input_delay -clock aclk -max 0.500 [get_ports {*_m_axi_*}]
set_input_delay -clock aclk -min 0.100 [get_ports {*_m_axi_*}]

# Set output delay (relative to aclk)
set_output_delay -clock aclk -max 0.500 [get_ports {*_s_axi_*}]
set_output_delay -clock aclk -min 0.100 [get_ports {*_s_axi_*}]

# Reset is asynchronous
set_false_path -from [get_ports aresetn]

# Multicycle paths (if using pipeline stages)
set_multicycle_path -setup 2 -through [get_pins -hier *_skid_*]
set_multicycle_path -hold 1 -through [get_pins -hier *_skid_*]
```

---

#### Clock Quality Requirements

**For Reliable Operation:**

| Metric | Requirement | Impact if Violated |
|--------|-------------|-------------------|
| **Jitter** | < 100 ps RMS | Timing violations, data corruption |
| **Duty Cycle** | 45%-55% | Setup/hold issues |
| **Skew** | < 200 ps | Metastability risk |
| **Frequency Accuracy** | ± 100 ppm | Generally not critical for logic |

**Clock Source Recommendations:**
- PLL-generated clocks (most FPGA designs)
- Crystal oscillator (for standalone systems)
- Clock from  master IP (if AXI master provides clock)

---

#### Reset Distribution

**Synchronizer for Asynchronous Reset:**

```systemverilog
// Reset synchronizer (good practice)
logic aresetn_sync_1, aresetn_sync_2;

always_ff @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        aresetn_sync_1 <= 1'b0;
        aresetn_sync_2 <= 1'b0;
    end else begin
        aresetn_sync_1 <= 1'b1;
        aresetn_sync_2 <= aresetn_sync_1;
    end
end

// Use synchronized reset throughout design
wire aresetn_internal = aresetn_sync_2;
```

**Why Synchronize?**
- Prevents metastability on reset de-assertion
- Ensures all flops see same reset release time
- Required for proper operation at high frequencies

**Reset Tree Considerations:**
- Use reset buffers for large designs
- Minimize reset fanout (< 10K flops per driver)
- Consider hierarchical reset trees

---

#### Debugging Clock and Reset Issues

**Common Problems:**

**Problem 1: Bridge Not Responding After Reset**
```
Symptoms: *_ready signals stay low
Check: 
  - Reset held for ≥10 cycles?
  - aresetn synchronized to aclk edge?
  - Clock actually toggling (scope)?
```

**Problem 2: Random Data Corruption**
```
Symptoms: Intermittent errors, not reproducible
Check:
  - Clock jitter (should be <100ps)
  - Clock duty cycle (should be 45-55%)
  - Timing violations (setup/hold)
  - CDC issues if using multiple clocks
```

**Problem 3: Synthesis Timing Violations**
```
Symptoms: Synth reports failing paths
Solutions:
  - Reduce target Fmax
  - Add pipeline stages (skid buffers)
  - See Chapter 6: Performance
```

---

#### Clock and Reset Checklist

Before integration:

- [ ] Single clock source (`aclk`) connected to all bridge logic
- [ ] Clock frequency within recommended range
- [ ] Clock duty cycle 45-55%
- [ ] Reset signal (`aresetn`) is active-low
- [ ] Reset held for ≥10 cycles
- [ ] Reset de-asserted synchronously (on aclk rising edge)
- [ ] Reset synchronizer implemented (recommended)
- [ ] Timing constraints applied (SDC file)
- [ ] No clock domain crossings (or external CDC FIFOs used)
- [ ] Post-synthesis timing clean (no violations)

---

#### Future Enhancements

**Planned:**
- Native CDC support (CDC_ENABLE parameter)
- Per-adapter clock gating for power
- Multiple slave clock domains
- Automatic clock relationship constraints

**Under Consideration:**
- DVFS support
- Clock monitoring/failover
- Asynchronous reset removal (fully synchronous design)

---

**Next:** [Chapter 1.4 - Acronyms](04_acronyms.md)
