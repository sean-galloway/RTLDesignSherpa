### APB HPET Top Level - System Integration

#### Overview

The `apb_hpet` module is the top-level system integration point that combines APB slave interface, configuration registers, and timer core into a complete HPET peripheral. It provides parameterized clock domain crossing (CDC) support and exposes a unified external interface.

**Top-Level Block Diagram:**

![APB HPET Top-Level Block Diagram](../assets/svg/apb_hpet.svg)

*Figure: APB HPET top-level integration showing dual clock domains (PCLK and HPET_CLK), optional CDC, configuration registers, HPET core, and interrupt outputs. [Source: assets/graphviz/apb_hpet.gv](../assets/graphviz/apb_hpet.gv) | [SVG](../assets/svg/apb_hpet.svg)*

**Key Integration Features:**
- Conditional APB slave instantiation (CDC or non-CDC)
- Clock domain management
- Parameter propagation to all child modules
- Timer interrupt aggregation
- Single-point system configuration

#### Module Hierarchy

```
apb_hpet
+-- APB Slave Interface (conditional generation)
|   +-- apb_slave (CDC_ENABLE=0)
|   |   +-- Synchronous APB protocol
|   +-- apb_slave_cdc (CDC_ENABLE=1)
|       +-- APB protocol (pclk domain)
|       +-- CDC handshake (pclk ↔ hpet_clk)
|
+-- HPET Configuration Registers
|   +-- peakrdl_to_cmdrsp (protocol adapter)
|   +-- hpet_regs (PeakRDL generated)
|   +-- Interface mapping logic
|
+-- HPET Core
    +-- 64-bit counter
    +-- Timer comparators [NUM_TIMERS]
    +-- Interrupt generation [NUM_TIMERS]
```

#### Interface Specification

##### Parameters

| Parameter | Type | Default | Range | Description |
|-----------|------|---------|-------|-------------|
| **VENDOR_ID** | int | 1 | 0-65535 | Vendor identification (read-only in HPET_ID register) |
| **REVISION_ID** | int | 1 | 0-65535 | Revision identification (read-only in HPET_ID register) |
| **NUM_TIMERS** | int | 2 | 2, 3, 8 | Number of independent timers in array |
| **CDC_ENABLE** | int | 0 | 0, 1 | Clock domain crossing: 0=synchronous, 1=asynchronous |

**Parameter Notes:**
- **VENDOR_ID** and **REVISION_ID**: Informational only, visible in HPET_CAPABILITIES register
- **NUM_TIMERS**: Must match PeakRDL generation (currently supports 2, 3, or 8)
- **CDC_ENABLE**: Critical for system integration - determines clock relationship

##### Clock and Reset - Dual Domain

| Signal Name | Type | Width | Direction | Description |
|-------------|------|-------|-----------|-------------|
| **pclk** | logic | 1 | Input | APB clock domain (always used for APB interface) |
| **presetn** | logic | 1 | Input | APB reset (active-low) |
| **hpet_clk** | logic | 1 | Input | HPET clock domain (used for timer logic) |
| **hpet_resetn** | logic | 1 | Input | HPET reset (active-low) |

**Clock Constraints:**
- **CDC_ENABLE=0:** `pclk` and `hpet_clk` must be the same or synchronous
- **CDC_ENABLE=1:** `pclk` and `hpet_clk` can be fully asynchronous

**Reset Constraints:**
- **CDC_ENABLE=0:** `presetn` and `hpet_resetn` should be asserted/deasserted together
- **CDC_ENABLE=1:** Both resets must overlap during power-on, can be independent afterward

##### APB4 Slave Interface (Low Frequency Domain)

| Signal Name | Type | Width | Direction | Description |
|-------------|------|-------|-----------|-------------|
| **s_apb_PSEL** | logic | 1 | Input | Peripheral select |
| **s_apb_PENABLE** | logic | 1 | Input | Enable signal |
| **s_apb_PREADY** | logic | 1 | Output | Ready signal |
| **s_apb_PADDR** | logic | 12 | Input | Address bus (fixed 12-bit addressing) |
| **s_apb_PWRITE** | logic | 1 | Input | Write enable (1=write, 0=read) |
| **s_apb_PWDATA** | logic | 32 | Input | Write data bus |
| **s_apb_PSTRB** | logic | 4 | Input | Write strobe (byte enables) |
| **s_apb_PPROT** | logic | 3 | Input | Protection type |
| **s_apb_PRDATA** | logic | 32 | Output | Read data bus |
| **s_apb_PSLVERR** | logic | 1 | Output | Slave error |

**Address Space:** 12-bit addressing supports up to 4KB (0x000-0xFFF)
- Global registers: 0x000-0x0FF
- Timer registers: 0x100-0x1FF (32-byte spacing per timer)
- Reserved: 0x200-0xFFF

##### Timer Interrupt Outputs (High Frequency Domain)

| Signal Name | Type | Width | Direction | Description |
|-------------|------|-------|-----------|-------------|
| **timer_irq[NUM_TIMERS-1:0]** | logic | NUM_TIMERS | Output | Per-timer interrupt outputs (active-high) |

**Interrupt Characteristics:**
- **Active-high level-sensitive**
- **One interrupt per timer** (independent)
- **Follows HPET_STATUS register** (sticky until cleared)
- **W1C clearing** (software writes 1 to HPET_STATUS to clear)

#### Internal Signal Interfaces

##### CDC Command/Response Interface

**Between APB Slave and Configuration Registers:**

```systemverilog
logic                    w_cmd_valid;
logic                    w_cmd_ready;
logic                    w_cmd_pwrite;
logic [11:0]             w_cmd_paddr;
logic [31:0]             w_cmd_pwdata;
logic [3:0]              w_cmd_pstrb;
logic [2:0]              w_cmd_pprot;

logic                    w_rsp_valid;
logic                    w_rsp_ready;
logic [31:0]             w_rsp_prdata;
logic                    w_rsp_pslverr;
```

**Clock Domain:**
- **CDC_ENABLE=0:** Runs on `pclk`
- **CDC_ENABLE=1:** Runs on `hpet_clk` (synchronized from pclk)

##### Configuration Register Interface

**Between hpet_config_regs and hpet_core:**

```systemverilog
// Global configuration
logic                    w_hpet_enable;
logic                    w_legacy_replacement;

// Counter interface
logic                    w_counter_write;
logic [63:0]             w_counter_wdata;
logic [63:0]             w_counter_rdata;

// Per-timer configuration
logic [NUM_TIMERS-1:0]   w_timer_enable;
logic [NUM_TIMERS-1:0]   w_timer_int_enable;
logic [NUM_TIMERS-1:0]   w_timer_type;
logic [NUM_TIMERS-1:0]   w_timer_size;
logic [NUM_TIMERS-1:0]   w_timer_value_set;

// Per-timer comparator (dedicated buses)
logic [NUM_TIMERS-1:0]   w_timer_comp_write;
logic [63:0]             w_timer_comp_wdata [NUM_TIMERS];
logic                    w_timer_comp_write_high;
logic [63:0]             w_timer_comp_rdata [NUM_TIMERS];

// Interrupt status
logic [NUM_TIMERS-1:0]   w_timer_int_status;
logic [NUM_TIMERS-1:0]   w_timer_int_clear;
```

#### APB Slave Conditional Generation

The top-level module uses a SystemVerilog `generate` block to conditionally instantiate the appropriate APB slave variant:

##### Non-CDC Configuration (CDC_ENABLE=0)

```systemverilog
generate
    if (CDC_ENABLE != 0) begin : g_apb_slave_cdc
        // ... CDC variant instantiation ...
    end else begin : g_apb_slave_no_cdc
        // Non-CDC version for same clock domain (pclk == hpet_clk)
        apb_slave #(
            .ADDR_WIDTH(12),
            .DATA_WIDTH(32),
            .STRB_WIDTH(4),
            .PROT_WIDTH(3)
        ) u_apb_slave (
            // Single clock domain (use pclk for both APB and cmd/rsp)
            .pclk                 (pclk),
            .presetn              (presetn),

            // APB Interface
            .s_apb_PSEL           (s_apb_PSEL),
            .s_apb_PENABLE        (s_apb_PENABLE),
            .s_apb_PREADY         (s_apb_PREADY),
            .s_apb_PADDR          (s_apb_PADDR),
            .s_apb_PWRITE         (s_apb_PWRITE),
            .s_apb_PWDATA         (s_apb_PWDATA),
            .s_apb_PSTRB          (s_apb_PSTRB),
            .s_apb_PPROT          (s_apb_PPROT),
            .s_apb_PRDATA         (s_apb_PRDATA),
            .s_apb_PSLVERR        (s_apb_PSLVERR),

            // Command Interface (same pclk domain)
            .cmd_valid            (w_cmd_valid),
            .cmd_ready            (w_cmd_ready),
            .cmd_pwrite           (w_cmd_pwrite),
            .cmd_paddr            (w_cmd_paddr),
            .cmd_pwdata           (w_cmd_pwdata),
            .cmd_pstrb            (w_cmd_pstrb),
            .cmd_pprot            (w_cmd_pprot),

            // Response Interface (same pclk domain)
            .rsp_valid            (w_rsp_valid),
            .rsp_ready            (w_rsp_ready),
            .rsp_prdata           (w_rsp_prdata),
            .rsp_pslverr          (w_rsp_pslverr)
        );
    end
endgenerate
```

**Characteristics:**
- **Latency:** 2 APB clock cycles (SETUP + ACCESS phases)
- **Clock:** Single `pclk` domain
- **Resources:** ~20 FF, ~50 LUTs

##### CDC Configuration (CDC_ENABLE=1)

```systemverilog
generate
    if (CDC_ENABLE != 0) begin : g_apb_slave_cdc
        // Clock Domain Crossing version for async clocks
        apb_slave_cdc #(
            .ADDR_WIDTH(12),
            .DATA_WIDTH(32),
            .STRB_WIDTH(4),
            .PROT_WIDTH(3),
            .DEPTH     (2)
        ) u_apb_slave_cdc (
            // APB Clock Domain
            .pclk                 (pclk),
            .presetn              (presetn),

            // HPET Clock Domain
            .aclk                 (hpet_clk),
            .aresetn              (hpet_resetn),

            // APB Interface (pclk domain)
            .s_apb_PSEL           (s_apb_PSEL),
            .s_apb_PENABLE        (s_apb_PENABLE),
            .s_apb_PREADY         (s_apb_PREADY),
            .s_apb_PADDR          (s_apb_PADDR),
            .s_apb_PWRITE         (s_apb_PWRITE),
            .s_apb_PWDATA         (s_apb_PWDATA),
            .s_apb_PSTRB          (s_apb_PSTRB),
            .s_apb_PPROT          (s_apb_PPROT),
            .s_apb_PRDATA         (s_apb_PRDATA),
            .s_apb_PSLVERR        (s_apb_PSLVERR),

            // Command Interface (hpet_clk domain)
            .cmd_valid            (w_cmd_valid),
            .cmd_ready            (w_cmd_ready),
            .cmd_pwrite           (w_cmd_pwrite),
            .cmd_paddr            (w_cmd_paddr),
            .cmd_pwdata           (w_cmd_pwdata),
            .cmd_pstrb            (w_cmd_pstrb),
            .cmd_pprot            (w_cmd_pprot),

            // Response Interface (hpet_clk domain)
            .rsp_valid            (w_rsp_valid),
            .rsp_ready            (w_rsp_ready),
            .rsp_prdata           (w_rsp_prdata),
            .rsp_pslverr          (w_rsp_pslverr)
        );
    end else begin : g_apb_slave_no_cdc
        // ... non-CDC variant instantiation ...
    end
endgenerate
```

**Characteristics:**
- **Latency:** 4-6 APB clock cycles (CDC handshake overhead)
- **Clocks:** Dual domains (pclk and hpet_clk)
- **Resources:** ~100 FF, ~150 LUTs (additional CDC logic)

#### Clock Domain Assignment

Configuration registers and HPET core run in a clock domain determined by `CDC_ENABLE`:

```systemverilog
// HPET Configuration Registers
hpet_config_regs #(
    .VENDOR_ID        (VENDOR_ID),
    .REVISION_ID      (REVISION_ID),
    .NUM_TIMERS       (NUM_TIMERS)
) u_hpet_config_regs (
    // Clock and Reset - conditional based on CDC_ENABLE
    .clk               (CDC_ENABLE[0] ? hpet_clk : pclk),
    .rst_n             (CDC_ENABLE[0] ? hpet_resetn : presetn),
    // ... interface connections ...
);

// HPET Timer Core
hpet_core #(
    .NUM_TIMERS(NUM_TIMERS)
) u_hpet_core (
    // Clock and Reset - conditional based on CDC_ENABLE
    .clk                  (CDC_ENABLE[0] ? hpet_clk : pclk),
    .rst_n                (CDC_ENABLE[0] ? hpet_resetn : presetn),
    // ... interface connections ...
);
```

**Clock Assignment Logic:**
- **CDC_ENABLE=0:** Both use `pclk` and `presetn`
- **CDC_ENABLE=1:** Both use `hpet_clk` and `hpet_resetn`

**Rationale:** Configuration registers and timer core must run in the same domain. APB slave handles the clock crossing (if needed).

#### Integration Examples

##### Example 1: Synchronous Configuration (CDC_ENABLE=0)

```systemverilog
apb_hpet #(
    .VENDOR_ID(16'h8086),      // Intel vendor ID
    .REVISION_ID(16'h0001),
    .NUM_TIMERS(2),
    .CDC_ENABLE(0)              // ← Synchronous clocks
) u_hpet (
    // Use same clock for both domains
    .pclk           (system_clk),
    .presetn        (system_rst_n),
    .hpet_clk       (system_clk),      // ← Same clock as pclk
    .hpet_resetn    (system_rst_n),    // ← Same reset as presetn

    // APB Interface
    .s_apb_PSEL     (apb_psel),
    .s_apb_PENABLE  (apb_penable),
    .s_apb_PREADY   (apb_pready),
    .s_apb_PADDR    (apb_paddr[11:0]),
    .s_apb_PWRITE   (apb_pwrite),
    .s_apb_PWDATA   (apb_pwdata),
    .s_apb_PSTRB    (apb_pstrb),
    .s_apb_PPROT    (apb_pprot),
    .s_apb_PRDATA   (apb_prdata),
    .s_apb_PSLVERR  (apb_pslverr),

    // Timer Interrupts
    .timer_irq      (hpet_irq[1:0])
);

// Connect interrupts to system interrupt controller
assign irq_sources[31:30] = hpet_irq[1:0];
```

##### Example 2: Asynchronous Configuration (CDC_ENABLE=1)

```systemverilog
apb_hpet #(
    .VENDOR_ID(16'h1022),      // AMD vendor ID
    .REVISION_ID(16'h0002),
    .NUM_TIMERS(3),
    .CDC_ENABLE(1)              // ← Asynchronous clocks
) u_hpet (
    // APB domain (slow system clock)
    .pclk           (apb_clk),         // 50 MHz APB clock
    .presetn        (apb_rst_n),

    // HPET domain (high-precision timer clock)
    .hpet_clk       (timer_clk),       // 100 MHz timer clock (async)
    .hpet_resetn    (timer_rst_n),

    // APB Interface
    .s_apb_PSEL     (apb_psel),
    .s_apb_PENABLE  (apb_penable),
    .s_apb_PREADY   (apb_pready),
    .s_apb_PADDR    (apb_paddr[11:0]),
    .s_apb_PWRITE   (apb_pwrite),
    .s_apb_PWDATA   (apb_pwdata),
    .s_apb_PSTRB    (apb_pstrb),
    .s_apb_PPROT    (apb_pprot),
    .s_apb_PRDATA   (apb_prdata),
    .s_apb_PSLVERR  (apb_pslverr),

    // Timer Interrupts (hpet_clk domain)
    .timer_irq      (hpet_irq[2:0])
);

// Synchronize interrupts to system clock domain
sync_2ff #(.WIDTH(3)) u_irq_sync (
    .i_clk   (system_clk),
    .i_rst_n (system_rst_n),
    .i_data  (hpet_irq[2:0]),
    .o_data  (hpet_irq_sync[2:0])
);

// Connect synchronized interrupts to interrupt controller
assign irq_sources[33:31] = hpet_irq_sync[2:0];
```

#### Resource Utilization Summary

**Total Resource Usage by Configuration:**

| Configuration | NUM_TIMERS | CDC_ENABLE | Flip-Flops | LUTs | BRAM |
|---------------|------------|------------|------------|------|------|
| 2-timer sync | 2 | 0 | ~528 FF | ~510 LUTs | 0 |
| 3-timer sync | 3 | 0 | ~718 FF | ~680 LUTs | 0 |
| 8-timer sync | 8 | 0 | ~1544 FF | ~1360 LUTs | 0 |
| 2-timer CDC | 2 | 1 | ~608 FF | ~610 LUTs | 0 |
| 3-timer CDC | 3 | 1 | ~798 FF | ~780 LUTs | 0 |
| 8-timer CDC | 8 | 1 | ~1624 FF | ~1460 LUTs | 0 |

**Resource Breakdown:**
- **APB Slave (no CDC):** ~20 FF, ~50 LUTs
- **APB Slave CDC:** ~100 FF, ~150 LUTs
- **Config Registers:** Scales with NUM_TIMERS (~35 FF + ~70 LUTs per timer)
- **HPET Core:** Scales with NUM_TIMERS (~128 FF + ~85 LUTs per timer)

#### Verification Checklist

**Integration Validation:**

- [ ] **Clock Configuration:**
  - [ ] If CDC_ENABLE=0: Verify pclk = hpet_clk
  - [ ] If CDC_ENABLE=1: Verify independent clock sources

- [ ] **Reset Coordination:**
  - [ ] Both resets overlap at power-on
  - [ ] Both resets held for >=10 cycles
  - [ ] Reset deasserted cleanly

- [ ] **APB Interface:**
  - [ ] Read/write to all registers functional
  - [ ] Address decoding correct
  - [ ] PREADY timing appropriate (2 cycles sync, 4-6 cycles CDC)

- [ ] **Timer Operation:**
  - [ ] All NUM_TIMERS functional
  - [ ] One-shot mode works
  - [ ] Periodic mode works
  - [ ] Counter increments correctly

- [ ] **Interrupt Generation:**
  - [ ] All timer_irq outputs functional
  - [ ] W1C clearing works
  - [ ] Sticky behavior correct

- [ ] **CDC (if enabled):**
  - [ ] No metastability issues
  - [ ] Data integrity across domains
  - [ ] Proper handshake protocol

---

**Next:** [Chapter 2.5 - FSM Summary](05_fsm_summary.md)
