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

# APB HPET Architecture

## Overview

Three blocks do the work: an APB slave (with or without CDC), a register wrapper that adapts the PeakRDL register file to the core, and the timer core itself. The block diagram shows how they fit together.

### High-Level Block Diagram

```
+-------------------------------------------------------------------+
|                           APB HPET                                 |
|                                                                    |
|  +----------------+        +------------------+                  |
|  |   APB Slave    |--------▶|  hpet_config_regs|                  |
|  |  (Optional CDC)|        |  (PeakRDL Wrapper)|                  |
|  |                |        |                   |                  |
|  |  APB Interface |        | +--------------+ |                  |
|  |  - PADDR       |        | |  hpet_regs   | |  Per-Timer Data  |
|  |  - PDATA       |        | |  (PeakRDL    | |  Buses           |
|  |  - PSEL/PENABLE|        | |  Generated)  | |  +-+-+-+-+-+-+  |
|  |  - PREADY      |        | +--------------+ |  |0|1|2|3|...|N|  |
|  +----------------+        |                   |  +-+-+-+-+-+-+  |
|         |                  |  Edge Detect +    |       |         |
|         |                  |  Data Routing     |       |         |
|         ▼                  +------------------+       |         |
|  +----------------+               |                   |         |
|  |  APB CDC       |◀--------------+                   |         |
|  |  (Optional)    |                                    |         |
|  +----------------+                                    |         |
|         |                                               ▼         |
|         |                        +--------------------------+    |
|         +------------------------▶|     hpet_core           |    |
|                                   |                          |    |
|                                   |  +---------------------+|    |
|                                   |  |  64-bit Counter     ||    |
|                                   |  |  - Free-running     ||    |
|                                   |  |  - Read/Write access||    |
|                                   |  +---------------------+|    |
|                                   |                          |    |
|                                   |  +---------------------+|    |
|                                   |  | Timer Array [N-1:0] ||    |
|                                   |  |                     ||    |
|                                   |  | Per Timer:          ||    |
|                                   |  | - 64-bit Comparator ||    |
|                                   |  | - Control FSM       ||    |
|                                   |  | - Fire Detection    ||    |
|                                   |  | - Period Storage    ||    |
|                                   |  +---------------------+|    |
|                                   |                          |    |
|                                   |  Outputs:                |    |
|                                   |  - timer_irq[N-1:0]      |    |
|                                   |  - timer_fired[N-1:0]    |    |
|                                   +--------------------------+    |
|                                                 |                 |
|                                                 ▼                 |
|                                   timer_irq[NUM_TIMERS-1:0] ---------▶ To Interrupt Controller
|                                                                    |
+--------------------------------------------------------------------+
```

### Module Hierarchy

```
apb4_hpet (Top Level)
+-- apb4_slave (OR apb4_slave_cdc if CDC_ENABLE=1)
|   +-- APB protocol handling
|   +-- Read/write transaction management
|   +-- Optional clock domain crossing
|
+-- hpet_config_regs (Register Wrapper)
|   +-- hpet_regs (PeakRDL Generated)
|   |   +-- HPET_CONFIG register
|   |   +-- HPET_STATUS register (W1C)
|   |   +-- HPET_COUNTER_LO/HI registers
|   |   +-- HPET_ID register (RO, capabilities/identification)
|   |   +-- TIMER[i]_* registers (per-timer)
|   |
|   +-- edge_detect (x NUM_TIMERS) - Write strobe generation
|   +-- Per-timer data bus routing (corruption prevention)
|
+-- hpet_core (Timer Logic)
    +-- 64-bit main counter (r_main_counter)
    +-- Timer array [NUM_TIMERS-1:0]
    |   +-- 64-bit comparator (r_timer_comparator[i])
    |   +-- 64-bit period storage (r_timer_period[i])
    |   +-- Timer control FSM (one-shot vs periodic)
    |   +-- Fire detection logic
    +-- Counter increment logic
    +-- Comparator match detection
    +-- Interrupt generation
```

---

## Parameters

### Compile-Time Parameters

| Parameter | Type | Default | Range | Description |
|-----------|------|---------|-------|-------------|
| `NUM_TIMERS` | int | 2 | 2, 3, 8 | Number of independent timers |
| `VENDOR_ID` | int | 1 | -- | Currently unwired: HPET_ID vendor byte is fixed 0x01 in the generated register block |
| `REVISION_ID` | int | 1 | -- | Currently unwired: HPET_ID revision byte is fixed 0x01 |
| `CDC_ENABLE` | int | 0 | 0, 1 | Enable clock domain crossing |
| `USE_JOHNSON` | int | 0 | 0, 1 | CDC FIFO pointer encoding (0 = Gray, 1 = Johnson) |

The APB address bus is fixed at 12 bits and the data bus at 32 bits; they are
not parameters.

**Address-map constants** (values from the generated decode in
hpet_regs.sv -- there are no such localparams in the RTL):

- Timer stride: 0x20 bytes per timer
- Timer register base: 0x100

---

## Ports

### Interface Summary

**APB Interface:** Standard AMBA APB4
- Address width: Fixed 12-bit (4KB space)
- Data width: Fixed 32-bit
- Protocol: APB4 (with PREADY support)

**HPET Clock Interface:** Separate timer clock domain
- Independent from APB clock (if CDC enabled)
- Free-running 64-bit counter
- Configurable clock frequency

**Interrupt Interface:** Per-timer dedicated outputs
- `timer_irq[NUM_TIMERS-1:0]` - Active-high interrupt signals
- Registered output from core state (one hpet_clk after fire)
- W1C clearing via HPET_STATUS register

**See:** Chapter 3 - Interface Specifications for detailed signal descriptions

---

## Functional Description

### Data Flow

#### Write Transaction Flow (APB -> HPET Core)

```
1. APB Master Write
   |
   ▼
2. APB Slave (or APB CDC)
   - Protocol handling
   - Clock domain crossing (if enabled)
   |
   ▼
3. hpet_regs (PeakRDL)
   - Register decoding
   - Field updates
   - Software access flags (swacc, swmod)
   |
   ▼
4. hpet_config_regs
   - Edge detection on swacc signals
   - Generate write strobes (timer_comp_write[i])
   - Route per-timer data buses
   |
   ▼
5. hpet_core
   - Update counter (if HPET_COUNTER write)
   - Update comparator (if TIMER_COMPARATOR write)
   - Update control (if TIMER_CONFIG write)
   - Clear interrupt (if HPET_STATUS write with W1C)
```

#### Read Transaction Flow (HPET Core -> APB)

```
1. APB Master Read
   |
   ▼
2. APB Slave (or APB CDC)
   - Protocol handling
   - Read data synchronization (if CDC)
   |
   ▼
3. hpet_regs (PeakRDL)
   - Address decode
   - Multiplex read data from hardware interface (hwif)
   |
   ▼
4. hpet_config_regs
   - Connect hpet_core signals to hwif read ports
   |
   ▼
5. hpet_core
   - Provide counter value
   - Provide timer configuration
   - Provide status flags
   |
   ▼
6. APB Slave returns PRDATA to master
```

#### Timer Operation Flow

```
1. Counter Increment (every hpet_clk)
   r_main_counter <= r_main_counter + 1
   |
   ▼
2. Comparator Match Detection (for each timer i)
   timer_match[i] = (r_main_counter >= r_timer_comparator[i])
   |
   ▼
3. Timer Fire Logic
   |
   +- One-Shot Mode:
   |  - Fire when match first detected
   |  - Stay idle until reconfigured
   |  - Assert timer_irq[i]
   |
   +- Periodic Mode:
      - Fire when match detected
      - Auto-increment comparator:
        r_timer_comparator[i] <= r_timer_comparator[i] + r_timer_period[i]
      - Assert timer_irq[i]
      - Repeat
   |
   ▼
4. Interrupt Status Update
   HPET_STATUS[i] <= 1 (sticky until software clears via W1C)
   |
   ▼
5. Interrupt Output
   timer_irq[i] is a flop in hpet_core: set one hpet_clk after the fire
   event when timer_int_enable[i] was set at fire time; cleared by the
   same W1C that clears the status. It is core state, not a combinational
   copy of HPET_STATUS.
```

### Clock Domains

**Synchronous Mode (CDC_ENABLE = 0):**
```
+----------+
|   pclk   |--------+-------------+---------------+
+----------+        |             |               |
              +-----▼------+  +--▼------+  +----▼-----+
              | APB Slave  |  | hpet_   |  |  hpet_   |
              |            |  | config_ |  |  core    |
              |            |  | regs    |  |          |
              +------------+  +---------+  +----------+

Note: pclk = hpet_clk (same clock domain)
```

**Asynchronous Mode (CDC_ENABLE = 1):**
```
+----------+                                +----------+
|   pclk   |---------+--------------+       | hpet_clk |
+----------+         |              |       +----------+
               +-----▼------+  +---▼----+       |
               | APB Slave  |  |  APB   |       |
               |            |  |  CDC   |       |
               |            |  |        |       |
               +------------+  +---+----+       |
                                   |            |
                             +-----▼------------▼----+
                             |  hpet_config_regs +   |
                             |  hpet_core             |
                             |  (HPET clock domain)   |
                             +------------------------+

Note: pclk and hpet_clk are asynchronous, CDC required
```

### Reset Domains

**Reset Signals:**
- `presetn` - APB reset (active-low, asynchronous)
- `hpet_resetn` - HPET reset (active-low, asynchronous)

**Reset Behavior:**

The register file and the timer core always share ONE clock/reset domain,
selected by `CDC_ENABLE`: with `CDC_ENABLE=0` both run on `pclk`/`presetn`;
with `CDC_ENABLE=1` both run on `hpet_clk`/`hpet_resetn` and only the APB
front-end stays on `pclk`. There is no configuration in which the registers
and the core reset from different domains.

| Signal | Reset Value | Notes |
|--------|-------------|-------|
| `r_main_counter` | 64'h0 | Counter reset to zero |
| `r_timer_comparator[i]` | 64'h0 | Comparators reset to zero |
| `r_timer_period[i]` | 64'h0 | Period storage reset |
| `HPET_CONFIG` | 32'h0 | Global enable cleared |
| `HPET_STATUS` | undefined | Storage has no reset (RTL defect, #46); intended 8'h0 |
| `TIMER[i]_CONFIG` | 32'h0 | All timers disabled |

**Reset Sequence:**
```systemverilog
// Illustrative only. clk/rst_n are the selected domain:
// CDC_ENABLE=0 -> pclk/presetn; CDC_ENABLE=1 -> hpet_clk/hpet_resetn.
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        // Register file
        HPET_CONFIG <= '0;
        // HPET_STATUS: no reset exists in the RTL (defect #46) --
        // readback undefined until first load
        for (int i = 0; i < NUM_TIMERS; i++) begin
            TIMER_CONFIG[i] <= '0;
        end
        // Timer core
        r_main_counter <= 64'h0;
        for (int i = 0; i < NUM_TIMERS; i++) begin
            r_timer_comparator[i] <= 64'h0;
            r_timer_period[i] <= 64'h0;
            r_interrupt_status[i] <= 1'b0;
        end
    end
end
```

**CDC Reset Coordination:**
When CDC is enabled, both reset signals must be properly synchronized and coordinated to prevent metastability and ensure clean initialization.

---

## Usage Example

### Configuration Examples

**2-Timer Configuration (synchronous clocks):**
```systemverilog
apb4_hpet #(
    .NUM_TIMERS(2),
    .CDC_ENABLE(0)
) u_hpet_2t (...);
```

**8-Timer Configuration with CDC:**
```systemverilog
apb4_hpet #(
    .NUM_TIMERS(8),
    .CDC_ENABLE(1)          // Asynchronous clocks
) u_hpet_8t (...);
```

Setting `VENDOR_ID`/`REVISION_ID` at instantiation is accepted but has no
effect on the hardware: HPET_ID always reads back vendor 0x01 / revision
0x01 (see Chapter 5).

---

## Design Notes

### Per-Timer Data Bus Architecture

**Problem:** Initial implementation had timer corruption due to shared data bus

**Root Cause:**
```systemverilog
// WRONG: Shared data bus for all timers
wire [63:0] timer_comp_wdata;  // Single 64-bit bus

// Multiple timers try to sample from same bus
always_ff @(posedge hpet_clk) begin
    if (timer_comp_write[0]) r_timer_comparator[0] <= timer_comp_wdata;
    if (timer_comp_write[1]) r_timer_comparator[1] <= timer_comp_wdata;
    if (timer_comp_write[2]) r_timer_comparator[2] <= timer_comp_wdata;
    // If write strobes overlap, wrong timer gets wrong data!
end
```

**Solution:** Per-timer dedicated data buses
```systemverilog
// CORRECT: Dedicated data bus per timer
wire [63:0] timer_comp_wdata [NUM_TIMERS-1:0];  // Array of 64-bit buses

// Each timer has dedicated data path
always_ff @(posedge hpet_clk) begin
    if (timer_comp_write[0]) r_timer_comparator[0] <= timer_comp_wdata[0];
    if (timer_comp_write[1]) r_timer_comparator[1] <= timer_comp_wdata[1];
    if (timer_comp_write[2]) r_timer_comparator[2] <= timer_comp_wdata[2];
    // Each timer reads from its own dedicated bus - no corruption possible
end
```

**Implementation in hpet_config_regs.sv:**
```systemverilog
// Dedicated data buses prevent corruption
assign timer_comp_wdata[0] = {hwif.timer0_comparator_hi.value,
                                   hwif.timer0_comparator_lo.value};
assign timer_comp_wdata[1] = {hwif.timer1_comparator_hi.value,
                                   hwif.timer1_comparator_lo.value};
assign timer_comp_wdata[2] = {hwif.timer2_comparator_hi.value,
                                   hwif.timer2_comparator_lo.value};
// ... one data bus per timer
```

**Verification:** All timer corruption issues resolved after per-timer bus implementation

---

## Navigation

**Next:** [Chapter 1.3 - Clocks and Reset](03_clocks_and_reset.md)
