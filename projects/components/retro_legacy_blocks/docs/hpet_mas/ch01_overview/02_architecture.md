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

### APB HPET - Architecture

#### High-Level Block Diagram

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

#### Module Hierarchy

```
apb_hpet (Top Level)
+-- apb_slave (OR apb_slave_cdc if CDC_ENABLE=1)
|   +-- APB protocol handling
|   +-- Read/write transaction management
|   +-- Optional clock domain crossing
|
+-- hpet_config_regs (Register Wrapper)
|   +-- hpet_regs (PeakRDL Generated)
|   |   +-- HPET_CONFIG register
|   |   +-- HPET_STATUS register (W1C)
|   |   +-- HPET_COUNTER_LO/HI registers
|   |   +-- HPET_CAPABILITIES register (RO)
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

#### Data Flow

##### Write Transaction Flow (APB -> HPET Core)

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
   - Generate write strobes (timer_comparator_wr[i])
   - Route per-timer data buses
   |
   ▼
5. hpet_core
   - Update counter (if HPET_COUNTER write)
   - Update comparator (if TIMER_COMPARATOR write)
   - Update control (if TIMER_CONFIG write)
   - Clear interrupt (if HPET_STATUS write with W1C)
```

##### Read Transaction Flow (HPET Core -> APB)

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

##### Timer Operation Flow

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
   timer_irq[i] = HPET_STATUS[i] (combinational)
```

#### Clock Domains

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

#### Reset Domains

**Reset Signals:**
- `presetn` - APB reset (active-low, asynchronous)
- `hpet_rst_n` - HPET reset (active-low, asynchronous)

**Reset Behavior:**

| Signal | Reset Domain | Reset Value | Notes |
|--------|--------------|-------------|-------|
| `r_main_counter` | hpet_clk | 64'h0 | Counter reset to zero |
| `r_timer_comparator[i]` | hpet_clk | 64'h0 | Comparators reset to zero |
| `r_timer_period[i]` | hpet_clk | 64'h0 | Period storage reset |
| `HPET_CONFIG` | pclk | Disabled | Global enable cleared |
| `HPET_STATUS` | pclk | 8'h0 | All interrupt flags cleared |
| `TIMER[i]_CONFIG` | pclk | Disabled | All timers disabled |

**Reset Sequence:**
```systemverilog
// APB domain reset
always_ff @(posedge pclk or negedge presetn) begin
    if (!presetn) begin
        // Reset APB-accessible registers
        HPET_CONFIG <= '0;
        HPET_STATUS <= '0;
        for (int i = 0; i < NUM_TIMERS; i++) begin
            TIMER_CONFIG[i] <= '0;
        end
    end
end

// HPET domain reset
always_ff @(posedge hpet_clk or negedge hpet_rst_n) begin
    if (!hpet_rst_n) begin
        // Reset timer logic
        r_main_counter <= 64'h0;
        for (int i = 0; i < NUM_TIMERS; i++) begin
            r_timer_comparator[i] <= 64'h0;
            r_timer_period[i] <= 64'h0;
            r_timer_fired[i] <= 1'b0;
        end
    end
end
```

**CDC Reset Coordination:**
When CDC is enabled, both reset signals must be properly synchronized and coordinated to prevent metastability and ensure clean initialization.

#### Per-Timer Data Bus Architecture

**Problem:** Initial implementation had timer corruption due to shared data bus

**Root Cause:**
```systemverilog
// ❌ WRONG: Shared data bus for all timers
wire [63:0] timer_comparator_data;  // Single 64-bit bus

// Multiple timers try to sample from same bus
always_ff @(posedge hpet_clk) begin
    if (timer_comparator_wr[0]) r_timer_comparator[0] <= timer_comparator_data;
    if (timer_comparator_wr[1]) r_timer_comparator[1] <= timer_comparator_data;
    if (timer_comparator_wr[2]) r_timer_comparator[2] <= timer_comparator_data;
    // If write strobes overlap, wrong timer gets wrong data!
end
```

**Solution:** Per-timer dedicated data buses
```systemverilog
// ✅ CORRECT: Dedicated data bus per timer
wire [63:0] timer_comparator_data [NUM_TIMERS-1:0];  // Array of 64-bit buses

// Each timer has dedicated data path
always_ff @(posedge hpet_clk) begin
    if (timer_comparator_wr[0]) r_timer_comparator[0] <= timer_comparator_data[0];
    if (timer_comparator_wr[1]) r_timer_comparator[1] <= timer_comparator_data[1];
    if (timer_comparator_wr[2]) r_timer_comparator[2] <= timer_comparator_data[2];
    // Each timer reads from its own dedicated bus - no corruption possible
end
```

**Implementation in hpet_config_regs.sv:**
```systemverilog
// Dedicated data buses prevent corruption
assign timer_comparator_data[0] = {hwif.timer0_comparator_hi.value,
                                   hwif.timer0_comparator_lo.value};
assign timer_comparator_data[1] = {hwif.timer1_comparator_hi.value,
                                   hwif.timer1_comparator_lo.value};
assign timer_comparator_data[2] = {hwif.timer2_comparator_hi.value,
                                   hwif.timer2_comparator_lo.value};
// ... one data bus per timer
```

**Verification:** All timer corruption issues resolved after per-timer bus implementation

#### Parameterization

**Compile-Time Parameters:**

| Parameter | Type | Default | Range | Description |
|-----------|------|---------|-------|-------------|
| `NUM_TIMERS` | int | 2 | 2, 3, 8 | Number of independent timers |
| `VENDOR_ID` | int (16-bit) | 0x8086 | 0x0000-0xFFFF | Vendor identification |
| `REVISION_ID` | int (16-bit) | 0x0001 | 0x0000-0xFFFF | Hardware revision |
| `CDC_ENABLE` | bit | 0 | 0, 1 | Enable clock domain crossing |
| `ADDR_WIDTH` | int | 12 | >= 12 | APB address bus width |
| `DATA_WIDTH` | int | 32 | 32 | APB data bus width (fixed) |

**Derived Parameters:**
```systemverilog
localparam int TIMER_ADDR_OFFSET = 32'h20;  // 32-byte stride per timer
localparam int TIMER_REGS_START = 32'h100;  // Timer register base address
```

**Configuration Examples:**

**2-Timer "Intel-like" Configuration:**
```systemverilog
apb_hpet #(
    .NUM_TIMERS(2),
    .VENDOR_ID(16'h8086),   // Intel
    .REVISION_ID(16'h0001),
    .CDC_ENABLE(0)          // Synchronous clocks
) u_hpet_intel (...);
```

**3-Timer "AMD-like" Configuration:**
```systemverilog
apb_hpet #(
    .NUM_TIMERS(3),
    .VENDOR_ID(16'h1022),   // AMD
    .REVISION_ID(16'h0002),
    .CDC_ENABLE(0)
) u_hpet_amd (...);
```

**8-Timer Custom with CDC:**
```systemverilog
apb_hpet #(
    .NUM_TIMERS(8),
    .VENDOR_ID(16'hABCD),   // Custom vendor
    .REVISION_ID(16'h0010),
    .CDC_ENABLE(1)          // Asynchronous clocks
) u_hpet_custom (...);
```

#### Interface Summary

**APB Interface:** Standard AMBA APB4
- Address width: Configurable (default 12-bit for 4KB space)
- Data width: Fixed 32-bit
- Protocol: APB4 (with PREADY support)

**HPET Clock Interface:** Separate timer clock domain
- Independent from APB clock (if CDC enabled)
- Free-running 64-bit counter
- Configurable clock frequency

**Interrupt Interface:** Per-timer dedicated outputs
- `timer_irq[NUM_TIMERS-1:0]` - Active-high interrupt signals
- Combinational output (driven by STATUS register)
- W1C clearing via HPET_STATUS register

**See:** Chapter 3 - Interface Specifications for detailed signal descriptions

---

**Next:** [Chapter 1.3 - Clocks and Reset](03_clocks_and_reset.md)
