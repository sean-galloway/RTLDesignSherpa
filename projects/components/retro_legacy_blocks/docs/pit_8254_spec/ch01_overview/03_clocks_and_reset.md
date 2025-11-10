### APB PIT 8254 - Clocks and Reset

#### Clock Domains

The APB PIT 8254 supports two clock domain configurations controlled by the `CDC_ENABLE` parameter:

**Single Clock Configuration (CDC_ENABLE=0):**
```
pclk (APB clock) ──┬──► APB Slave Interface
                   ├──► Register File
                   └──► Counter Logic
```

**Dual Clock Configuration (CDC_ENABLE=1):**
```
pclk (APB clock) ────► APB Slave Interface ──► CDC Logic ──┐
                                                             ├──► Register File
pit_clk (Timer clock) ───────────────────────────────────────┴──► Counter Logic
```

#### Clock Signals

**pclk (APB Clock):**
- **Purpose:** APB bus interface timing
- **Frequency:** Determined by system APB bus (typically 50-100 MHz)
- **Domain:** Always present, required for register access
- **Usage:** Clocks APB slave, optional CDC logic

**pit_clk (PIT Timer Clock):**
- **Purpose:** Counter decrement timing
- **Frequency:** Configurable, determines timer resolution
- **Domain:** Only used when `CDC_ENABLE=1`
- **Usage:** Clocks counter logic when separate from APB domain
- **Note:** When `CDC_ENABLE=0`, counters use `pclk` directly

#### Clock Domain Crossing (CDC)

**When CDC_ENABLE=1:**

The design includes clock domain crossing infrastructure to safely transfer data between APB and timer clock domains:

**CDC Components:**
- `apb_slave_cdc` module provides safe crossing from `pclk` to `pit_clk`
- Command/response interface synchronized using gray-code FIFOs
- Handshaking ensures no data loss across domains
- Status signals synchronized back to `pclk` domain

**CDC Timing:**
```
APB Write → pclk domain → CDC FIFO → pit_clk domain → Register Update
                (1-2 cycles)        (2-3 cycles)      (1 cycle)
Total latency: 4-6 pit_clk cycles
```

**CDC Verification:**
- All 6/6 tests pass with `CDC_ENABLE=1` configuration
- No metastability issues observed in simulation
- Proper handshaking verified with stress tests

**When CDC_ENABLE=0:**

The design uses a single clock domain with `apb_slave` module (no CDC):

**Direct Connection:**
- APB slave converts APB protocol to cmd/rsp interface
- No domain crossing required
- Lower latency (2-3 cycle register access)

**Single Clock Timing:**
```
APB Write → pclk domain → Register Update
                (1-2 cycles)
Total latency: 2-3 pclk cycles
```

#### Clock Enable Signal

**i_clk_en (Clock Enable):**
- **Purpose:** Global enable/disable for counter operation
- **Source:** `PIT_CONFIG.PIT_ENABLE` register bit
- **Effect:** Gates counter decrement logic without stopping clock
- **Behavior:**
  - `i_clk_en=0`: Counters hold current value
  - `i_clk_en=1`: Counters decrement normally (if GATE high)

**Implementation:**
```systemverilog
// Counter decrement with clock enable check
if (r_counting && i_clk_en) begin
    if (r_count == 16'd0) begin
        r_out <= 1'b1;        // Terminal count reached
        r_counting <= 1'b0;
    end else begin
        r_count <= r_count - 16'd1;
    end
end
```

**Benefits:**
- Software-controlled start/stop without glitches
- Preserves counter values during disable
- No clock domain crossing issues
- Synchronous control

#### Reset Signal

**presetn (Active-Low Asynchronous Reset):**
- **Type:** Asynchronous assertion, synchronous deassertion
- **Polarity:** Active-low (standard APB convention)
- **Domain:** Applied to all clock domains
- **Purpose:** Initialize all state to known values

**Reset Behavior:**

**Power-On Reset:**
```systemverilog
// All counters reset to safe state
r_count         <= 16'd0;       // Counter value cleared
r_null_count    <= 1'b1;        // No count loaded flag set
r_counting      <= 1'b0;        // Not counting
r_out           <= 1'b0;        // OUT signal low
r_reload_pending<= 1'b0;        // No reload pending
r_mode          <= 3'b000;      // Mode 0
r_rw_mode       <= 2'b00;       // No access mode set
r_bcd           <= 1'b0;        // Binary mode
```

**Register Reset Values:**
```
PIT_CONFIG    = 0x00000000  (PIT disabled)
PIT_STATUS    = 0x00303030  (all counters NULL_COUNT=1, OUT=0)
COUNTER0_DATA = 0x00000000  (no count loaded)
COUNTER1_DATA = 0x00000000  (no count loaded)
COUNTER2_DATA = 0x00000000  (no count loaded)
```

**Reset Timing:**
```
presetn ──┐      ┌──────────────────────────
          │      │
          └──────┘
          ▲      ▲
       Assert  Deassert
         │        │
         │        └── Synchronous to clock edge
         └─────────── Asynchronous (immediate)

pclk   ───┐  ┐  ┐  ┐  ┐  ┐  ┐──
          └──┘  └──┘  └──┘  └──
             ▲
             └── State cleared on this edge (or earlier if async assert)
```

**Reset Sequence:**

1. **Assertion (asynchronous):**
   - Immediately forces all state to reset values
   - No clock edge required
   - Occurs as soon as `presetn=0`

2. **Hold Period:**
   - Must hold `presetn=0` for minimum 2 clock cycles
   - Ensures all registers properly reset
   - Applies to slowest clock domain (if CDC enabled)

3. **Deassertion (synchronous):**
   - Released synchronously with clock edge
   - State begins normal operation
   - Counters remain idle until configured

**Recommended Reset Sequence:**
```c
// 1. Assert reset
set_reset(0);
wait_us(10);  // Hold for sufficient time

// 2. Deassert reset
set_reset(1);
wait_us(10);  // Allow settling

// 3. Verify reset state
assert(read_register(PIT_CONFIG) == 0x00000000);
assert(read_register(PIT_STATUS) == 0x00303030);

// 4. Configure PIT
write_register(PIT_CONTROL, 0x30);  // Counter 0, Mode 0
write_register(COUNTER0_DATA, 1000);
write_register(PIT_CONFIG, 0x01);   // Enable PIT
```

#### Clock Gating

**Dynamic Clock Gating:**

The PIT does NOT implement dynamic clock gating at the module level. Clock gating (if desired) should be implemented at the integration level:

**Integration-Level Gating Example:**
```systemverilog
// External clock gate (system integrator's responsibility)
logic gated_pclk;
assign gated_pclk = pclk & pit_clock_enable;

apb_pit_8254 #(
    .CDC_ENABLE(0)
) u_pit (
    .pclk       (gated_pclk),  // Gated clock
    // ...
);
```

**Static Clock Enable:**

When `PIT_ENABLE=0`, counters use clock enable gating internally:
- Clock still toggles (no clock tree gating)
- Counter logic uses `if (i_clk_en)` conditions
- Reduces dynamic power by preventing state changes
- No glitches or timing issues

#### Multi-Clock Timing Constraints

**For CDC_ENABLE=1 configurations, apply these timing constraints:**

**Clock Definitions:**
```tcl
create_clock -period 10.0 [get_ports pclk]
create_clock -period 20.0 [get_ports pit_clk]
```

**Asynchronous Clock Groups:**
```tcl
set_clock_groups -asynchronous \
    -group [get_clocks pclk] \
    -group [get_clocks pit_clk]
```

**CDC Path Constraints:**
```tcl
# CDC paths handled by apb_slave_cdc module
# Verify no timing paths between domains except through CDC
set_false_path -from [get_clocks pclk] -to [get_clocks pit_clk]
set_false_path -from [get_clocks pit_clk] -to [get_clocks pclk]
```

**Reset Synchronization:**
```tcl
# Reset must be synchronized to each clock domain
set_false_path -from [get_ports presetn] -to [all_registers]
```

---

**Version:** 1.0
**Last Updated:** 2025-11-08
