# Clocks and Reset Specification

**Chapter:** 01
**Version:** 0.90
**Last Updated:** 2025-11-22

---

## Overview

STREAM operates in a single clock domain with a single asynchronous active-low reset. This chapter defines clock requirements, reset behavior, and timing constraints for the STREAM subsystem.

---

## Clock Domain

### Primary Clock: `aclk`

**Specification:**
- **Name:** `aclk` (AXI clock)
- **Type:** Synchronous, single-edge (rising edge)
- **Frequency:** Configurable (typical: 100 MHz - 500 MHz)
- **Duty Cycle:** 50%   5%
- **Jitter:** < 100 ps peak-to-peak

**Usage:**
- All STREAM internal logic
- All AXI master interfaces
- All AXIL interfaces
- MonBus output
- SRAM

### Secondary Clock: `pclk` (APB Clock)

**Specification:**
- **Name:** `pclk` (Peripheral clock)
- **Type:** Synchronous, single-edge (rising edge)
- **Frequency:** Configurable (typical: 50 MHz - 200 MHz)
- **Relation to `aclk`:** May be asynchronous

**Usage:**
- APB configuration interface only

**Clock Domain Crossing (CDC):**
- If `pclk`   `aclk`: CDC logic required in `apb_config.sv`
- If `pclk` = `aclk`: Direct connection (no CDC)

**CDC Implementation:**
- Use `apb_slave_cdc` wrapper (like HPET example)
- `apb_slave_cdc` implements **handshake-based CDC** using `cdc_handshake` modules
  - One `cdc_handshake` for command interface (APB → core)
  - One `cdc_handshake` for response interface (core → APB)
  - Full req/ack handshake protocol (NOT async FIFO)
  - Works across all frequency ratios (slow-to-fast, fast-to-slow, any ratio)

---

## Reset

### Primary Reset: `aresetn`

**Specification:**
- **Name:** `aresetn` (AXI reset, active-low)
- **Type:** Asynchronous assertion, synchronous deassertion
- **Polarity:** Active-low (0 = reset, 1 = normal operation)
- **Assertion:** Asynchronous (can occur at any time)
- **Deassertion:** Synchronous to `aclk` rising edge
- **Duration:** Minimum 10 `aclk` cycles

**Reset Behavior:**

```systemverilog
// Standard reset pattern for all STREAM modules
always_ff @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        // Asynchronous reset assertion
        r_state <= IDLE;
        r_counter <= '0;
        r_valid <= 1'b0;
        // ... all registers to known state
    end else begin
        // Synchronous operation
        r_state <= w_next_state;
        // ... normal logic
    end
end
```

### Secondary Reset: `presetn`

**Specification:**
- **Name:** `presetn` (APB reset, active-low)
- **Type:** Asynchronous assertion, synchronous deassertion
- **Polarity:** Active-low (0 = reset, 1 = normal operation)
- **Synchronization:** May be asynchronous to `aresetn`

**Usage:**
- APB configuration interface only
- Typically tied to `aresetn` if `pclk` = `aclk`

---

## Reset Sequencing

### Power-On Reset

**Recommended sequence:**

```
1. Assert aresetn (LOW)
2. Assert presetn (LOW)
3. Apply stable clocks (aclk, pclk)
4. Wait   10 aclk cycles
5. Deassert presetn (HIGH) on pclk rising edge
6. Deassert aresetn (HIGH) on aclk rising edge
7. Wait   5 aclk cycles for stabilization
8. Begin APB configuration
```

**Timing diagram:**

```
aclk     __| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_
pclk     __| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_
aresetn  __________|                                  
presetn  __________|                                  
         <--10 cyc-->
```

### Functional Reset

**Software-initiated reset (per channel):**

```c
// Reset specific channel via APB
write_apb(ADDR_GLOBAL_CTRL, CHANNEL_0_RESET);  // Auto-clears after 1 cycle

// Hardware response:
// - Channel FSM returns to IDLE
// - Channel registers cleared
// - Outstanding transactions flushed
// - MonBus error packet generated (if mid-transfer)
```

### Reset Recovery

**After reset deassertion:**

| Cycle | Event |
|-------|-------|
| 0 | `aresetn` deasserted (rising edge) |
| 1-5 | Internal state stabilization |
| 6+ | Ready for APB configuration |
| 10+ | Ready for descriptor transfers |

---

## Clock Requirements by Module

### Functional Unit Blocks (FUB)

| Module | Clock | Reset | Frequency | Notes |
|--------|-------|-------|-----------|-------|
| descriptor_engine | `aclk` | `aresetn` | 100-500 MHz | AXI master timing |
| scheduler | `aclk` | `aresetn` | 100-500 MHz | Single cycle FSM |
| axi_read_engine | `aclk` | `aresetn` | 100-500 MHz | AXI master timing |
| axi_write_engine | `aclk` | `aresetn` | 100-500 MHz | AXI master timing |
| simple_sram | `aclk` | `aresetn` | 100-500 MHz | Synchronous SRAM |

### Integration Blocks (MAC)

| Module | Clock(s) | Reset(s) | Frequency | Notes |
|--------|----------|----------|-----------|-------|
| channel_arbiter | `aclk` | `aresetn` | 100-500 MHz | Single cycle arbitration |
| apb_config | `pclk`, (`aclk`) | `presetn`, (`aresetn`) | 50-200 MHz (APB) | CDC if async |
| monbus_axil_group | `aclk` | `aresetn` | 100-500 MHz | AXIL timing |
| stream_top | `aclk`, `pclk` | `aresetn`, `presetn` | Mixed | Top-level |

---

## Timing Constraints

### Setup and Hold Times

**Internal registers (relative to `aclk`):**
- Setup time: 0.5 ns (typical)
- Hold time: 0.1 ns (typical)
- Clock-to-Q: 0.3 ns (typical)

**External interfaces:**
- AXI/AXIL: Per ARM IHI0022E specification
- APB: Per ARM IHI0024C specification

### Critical Paths

**Identified critical paths:**

1. **Arbiter -> Scheduler grant:**
   - Latency: 1 cycle
   - Path: Priority encoder -> One-hot grant

2. **AXI read -> SRAM write:**
   - Latency: 1 cycle
   - Path: R data -> SRAM write port

3. **SRAM read -> AXI write:**
   - Latency: 1 cycle
   - Path: SRAM read port -> W data

**Maximum frequency estimation:**
- Typical FPGA (Xilinx 7-series): 250 MHz
- High-end FPGA (UltraScale+): 400 MHz
- ASIC (28nm): 500 MHz

---

## Clock Domain Crossing (CDC)

### APB Configuration CDC

**When required:** `pclk`   `aclk` (asynchronous APB interface)

**CDC Implementation:**

```systemverilog
// APB to STREAM domain (pclk -> aclk)
apb_slave_cdc #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32),
    .SYNC_STAGES(2)  // Dual-flop synchronizer
) u_apb_cdc (
    // APB side (pclk domain)
    .s_pclk(pclk),
    .s_presetn(presetn),
    .s_paddr(paddr),
    .s_pwrite(pwrite),
    .s_pwdata(pwdata),
    .s_prdata(prdata),

    // STREAM side (aclk domain)
    .m_pclk(aclk),
    .m_presetn(aresetn),
    .m_paddr(paddr_sync),
    .m_pwrite(pwrite_sync),
    .m_pwdata(pwdata_sync),
    .m_prdata(prdata_sync)
);
```

**CDC Mechanism:**
- `apb_slave_cdc` uses **handshake-based CDC** via `cdc_handshake` modules (NOT async FIFOs)
- **Command path** (`pclk` → `aclk`): APB write/read commands cross via req/ack handshake
- **Response path** (`aclk` → `pclk`): APB read data crosses back via req/ack handshake
- **Internal synchronizers**: Dual-flop synchronizers (2-3 stages) for handshake signals
- **ASYNC_REG attribute**: Applied to synchronizer stages for timing tools
- **Timing constraints**: Proper constraints required in SDC/XDC for synchronizer paths

**Handshake Protocol Benefits:**
- Works across **all frequency ratios** (slow-to-fast, fast-to-slow, arbitrary ratios)
- Guaranteed data integrity (req/ack ensures data stability before sampling)
- No FIFO depth management or gray code pointer complexity
- Latency: 4-6 APB clock cycles for register access (handshake round-trip)

### No CDC Required

**Single clock domain:** If `pclk` = `aclk` and `presetn` = `aresetn`:

```systemverilog
// Direct connection (no CDC wrapper)
apb_config #(
    .NUM_CHANNELS(8)
) u_apb_config (
    .pclk(aclk),        // Same clock
    .presetn(aresetn),  // Same reset
    // ... direct APB signals
);
```

---

## Reset State Initialization

### Register Reset Values

**All STREAM modules must initialize to known state on reset:**

```systemverilog
// Descriptor Engine
if (!aresetn) begin
    r_desc_fifo_wr_ptr <= '0;
    r_desc_valid <= 1'b0;
    r_desc_error <= 1'b0;
end

// Scheduler
if (!aresetn) begin
    r_current_state <= CH_IDLE;
    r_read_beats_remaining <= '0;
    r_write_beats_remaining <= '0;
    r_timeout_counter <= '0;
end

// AXI Engines
if (!aresetn) begin
    r_burst_counter <= '0;
    m_axi_arvalid <= 1'b0;
    m_axi_awvalid <= 1'b0;
end

// Arbiter
if (!aresetn) begin
    r_last_grant_id <= '0;
    r_grant_valid <= 1'b0;
end
```

### SRAM Reset

**SRAM contents:** Undefined after reset (no initialization required)

**SRAM pointers:**
```systemverilog
if (!aresetn) begin
    wr_ptr <= '0;
    rd_ptr <= '0;
end
```

---

## Clock Gating (Optional)

**For power optimization in ASIC implementations:**

### Per-Channel Clock Gating

```systemverilog
// Clock gate when channel idle
clock_gate_ctrl u_ch0_clk_gate (
    .clk_in(aclk),
    .enable(ch0_enable),
    .clk_out(ch0_gated_clk)
);

// Use gated clock for channel logic
scheduler #(.CHANNEL_ID(0)) u_ch0_sched (
    .aclk(ch0_gated_clk),  // Gated clock
    .aresetn(aresetn),
    // ...
);
```

**Note:** Clock gating typically not used in FPGA implementations (tutorial focus).

---

## Verification Requirements

### Clock Checks

**Testbench must verify:**
- [Done] Clock period consistent
- [Done] Clock duty cycle 50%   tolerance
- [Done] No glitches on clock
- [Done] Setup/hold times met

### Reset Checks

**Testbench must verify:**
- [Done] All registers initialize to known state
- [Done] Reset assertion clears FSMs to IDLE
- [Done] Reset deassertion synchronous to clock
- [Done] Minimum reset duration (10 cycles) enforced
- [Done] Operations don't start until stabilization complete

### CDC Checks

**For APB CDC (if present):**
- [Done] No metastability violations
- [Done] Data integrity across domains
- [Done] Proper flag synchronization

---

## Example Reset Testbench

```python
# CocoTB testbench pattern
class StreamTB(TBBase):
    async def setup_clocks_and_reset(self):
        """Complete clock and reset initialization"""
        # Start clocks
        await self.start_clock('aclk', freq=10, units='ns')  # 100 MHz
        await self.start_clock('pclk', freq=20, units='ns')  # 50 MHz (async)

        # Assert reset
        await self.assert_reset()

        # Hold reset for 10 aclk cycles
        await self.wait_clocks('aclk', 10)

        # Deassert reset (synchronous to aclk)
        await self.deassert_reset()

        # Stabilization period
        await self.wait_clocks('aclk', 5)

        # Ready for operation

    async def assert_reset(self):
        """Assert both resets"""
        self.dut.aresetn.value = 0
        self.dut.presetn.value = 0

    async def deassert_reset(self):
        """Deassert both resets synchronously"""
        # Wait for rising edge of aclk
        await RisingEdge(self.dut.aclk)
        self.dut.aresetn.value = 1

        # Wait for rising edge of pclk
        await RisingEdge(self.dut.pclk)
        self.dut.presetn.value = 1
```

---

## Related Documentation

- **Scheduler FSM:** `fub_02_scheduler.md` - Reset behavior
- **APB Config:** `mac_02_apb_config.md` - CDC implementation
- **Top-Level:** `mac_04_stream_top.md` - Clock/reset integration

---

**Last Updated:** 2025-12-01
