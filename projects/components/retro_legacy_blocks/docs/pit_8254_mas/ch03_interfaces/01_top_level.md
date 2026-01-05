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

### APB PIT 8254 - Top-Level Interface

#### Module Declaration

```systemverilog
module apb_pit_8254 #(
    parameter int NUM_COUNTERS = 3,      // Number of counters (fixed at 3)
    parameter int CDC_ENABLE   = 0       // 0=single clock, 1=dual clock with CDC
) (
    // APB Clock and Reset
    input  logic        pclk,
    input  logic        presetn,

    // APB Interface
    input  logic [31:0] paddr,
    input  logic        psel,
    input  logic        penable,
    input  logic        pwrite,
    input  logic [31:0] pwdata,
    input  logic [3:0]  pstrb,
    output logic [31:0] prdata,
    output logic        pready,
    output logic        pslverr,

    // PIT Clock and Reset (used when CDC_ENABLE=1)
    input  logic        pit_clk,
    input  logic        pit_rst_n,

    // Counter GATE Inputs
    input  logic [2:0]  gate_in,

    // Timer Interrupt Outputs
    output logic [2:0]  timer_irq
);
```

#### Signal Groups

**APB Clock and Reset:**
| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `pclk` | Input | 1 | APB bus clock. All APB signals are synchronous to this clock. |
| `presetn` | Input | 1 | APB reset, active-low. Asynchronous assertion, synchronous deassertion. |

**APB Interface Signals:**
| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `paddr` | Input | 32 | APB address. Only bits [7:0] are decoded (256-byte address space). |
| `psel` | Input | 1 | APB select. Asserted by interconnect when this peripheral is accessed. |
| `penable` | Input | 1 | APB enable. Asserted in second cycle of transfer (access phase). |
| `pwrite` | Input | 1 | APB write/read. 1=write, 0=read. |
| `pwdata` | Input | 32 | APB write data. Valid only when `pwrite=1`. |
| `pstrb` | Input | 4 | APB write strobe (byte lane enables). Currently unused, all writes are 32-bit. |
| `prdata` | Output | 32 | APB read data. Valid when `pready=1` and `pwrite=0`. |
| `pready` | Output | 1 | APB ready. Asserted when peripheral completes transaction. Always 1 for this design (zero wait states). |
| `pslverr` | Output | 1 | APB slave error. Asserted for invalid address access. |

**PIT Clock and Reset:**
| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `pit_clk` | Input | 1 | Timer clock. Used when `CDC_ENABLE=1` for independent timer clock domain. Ignored when `CDC_ENABLE=0`. |
| `pit_rst_n` | Input | 1 | Timer reset, active-low. Used when `CDC_ENABLE=1`. Should be synchronous to `pit_clk`. Ignored when `CDC_ENABLE=0`. |

**Counter Control and Status:**
| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `gate_in[2:0]` | Input | 3 | GATE inputs for counters 0, 1, 2. When high, corresponding counter is enabled (if also globally enabled). When low, counter pauses. |
| `timer_irq[2:0]` | Output | 3 | Timer interrupt outputs. Driven by OUT signals from counters 0, 1, 2. High when terminal count reached (Mode 0). |

#### Address Map

The APB PIT 8254 decodes only the lower 8 bits of `paddr`, providing a 256-byte address space:

| Address Range | Register | Access | Description |
|---------------|----------|--------|-------------|
| `0x000` | PIT_CONFIG | RW | Global configuration (enable) |
| `0x004` | PIT_CONTROL | WO | Control word (8254-compatible) |
| `0x008` | PIT_STATUS | RO | Status readback (3 counters) |
| `0x00C` | RESERVED | - | Reserved |
| `0x010` | COUNTER0_DATA | RW | Counter 0 value |
| `0x014` | COUNTER1_DATA | RW | Counter 1 value |
| `0x018` | COUNTER2_DATA | RW | Counter 2 value |
| `0x01C-0x0FF` | - | - | Unmapped (returns SLVERR) |

**Integration Note:** When integrating into a larger address space, these addresses are relative to the base address assigned to the PIT. For example, if the PIT is assigned base address `0x4000_2000`, then PIT_CONFIG would be at absolute address `0x4000_2000`.

#### Parameter Configuration

**NUM_COUNTERS:**
- **Type:** Integer parameter
- **Default:** 3
- **Valid Values:** Currently fixed at 3
- **Purpose:** Defines number of independent counters
- **Note:** While parameterized, current implementation only supports 3 counters

**CDC_ENABLE:**
- **Type:** Integer parameter
- **Default:** 0
- **Valid Values:** 0 (single clock), 1 (dual clock with CDC)
- **Purpose:** Selects between single-clock and dual-clock configuration
- **Impact:**
  - `CDC_ENABLE=0`: Uses `apb_slave`, ignores `pit_clk` and `pit_rst_n`
  - `CDC_ENABLE=1`: Uses `apb_slave_cdc`, requires `pit_clk` and `pit_rst_n`

#### Clock Domain Configuration

**Single Clock Mode (CDC_ENABLE=0):**

**Connections:**
```systemverilog
// All logic uses pclk
apb_slave      uses: pclk, presetn
pit_config_regs uses: pclk, presetn
pit_core       uses: pclk, presetn
pit_counter[*] uses: pclk, presetn

// pit_clk and pit_rst_n are not used
```

**Use Cases:**
- Timer clock same as APB bus clock
- Simplified integration
- Lower latency (no CDC overhead)
- FPGA implementations with single clock domain

**Dual Clock Mode (CDC_ENABLE=1):**

**Connections:**
```systemverilog
// APB interface uses pclk
apb_slave_cdc uses: pclk for APB side, pit_clk for timer side
                    presetn for APB reset, pit_rst_n for timer reset

// Timer logic uses pit_clk
pit_config_regs uses: pit_clk, pit_rst_n
pit_core       uses: pit_clk, pit_rst_n
pit_counter[*] uses: pit_clk, pit_rst_n
```

**Use Cases:**
- Timer requires independent clock frequency
- Timer clock faster/slower than APB bus
- Power optimization (gate APB clock, keep timer running)
- Multiple clock domain systems

**CDC Considerations:**
- APB transactions take 4-6 `pit_clk` cycles (vs 2-3 in single-clock mode)
- Both clocks must be free-running during transactions
- Ensure proper reset sequencing (both domains reset before use)

#### Reset Requirements

**Power-On Reset Sequence:**

1. Assert both resets:
   ```
   presetn = 0
   pit_rst_n = 0  (if CDC_ENABLE=1)
   ```

2. Hold for minimum 10 clock cycles (of slowest clock):
   ```
   wait >= 10 * max(pclk_period, pit_clk_period)
   ```

3. Deassert resets synchronously:
   ```
   // On rising edge of pclk
   presetn = 1

   // On rising edge of pit_clk (if CDC_ENABLE=1)
   pit_rst_n = 1
   ```

4. Wait for reset propagation:
   ```
   wait >= 5 * max(pclk_period, pit_clk_period)
   ```

5. PIT now ready for register access

**Reset During Operation:**

If resetting during operation:
- Disable PIT first: `write(PIT_CONFIG, 0x00)`
- Wait for counters to stop: `wait >= 2 * pit_clk_period`
- Assert reset
- Follow power-on reset sequence from step 2

#### APB Protocol Timing

**Write Transaction (Zero Wait States):**

```
        ┌───┐   ┌───┐   ┌───┐   ┌───┐
pclk    ┘   └───┘   └───┘   └───┘   └───
          SETUP   ACCESS
psel    ───────┐           ┌───────────
               └───────────┘
penable ───────────┐   ┌───────────────
                   └───┘
pwrite  ───────┐           ┌───────────
               └───────────┘
paddr   ═══════X═══════════X═══════════
pwdata  ═══════X═══════════X═══════════
pready  ───────────────┐   ┌───────────
                       └───┘
```

**Read Transaction (Zero Wait States):**

```
        ┌───┐   ┌───┐   ┌───┐   ┌───┐
pclk    ┘   └───┘   └───┘   └───┘   └───
          SETUP   ACCESS
psel    ───────┐           ┌───────────
               └───────────┘
penable ───────────┐   ┌───────────────
                   └───┘
pwrite  ───────────────────────────────  (0)
paddr   ═══════X═══════════X═══════════
prdata  ═══════════════════X═══════════  (valid in ACCESS)
pready  ───────────────┐   ┌───────────
                       └───┘
```

**Error Response (Invalid Address):**

```
        ┌───┐   ┌───┐   ┌───┐   ┌───┐
pclk    ┘   └───┘   └───┘   └───┘   └───
          SETUP   ACCESS
psel    ───────┐           ┌───────────
               └───────────┘
penable ───────────┐   ┌───────────────
                   └───┘
paddr   ═══X0x01C══════════X═══════════  (unmapped)
pready  ───────────────┐   ┌───────────
                       └───┘
pslverr ───────────────┐   ┌───────────
                       └───┘
```

#### Integration Example

**Single Clock Integration:**

```systemverilog
apb_pit_8254 #(
    .NUM_COUNTERS(3),
    .CDC_ENABLE(0)
) u_pit (
    // APB interface
    .pclk       (apb_clk),
    .presetn    (apb_rst_n),
    .paddr      (paddr),
    .psel       (psel_pit),
    .penable    (penable),
    .pwrite     (pwrite),
    .pwdata     (pwdata),
    .pstrb      (pstrb),
    .prdata     (prdata_pit),
    .pready     (pready_pit),
    .pslverr    (pslverr_pit),

    // PIT clock (unused in single-clock mode, tie to apb_clk)
    .pit_clk    (apb_clk),
    .pit_rst_n  (apb_rst_n),

    // External signals
    .gate_in    (3'b111),           // All counters enabled
    .timer_irq  (pit_interrupts)
);
```

**Dual Clock Integration:**

```systemverilog
apb_pit_8254 #(
    .NUM_COUNTERS(3),
    .CDC_ENABLE(1)
) u_pit (
    // APB interface (system clock domain)
    .pclk       (system_clk),         // 100 MHz
    .presetn    (system_rst_n),
    .paddr      (paddr),
    .psel       (psel_pit),
    .penable    (penable),
    .pwrite     (pwrite),
    .pwdata     (pwdata),
    .pstrb      (pstrb),
    .prdata     (prdata_pit),
    .pready     (pready_pit),
    .pslverr    (pslverr_pit),

    // PIT clock (dedicated timer clock domain)
    .pit_clk    (timer_clk),          // 10 MHz (independent)
    .pit_rst_n  (timer_rst_n),

    // External signals
    .gate_in    (pit_gate_controls),  // From external logic
    .timer_irq  (pit_interrupts)
);
```

---

**Version:** 1.0
**Last Updated:** 2025-11-08
