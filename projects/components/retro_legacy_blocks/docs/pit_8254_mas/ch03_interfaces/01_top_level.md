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

# APB PIT 8254 - Top-Level Interface

## Overview

`apb4_pit_8254` is the top-level module: an APB4 slave on one side, GATE inputs and interrupt outputs on the other, and a parameter-selected clocking scheme in the middle. This chapter is the integration contract -- pin list, parameters, address decode, and the reset sequence your SoC has to honor.

## Parameters

| Parameter | Type | Default | Valid Values | Description |
|-----------|------|---------|--------------|-------------|
| `NUM_COUNTERS` | int | 3 | Currently fixed at 3 | Number of independent counters. Parameterized, but the current implementation only supports 3. |
| `CDC_ENABLE` | bit | 0 | 0 = single clock, 1 = dual clock with CDC | Selects the clocking scheme. `CDC_ENABLE=0` uses `apb4_slave` and ignores `pit_clk`/`pit_resetn`; `CDC_ENABLE=1` uses `apb4_slave_cdc` and requires both. |
| `USE_JOHNSON` | int | 0 | 0 = Gray-coded CDC FIFO pointers, 1 = Johnson-coded | Forwarded to the CDC block's async FIFOs. Gray requires a power-of-2 depth; Johnson allows any depth. Only meaningful when `CDC_ENABLE=1`. |
| `SYNC_STAGES` | int | 2 | >= 2 | Depth of the `gate_in` synchronizer in `pit_core`. Present in both clocking configurations -- the pin is asynchronous to the counting clock either way. A GATE transition reaches the counter `SYNC_STAGES` counting clocks after it happens. |

## Ports

### Module Declaration

```systemverilog
module apb4_pit_8254 #(
    parameter int NUM_COUNTERS = 3,  // Number of counters (fixed at 3)
    parameter bit CDC_ENABLE   = 0,  // 0=single clock, 1=dual clock with CDC
    parameter int USE_JOHNSON  = 0,  // CDC FIFO pointer encoding: 0=Gray, 1=Johnson
    parameter int SYNC_STAGES  = 2   // gate_in synchronizer depth, >= 2
) (
    // Clock and Reset - Dual Domain
    input  wire                    pclk,        // APB clock domain
    input  wire                    presetn,     // APB reset (active low)
    input  wire                    pit_clk,     // PIT clock domain (CDC_ENABLE=1)
    input  wire                    pit_resetn,  // PIT reset (active low)

    // APB4 Slave Interface
    input  wire                    s_apb_PSEL,
    input  wire                    s_apb_PENABLE,
    output wire                    s_apb_PREADY,
    input  wire [11:0]             s_apb_PADDR,
    input  wire                    s_apb_PWRITE,
    input  wire [31:0]             s_apb_PWDATA,
    input  wire [3:0]              s_apb_PSTRB,
    input  wire [2:0]              s_apb_PPROT,
    output wire [31:0]             s_apb_PRDATA,
    output wire                    s_apb_PSLVERR,

    // Timer Interface
    input  wire [NUM_COUNTERS-1:0] gate_in,     // GATE inputs for counters
    output wire [NUM_COUNTERS-1:0] timer_irq    // Interrupt outputs
);
```

### Signal Groups

**APB Clock and Reset:**
| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `pclk` | Input | 1 | APB bus clock. All APB signals are synchronous to this clock. |
| `presetn` | Input | 1 | APB reset, active-low. Asynchronous assertion, synchronous deassertion (generated register file is the exception -- it resets synchronously; see ch01 clocks). |

**APB Interface Signals:**
| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `s_apb_PADDR` | Input | 12 | APB address. All 12 bits are compared against the seven mapped registers; anything else is dropped with PSLVERR. See Address Map below. |
| `s_apb_PSEL` | Input | 1 | APB select. Asserted by interconnect when this peripheral is accessed. |
| `s_apb_PENABLE` | Input | 1 | APB enable. Asserted in second cycle of transfer (access phase). |
| `s_apb_PWRITE` | Input | 1 | APB write/read. 1=write, 0=read. |
| `s_apb_PWDATA` | Input | 32 | APB write data. Valid only when `s_apb_PWRITE=1`. |
| `s_apb_PSTRB` | Input | 4 | APB write strobes (byte lane enables). Honoured all the way through: the register block merges the strobed bytes into the stored value, and a counter load takes that merged value, so a PSTRB=0x1 write to COUNTERx_DATA loads {stored high byte, new low byte}. A write that strobes none of a register's bytes changes nothing and fires no command. |
| `s_apb_PPROT` | Input | 3 | APB protection attributes. Accepted for protocol completeness; not used by the decode. |
| `s_apb_PRDATA` | Output | 32 | APB read data. Valid when `s_apb_PREADY=1` and `s_apb_PWRITE=0`. |
| `s_apb_PREADY` | Output | 1 | APB ready. The wrapper converts APB to an internal command/response handshake, so PREADY inserts wait states: typically 2-3 `pclk` cycles single-clock, 4-6 cycles across the CDC. |
| `s_apb_PSLVERR` | Output | 1 | APB slave error. Asserted for any access whose address is not one of the seven mapped registers: the write is ignored, the read returns 0, and the transfer completes with PSLVERR high. Mapped accesses never error. |

**PIT Clock and Reset:**
| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `pit_clk` | Input | 1 | Timer clock. Used when `CDC_ENABLE=1` for independent timer clock domain. Ignored when `CDC_ENABLE=0`. |
| `pit_resetn` | Input | 1 | Timer reset, active-low. Used when `CDC_ENABLE=1`. Should be synchronous to `pit_clk`. Ignored when `CDC_ENABLE=0`. |

**Counter Control and Status:**
| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `gate_in[2:0]` | Input | 3 | GATE inputs for counters 0, 1, 2, active high. In Mode 0 a low GATE pauses the count where it stands and a high GATE resumes it from that value -- no reload, no restart -- as on the Intel 8254. A load is unaffected by GATE. The pins are treated as asynchronous in both clocking configurations and pass a `SYNC_STAGES`-flop synchronizer (default 2) on the counting clock, so a transition takes effect `SYNC_STAGES` counting clocks after the pin moves. No external synchronizer is needed. |
| `timer_irq[2:0]` | Output | 3 | Timer interrupt outputs. Driven by OUT signals from counters 0, 1, 2. High when terminal count reached (Mode 0). |

## Functional Description

### Address Map

`s_apb_PADDR` is 12 bits and all 12 are decoded: only the seven mapped
registers below are software-visible. Every other address in the 4 KB
window -- 0x01C, 0x020 and up -- is dropped: the write is ignored, the read
returns 0, and the access completes with PSLVERR. There are no aliases, and
the command strobes (control-word execution, counter loads, latch release)
are reached only through an address the decode has already accepted, so a
write that stores is a write that executes. This is the same policy as the
ioapic and pic_8259 blocks.

| Address Range | Register | Access | Description |
|---------------|----------|--------|-------------|
| `0x000` | PIT_CONFIG | RW | Global configuration (enable) |
| `0x004` | PIT_CONTROL | WO | Control word (8254-compatible) |
| `0x008` | PIT_STATUS | RO | Status readback (3 counters) |
| `0x00C` | RESERVED | - | Reserved |
| `0x010` | COUNTER0_DATA | RW | Counter 0 value |
| `0x014` | COUNTER1_DATA | RW | Counter 1 value |
| `0x018` | COUNTER2_DATA | RW | Counter 2 value |
| `0x01C` | - | - | Unmapped: dropped with PSLVERR (reads 0, write ignored) |
| `0x020-0xFFF` | - | - | Unmapped: dropped with PSLVERR (reads 0, write ignored) |

**Integration Note:** When integrating into a larger address space, these addresses are relative to the base address assigned to the PIT. For example, if the PIT is assigned base address `0x4000_2000`, then PIT_CONFIG would be at absolute address `0x4000_2000`.

### Error Response

Any access to an address other than the seven mapped registers is
acknowledged locally by `pit_config_regs` and answered with `s_apb_PSLVERR`
high: the write changes nothing, the read returns 0. The dropped access still
completes -- the adapter holds its request until an acknowledge, so the
decode acks the drop itself rather than leaving the bus waiting. Mapped
accesses never raise PSLVERR. Software can rely on the bus error to catch a
bad pointer into this window.

## Timing

### Clock Domain Configuration

**Single Clock Mode (CDC_ENABLE=0):**

**Connections:**
```systemverilog
// All logic uses pclk
apb4_slave      uses: pclk, presetn
pit_config_regs uses: pclk, presetn
pit_core       uses: pclk, presetn
pit_counter[*] uses: pclk, presetn

// pit_clk and pit_resetn are not used
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
apb4_slave_cdc uses: pclk for APB side, pit_clk for timer side
                    presetn for APB reset, pit_resetn for timer reset

// Timer logic uses pit_clk
pit_config_regs uses: pit_clk, pit_resetn
pit_core       uses: pit_clk, pit_resetn
pit_counter[*] uses: pit_clk, pit_resetn
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
- `gate_in` needs no special handling: its synchronizer runs on the counting
  clock in both configurations (`SYNC_STAGES` flops, default 2)

### Reset Requirements

**Power-On Reset Sequence:**

1. Assert both resets:
   ```
   presetn = 0
   pit_resetn = 0  (if CDC_ENABLE=1)
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
   pit_resetn = 1
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

### APB Protocol Timing

**Write Transaction:**

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

**Read Transaction:**

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

## Usage Example

### Single Clock Integration

```systemverilog
apb4_pit_8254 #(
    .NUM_COUNTERS(3),
    .CDC_ENABLE(0)
) u_apb4_pit_8254 (
    .pclk                  (pclk),
    .presetn               (presetn),
    .pit_clk               (pit_clk),
    .pit_resetn            (pit_resetn),
    .s_apb_PSEL            (s_apb_PSEL),
    .s_apb_PENABLE         (s_apb_PENABLE),
    .s_apb_PREADY          (s_apb_PREADY),
    .s_apb_PADDR           (s_apb_PADDR),
    .s_apb_PWRITE          (s_apb_PWRITE),
    .s_apb_PWDATA          (s_apb_PWDATA),
    .s_apb_PSTRB           (s_apb_PSTRB),
    .s_apb_PPROT           (s_apb_PPROT),
    .s_apb_PRDATA          (s_apb_PRDATA),
    .s_apb_PSLVERR         (s_apb_PSLVERR),
    .gate_in               (gate_in),
    .timer_irq             (timer_irq)
);
```

### Dual Clock Integration

```systemverilog
apb4_pit_8254 #(
    .NUM_COUNTERS(3),
    .CDC_ENABLE(1)
) u_apb4_pit_8254 (
    .pclk                  (pclk),
    .presetn               (presetn),
    .pit_clk               (pit_clk),
    .pit_resetn            (pit_resetn),
    .s_apb_PSEL            (s_apb_PSEL),
    .s_apb_PENABLE         (s_apb_PENABLE),
    .s_apb_PREADY          (s_apb_PREADY),
    .s_apb_PADDR           (s_apb_PADDR),
    .s_apb_PWRITE          (s_apb_PWRITE),
    .s_apb_PWDATA          (s_apb_PWDATA),
    .s_apb_PSTRB           (s_apb_PSTRB),
    .s_apb_PPROT           (s_apb_PPROT),
    .s_apb_PRDATA          (s_apb_PRDATA),
    .s_apb_PSLVERR         (s_apb_PSLVERR),
    .gate_in               (gate_in),
    .timer_irq             (timer_irq)
);
```

---

**Version:** 1.1
**Last Updated:** 2026-09-09
