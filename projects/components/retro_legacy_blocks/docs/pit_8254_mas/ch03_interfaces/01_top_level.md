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

## Ports

### Module Declaration

```systemverilog
module apb4_pit_8254 #(
    parameter int NUM_COUNTERS = 3,  // Number of counters (fixed at 3)
    parameter bit CDC_ENABLE   = 0,  // 0=single clock, 1=dual clock with CDC
    parameter int USE_JOHNSON  = 0   // CDC FIFO pointer encoding: 0=Gray, 1=Johnson
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
| `s_apb_PADDR` | Input | 12 | APB address. The register block decodes only bits [4:0] (32-byte window); see Address Map below. |
| `s_apb_PSEL` | Input | 1 | APB select. Asserted by interconnect when this peripheral is accessed. |
| `s_apb_PENABLE` | Input | 1 | APB enable. Asserted in second cycle of transfer (access phase). |
| `s_apb_PWRITE` | Input | 1 | APB write/read. 1=write, 0=read. |
| `s_apb_PWDATA` | Input | 32 | APB write data. Valid only when `s_apb_PWRITE=1`. |
| `s_apb_PSTRB` | Input | 4 | APB write strobes (byte lane enables). Honored by the register STORAGE, but the counter-load capture takes all 16 bits of PWDATA unconditionally -- a partial-word COUNTERx_DATA write loads bus garbage into the unstrobed byte while storage keeps only the strobed one (RTL asymmetry, #52). Write COUNTERx_DATA full-word only. |
| `s_apb_PPROT` | Input | 3 | APB protection attributes. Accepted for protocol completeness; not used by the decode. |
| `s_apb_PRDATA` | Output | 32 | APB read data. Valid when `s_apb_PREADY=1` and `s_apb_PWRITE=0`. |
| `s_apb_PREADY` | Output | 1 | APB ready. The wrapper converts APB to an internal command/response handshake, so PREADY inserts wait states: typically 2-3 `pclk` cycles single-clock, 4-6 cycles across the CDC. |
| `s_apb_PSLVERR` | Output | 1 | APB slave error. Never asserted by this design: the register block's error outputs are tied off, so unmapped reads return 0 and unmapped writes are silently ignored. |

**PIT Clock and Reset:**
| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `pit_clk` | Input | 1 | Timer clock. Used when `CDC_ENABLE=1` for independent timer clock domain. Ignored when `CDC_ENABLE=0`. |
| `pit_resetn` | Input | 1 | Timer reset, active-low. Used when `CDC_ENABLE=1`. Should be synchronous to `pit_clk`. Ignored when `CDC_ENABLE=0`. |

**Counter Control and Status:**
| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `gate_in[2:0]` | Input | 3 | GATE inputs for counters 0, 1, 2. GATE is a start enable: it is sampled when a count is loaded (and when re-arming after terminal count). Once a count is in progress, GATE transitions have no effect - the counter does NOT pause. This deviates from the Intel 8254, where Mode 0 counting suspends while GATE is low (tracked as an RTL issue). GATE has NO synchronizer into the pit_clk domain -- with CDC_ENABLE=1 it must be driven synchronously to pit_clk or externally synchronized (#52). |
| `timer_irq[2:0]` | Output | 3 | Timer interrupt outputs. Driven by OUT signals from counters 0, 1, 2. High when terminal count reached (Mode 0). |

## Functional Description

### Address Map

`s_apb_PADDR` is 12 bits, but the register block decodes only address bits
[4:0], giving a 32-byte register window that ALIASES throughout the 4 KB
region: every 0x20 stride repeats the same registers for READS (0x020
reads PIT_CONFIG, and so on) -- but only for READS and for PIT_CONFIG writes: the command strobes
(control-word execution, counter loads) compare the FULL 12-bit
address, so a PIT_CONTROL or COUNTERx_DATA write through an alias
(0x024, 0x210, ...) updates storage without configuring or loading
anything -- a silent no-op (RTL asymmetry, #52). Use base offsets
for all command/data writes.
Within the window, 0x01C is the
only unmapped word - it reads as 0 and ignores writes. No access ever raises
PSLVERR (the error outputs are tied off).

| Address Range | Register | Access | Description |
|---------------|----------|--------|-------------|
| `0x000` | PIT_CONFIG | RW | Global configuration (enable) |
| `0x004` | PIT_CONTROL | WO | Control word (8254-compatible) |
| `0x008` | PIT_STATUS | RO | Status readback (3 counters) |
| `0x00C` | RESERVED | - | Reserved |
| `0x010` | COUNTER0_DATA | RW | Counter 0 value |
| `0x014` | COUNTER1_DATA | RW | Counter 1 value |
| `0x018` | COUNTER2_DATA | RW | Counter 2 value |
| `0x01C` | - | - | Unmapped (reads 0, writes ignored, no error) |
| `0x020-0xFFF` | - | - | Aliases of the 32-byte window above (decode is [4:0]) |

**Integration Note:** When integrating into a larger address space, these addresses are relative to the base address assigned to the PIT. For example, if the PIT is assigned base address `0x4000_2000`, then PIT_CONFIG would be at absolute address `0x4000_2000`.

### Error Response

There is none. The register block's error outputs are tied off
(`cpuif_wr_err = '0`, `readback_err = '0`), so `s_apb_PSLVERR` stays low for
every access: an unmapped or aliased address reads as 0 (or the aliased
register's value). Aliased WRITES are not symmetrical -- see the address-map
note above: only PIT_CONFIG writes take effect through aliases; command and
counter-data writes are silent no-ops off their base offsets.
Software cannot rely on a bus error to catch a bad pointer into this window.

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

**Version:** 1.0
**Last Updated:** 2025-11-08
