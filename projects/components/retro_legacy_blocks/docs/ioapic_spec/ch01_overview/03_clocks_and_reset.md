### APB IOAPIC - Clocks and Reset

#### Clock Domains

The IOAPIC supports both single and dual clock domain operation via the `CDC_ENABLE` parameter.

##### Single Clock Domain (CDC_ENABLE=0 - Default)

**Configuration:**
- Both APB interface and IOAPIC logic use same clock (`pclk`)
- `ioapic_clk` parameter tied to `pclk`
- No clock domain crossing logic instantiated

**Advantages:**
- Simplest configuration
- Lowest latency (~2 APB cycles for register access)
- Single clock timing constraints
- Recommended for most applications

**Clock Routing:**
```
pclk ──┬──► apb_slave (APB protocol)
       ├──► ioapic_config_regs (registers)
       └──► ioapic_core (interrupt logic)
```

##### Dual Clock Domain (CDC_ENABLE=1)

**Configuration:**
- APB interface uses `pclk`
- IOAPIC logic uses `ioapic_clk` (independent)
- `apb_slave_cdc` provides clock domain crossing
- CMD/RSP signals cross domains via async FIFOs

**Advantages:**
- Independent clock frequencies
- Can gate `pclk` while maintaining interrupt capability
- Supports always-on interrupt handling
- Useful for power-managed systems

**Clock Routing:**
```
pclk ────► apb_slave_cdc (APB protocol) ──┐
                                           │ CDC
ioapic_clk ──┬─────────────────────────────┴─► ioapic_config_regs
             └────────────────────────────────► ioapic_core
```

**Latency Impact:**
- Register access: +2-4 cycles for CDC handshake
- Total: ~4-6 APB cycles vs ~2 cycles for non-CDC

#### Clock Requirements

**Frequency Constraints:**

| Clock | Minimum | Typical | Maximum | Notes |
|-------|---------|---------|---------|-------|
| `pclk` | 1 MHz | 50-100 MHz | 200 MHz | APB bus clock |
| `ioapic_clk` (CDC=0) | Same as pclk | Same as pclk | Same as pclk | Tied to pclk |
| `ioapic_clk` (CDC=1) | 1 MHz | 25-100 MHz | 200 MHz | Independent |

**Relationship (CDC=1):**
- No fixed relationship required between `pclk` and `ioapic_clk`
- Can be asynchronous
- Ratio can be arbitrary
- CDC logic handles all synchronization

**Typical Configurations:**
- **No CDC:** pclk = ioapic_clk = 100 MHz (system clock)
- **With CDC:** pclk = 50 MHz (APB), ioapic_clk = 100 MHz (fast interrupts)
- **Power-managed:** pclk = gatable, ioapic_clk = always-on 32 kHz

#### Interrupt Response Time

**From IRQ assertion to delivery request:**

| Configuration | Synchronization | Edge Detect | Arbitration | Delivery | Total |
|---------------|-----------------|-------------|-------------|----------|-------|
| No CDC, 100 MHz | 30 ns | 10 ns | <10 ns | 10 ns | ~60 ns |
| CDC, pclk=50MHz, ioapic_clk=100MHz | 30 ns | 10 ns | <10 ns | 10 ns | ~60 ns |

**Note:** Above is from IRQ pin to `irq_out_valid`. CPU interrupt latency depends on LAPIC design.

#### Reset Signals

**Reset Types:**

| Signal | Polarity | Type | Domain | Purpose |
|--------|----------|------|--------|---------|
| `presetn` | Active Low | Async | APB | Resets APB interface |
| `ioapic_resetn` | Active Low | Async | IOAPIC | Resets interrupt logic |

**Reset Routing (CDC_ENABLE determines which reset is used):**

```systemverilog
// In apb_ioapic.sv:
assign config_regs_rst = (CDC_ENABLE[0]) ? ioapic_resetn : presetn;
assign core_rst = (CDC_ENABLE[0]) ? ioapic_resetn : presetn;
```

**CDC=0:** Both use `presetn`
**CDC=1:** Both use `ioapic_resetn`

#### Reset Behavior

**On Reset Assertion:**

1. **APB Interface:**
   - APB slave returns to IDLE
   - All pending transactions aborted
   - PREADY deasserted

2. **Registers:**
   - IOREGSEL ← 0x00
   - IOAPICID ← 0x00000000
   - All IOREDTBL entries ← default (all IRQs masked)

3. **Core Logic:**
   - All IRQ pending flags cleared
   - Delivery FSM → IDLE
   - All Remote IRR flags cleared
   - Synchronizer chains reset
   - No interrupts pending or being delivered

**Redirection Table Reset Values:**
- Vector: 0x00
- Delivery Mode: 0b000 (Fixed)
- Dest Mode: 0 (Physical)
- Delivery Status: 0 (Idle)
- Polarity: 0 (Active High)
- Remote IRR: 0
- Trigger Mode: 0 (Edge)
- **Mask: 1 (MASKED)** ← Critical: All IRQs disabled by default
- Destination: 0x00

**After reset, software must:**
1. Configure IOAPIC ID (if multiple IOAPICs)
2. Configure each needed IRQ's redirection entry
3. Unmask desired IRQs (clear mask bit)

#### Reset Sequencing

**Power-On Reset:**
```
1. Power stabilizes
2. POR circuitry asserts presetn/ioapic_resetn
3. Hold reset for minimum 10 clock cycles
4. Deassert reset synchronously
5. Wait 5 clock cycles for synchronizers
6. Begin software initialization
```

**Software Reset (via PM_ACPI if integrated):**
```
1. PM_ACPI asserts system reset
2. presetn/ioapic_resetn asserted
3. IOAPIC returns to reset state
4. Software must reinitialize all config
```

#### Clock Gating Considerations

**With CDC_ENABLE=1:**

**Can gate pclk when:**
- No APB accesses needed
- Power saving mode
- IOAPIC still operational on `ioapic_clk`
- Interrupts continue to function

**Cannot gate ioapic_clk when:**
- Interrupts must be serviced
- Need real-time interrupt response
- Unless entering deep power-down (then reinit required)

**Integration with PM_ACPI:**
If using PM_ACPI power management:
- Connect IOAPIC to always-on power domain
- Use `ioapic_clk` from always-on clock tree
- Enable CDC (CDC_ENABLE=1)
- IOAPIC continues operating in S1/S3 sleep states

#### Timing Constraints

**Critical Paths (for synthesis):**

**Without CDC:**
- APB write → register update → core config: Single clock domain
- IRQ input → synchronizer → edge detect → arbitration → delivery: ~4-5 levels of logic
- Typical Fmax: 150-200 MHz (depends on synthesis settings)

**With CDC:**
- APB domain: Same as without CDC
- IOAPIC domain: IRQ path same as above
- Cross-domain: Handled by async FIFOs (no combinational paths)
- Typical Fmax: 150-200 MHz each domain independently

**Setup/Hold:**
- IRQ inputs: Externally synchronized, 3-stage internal sync
- EOI inputs: Should be synchronous to ioapic_clk if possible
- APB signals: Per APB specification

#### Clock Jitter and Stability

**IRQ Input Synchronization:**
- 3-stage synchronizer handles moderate jitter
- MTBF (Mean Time Between Failures): >1000 years at 100 MHz
- No special jitter requirements on IRQ inputs

**Clock Source Requirements:**
- Stable clock (< 100 ppm drift typical)
- Low jitter for timing-critical applications
- FPGA PLLs/MMCMs acceptable

---

**See Also:**
- [Architecture](02_architecture.md) - Clock domain architecture diagrams
- [Top Level Interface](../ch03_interfaces/01_top_level.md) - Clock signal definitions
- [APB Interface](../ch03_interfaces/02_apb_interface_spec.md) - APB timing

**Next:** [Chapter 1.4 - Acronyms](04_acronyms.md)
