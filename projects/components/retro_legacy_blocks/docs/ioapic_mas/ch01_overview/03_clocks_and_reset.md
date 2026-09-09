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

# ioapic

## Overview

The IOAPIC supports both single and dual clock domain operation via the `CDC_ENABLE` parameter. This chapter covers the clocking options, the reset behavior, and — the part that will bite you if you skip it — exactly which signals are synchronized and which are not.

## Functional Description

### Reset Signals

**Reset Types:**

| Signal | Polarity | Type | Domain | Purpose |
| --- | --- | --- | --- | --- |
| `presetn` | Active Low | Async | APB | Resets APB interface |
| `ioapic_resetn` | Active Low | Async | IOAPIC | Resets interrupt logic |

**Reset Routing (CDC_ENABLE determines which reset is used):**

```systemverilog
// In apb4_ioapic.sv:
assign config_regs_rst = (CDC_ENABLE != 0) ? ioapic_resetn : presetn;
assign core_rst = (CDC_ENABLE != 0) ? ioapic_resetn : presetn;
```

**CDC=0:** Both use `presetn`
**CDC=1:** Both use `ioapic_resetn`

### Reset Behavior

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
   - Output stage empty (irq_out_valid = 0)
   - All Remote IRR flags and delivered-vector latches cleared
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

### Reset Sequencing

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

**Reset the two domains together (CDC_ENABLE=1).** Resetting only one side
can make a pulse synchronizer in the LAPIC crossing fabricate a single edge.
Both consumers qualify what they receive - an accept needs a valid delivery
in the stage, an EOI needs a set Remote IRR - so a fabricated pulse after a
one-sided reset is a no-op rather than a lost or duplicated interrupt, but
the intended sequence is still both resets asserted at once.

## Timing

### Clock Domains

#### Single Clock Domain (CDC_ENABLE=0 - Default)

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
pclk ──┬──► apb4_slave (APB protocol)
       ├──► ioapic_config_regs (registers)
       └──► ioapic_core (interrupt logic)
```

#### Dual Clock Domain (CDC_ENABLE=1)

**Configuration:**
- APB interface uses `pclk`
- IOAPIC logic uses `ioapic_clk` (independent)
- `apb4_slave_cdc` provides clock domain crossing
- CMD/RSP signals cross domains via async FIFOs
- The CPU/LAPIC-facing interface (`irq_out_valid`, `irq_out_vector`,
  `irq_out_dest`, `irq_out_deliv_mode`, `irq_out_ready`, `eoi_in`,
  `eoi_vector`) is presented in `pclk` and crossed inside `apb4_ioapic`

**Advantages:**
- Independent clock frequencies
- Can gate `pclk` without losing interrupts: capture (synchronizers, edge
  latches, level tracking, arbitration) runs in `ioapic_clk`; presentation
  to the CPU waits for `pclk`, because the LAPIC-facing interface lives there
- Useful for power-managed systems

**Clock Routing:**
```
pclk ────► apb4_slave_cdc (APB protocol) ──┐
                                           │ CDC
ioapic_clk ──┬─────────────────────────────┴─► ioapic_config_regs
             └────────────────────────────────► ioapic_core
                                                    │
pclk ◄── irq_out_* / irq_out_ready / eoi_* ◄── LAPIC crossing (apb4_ioapic)
```

**LAPIC Interface Crossing (CDC_ENABLE=1):**
- Delivery request, ioapic_clk to pclk: classic four-phase handshake. The
  core's output stage raises a request flop, it crosses a 3-stage
  synchronizer, and the pclk side registers the payload into the
  LAPIC-facing `irq_out_*` outputs. The payload is quasi-static behind the
  handshake - the core cannot change it until the pclk side acks
- Accept, pclk to ioapic_clk: the pclk side's ack crosses back through a
  3-stage synchronizer and becomes a one-cycle `irq_out_ready` into the core.
  The request is then withdrawn and the ack withdrawn behind it before the
  next delivery can start - one full four-phase round trip per delivery,
  which is what keeps `irq_out_valid` visible for exactly one pclk cycle when
  the CPU holds `irq_out_ready` high (one handshake, countable)
- EOI, pclk to ioapic_clk: `eoi_in` is edge-detected in pclk, the vector is
  registered on that edge, and the pulse crosses through a 3-stage pulse
  synchronizer (`sync_pulse`). The vector is quasi-static until the next EOI
- Matched latency: the accept and the EOI cross through synchronizers of the
  same depth, so their pclk ORDER survives into ioapic_clk. That ordering is
  load-bearing - the core drops an EOI that arrives before the accept it
  belongs to, and an EOI synchronized against an accept sampled raw in
  ioapic_clk would have been re-ordered behind it
- CDC_ENABLE=0: no crossing; the core drives the LAPIC interface directly and
  `eoi_in` is consumed as-is (a multi-cycle strobe is harmless there, the
  Remote IRR clear is idempotent)

**Latency Impact:**
- Register access: +2-4 cycles for CDC handshake
- Total: ~4-6 APB cycles vs ~2 cycles for non-CDC
- Delivery request to `irq_out_valid`: +1 ioapic_clk (request flop) + 3 pclk
  (synchronizer) + 1 pclk (LAPIC-facing register)
- Back-to-back deliveries: gated by the four-phase round trip (two
  synchronizer traversals in each direction)

### Clock Requirements

**Frequency Constraints:**

| Clock | Minimum | Typical | Maximum | Notes |
| --- | --- | --- | --- | --- |
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

### Interrupt Response Time

**From IRQ assertion to delivery request:**

| Configuration | Synchronization | Edge Detect | Arbitration | Delivery | Total |
| --- | --- | --- | --- | --- | --- |
| No CDC, 100 MHz | 30 ns (3 cycles) | 10 ns (1 cycle) | 0 ns (combinational) | 10 ns (1 cycle) | ~50 ns (5 cycles) |
| CDC, pclk=50MHz, ioapic_clk=100MHz | 30 ns (3 cycles) | 10 ns (1 cycle) | 0 ns (combinational) | 10 ns (1 cycle) + crossing: 10 ns (1 ioapic_clk) + 80 ns (4 pclk) | ~140 ns |

**Note:** Above is from IRQ pin to `irq_out_valid`. CPU interrupt latency depends on LAPIC design.

### Timing Constraints

**Critical Paths (for synthesis):**

**Without CDC:**
- APB write → register update → core config: Single clock domain
- IRQ input → synchronizer → edge detect → arbitration → delivery: ~4-5 levels of logic
- Typical Fmax: 150-200 MHz (depends on synthesis settings)

**With CDC:**
- APB domain: Same as without CDC
- IOAPIC domain: IRQ path same as above
- Cross-domain: APB CMD/RSP through async FIFOs; LAPIC interface through
  the four-phase request and pulse synchronizers (no combinational paths)
- Constrain the quasi-static payloads: with CDC_ENABLE=1 the delivery
  payload buses (vector, dest, delivery mode - ioapic_clk into pclk) and the
  registered EOI vector (pclk into ioapic_clk) are multi-cycle-path crossings
  held stable behind the four-phase and pulse handshakes. A build must
  declare them as such - `set_max_delay -datapath_only` across the crossing,
  or `set_false_path` - or they show up as timing failures against a clock
  they were never meant to meet. rlb_top uses CDC_ENABLE=0 and has none of
  these paths
- Typical Fmax: 150-200 MHz each domain independently

**Setup/Hold:**
- IRQ inputs: Asynchronous, 3-stage internal sync
- LAPIC interface (`irq_out_*`, `irq_out_ready`, `eoi_in`, `eoi_vector`):
  synchronous to `pclk` in both configurations. With CDC_ENABLE=1 the
  crossing into ioapic_clk is inside the block (fixed 2026-09-09, issue #48 -
  the EOI used to reach the core with no synchronizer at all)
- EOI rate contract (CDC_ENABLE=1): consecutive `eoi_in` strobes at least
  3 x T_ioapic_clk + 2 x T_pclk apart (the pulse synchronizer's spacing
  requirement). Closer than that, the two strobes land inside one
  destination sample window, toggle the pulse synchronizer twice, and BOTH
  are lost silently - not one - leaving two level pins in service with
  nothing reported. An EOI must also be at least one pclk cycle away from
  the delivery accept it is ordered against. One EOI per delivered interrupt
  and a delivery round trip costs far more than that, so software cannot
  legitimately hit either limit
- APB signals: Per APB specification

### Clock Jitter and Stability

**IRQ Input Synchronization:**
- 3-stage synchronizer handles moderate jitter
- MTBF (Mean Time Between Failures): >1000 years at 100 MHz
- No special jitter requirements on IRQ inputs

**Clock Source Requirements:**
- Stable clock (< 100 ppm drift typical)
- Low jitter for timing-critical applications
- FPGA PLLs/MMCMs acceptable

## Design Notes

### Clock Gating Considerations

**With CDC_ENABLE=1:**

**Can gate pclk when:**
- No APB accesses needed
- Power saving mode
- IOAPIC capture still operational on `ioapic_clk`
- Interrupts are held, not lost: an edge stays latched, a level stays
  tracked, and a delivery already in the output stage waits in the
  four-phase request until `pclk` resumes. Nothing is presented to the CPU,
  and no EOI is consumed, while `pclk` is stopped - so a wake-up source must
  be routed outside this interface

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

## Navigation

**See Also:**
- [Architecture](02_architecture.md) - Clock domain architecture diagrams
- [Top Level Interface](../ch03_interfaces/01_top_level.md) - Clock signal definitions
- [APB Interface](../ch03_interfaces/02_apb_interface_spec.md) - APB timing

**Next:** [Chapter 1.4 - Acronyms](04_acronyms.md)
