### APB IOAPIC - FSM Summary

#### Interrupt Delivery State Machine

The IOAPIC core implements a 3-state FSM for interrupt delivery management.

##### State Definitions

| State | Encoding | Description |
|-------|----------|-------------|
| **IDLE** | 2'b00 | No interrupt being delivered, arbitrating among pending IRQs |
| **DELIVER** | 2'b01 | Presenting interrupt to CPU, waiting for acknowledgment |
| **WAIT_EOI** | 2'b10 | Level interrupt delivered, waiting for End-of-Interrupt |

##### State Transition Diagram

```
                  ┌──────────────────────────────┐
                  │                              │
                  ▼                              │
          ┌───────────────┐                      │
          │     IDLE      │                      │
          │               │                      │
          │ • Arbitrate   │                      │
          │ • Select IRQ  │                      │
          └───────┬───────┘                      │
                  │                              │
                  │ IRQ pending &                │
                  │ unmasked                     │
                  ▼                              │
          ┌───────────────┐                      │
          │    DELIVER    │                      │
          │               │                      │
          │ • Assert      │                      │
          │   irq_out_    │                      │
          │   valid       │                      │
          └───────┬───────┘                      │
                  │                              │
         ┌────────┴────────┐                     │
         │                 │                     │
    Edge │                 │ Level               │
    Mode │                 │ Mode                │
         │                 │                     │
         │                 ▼                     │
         │         ┌───────────────┐             │
         │         │   WAIT_EOI    │             │
         │         │               │             │
         │         │ • Remote IRR  │             │
         │         │   set         │             │
         │         │ • Wait for    │             │
         │         │   EOI         │             │
         │         └───────┬───────┘             │
         │                 │                     │
         │                 │ eoi_in &&           │
         │                 │ vector match        │
         │                 │                     │
         └─────────────────┴─────────────────────┘
```

##### State Transitions

| Current State | Condition | Next State | Action |
|---------------|-----------|------------|--------|
| **IDLE** | No pending IRQs | IDLE | Continue arbitration |
| **IDLE** | Pending IRQ found | DELIVER | Latch IRQ info, assert irq_out_valid |
| **DELIVER** | !irq_out_ready | DELIVER | Wait for CPU |
| **DELIVER** | irq_out_ready && edge mode | IDLE | Complete, return to arbitration |
| **DELIVER** | irq_out_ready && level mode | WAIT_EOI | Set Remote IRR, wait for EOI |
| **WAIT_EOI** | !(eoi_in && vector match) | WAIT_EOI | Continue waiting |
| **WAIT_EOI** | eoi_in && vector match | IDLE | Clear Remote IRR, return |

##### State Functions

**IDLE State:**
- **Entry:** From WAIT_EOI (after EOI) or DELIVER (after edge interrupt)
- **Operations:**
  - Scan all 24 IRQs for pending, unmasked interrupts
  - Apply priority arbitration (lowest IRQ number wins)
  - Select highest priority IRQ if any
- **Outputs:**
  - irq_out_valid = 0 (no interrupt being presented)
- **Exit:** When pending IRQ found → DELIVER

**DELIVER State:**
- **Entry:** From IDLE when pending IRQ exists
- **Operations:**
  - Assert irq_out_valid
  - Present irq_out_vector (from selected IRQ's redirection entry)
  - Present irq_out_dest (destination APIC ID)
  - Present irq_out_deliv_mode (delivery mode)
  - Wait for CPU acknowledgment (irq_out_ready)
- **Outputs:**
  - irq_out_valid = 1
  - irq_out_vector = cfg_vector[selected_irq]
  - irq_out_dest = cfg_destination[selected_irq]
  - irq_out_deliv_mode = cfg_deliv_mode[selected_irq]
- **Exit:** 
  - Edge mode + irq_out_ready → IDLE
  - Level mode + irq_out_ready → WAIT_EOI

**WAIT_EOI State (Level-Triggered Only):**
- **Entry:** From DELIVER after CPU accepts level interrupt
- **Operations:**
  - Monitor eoi_in signal
  - Compare eoi_vector with current_vector
  - Remote IRR remains set (prevents re-trigger)
  - IRQ input still synchronized but masked by Remote IRR
- **Outputs:**
  - irq_out_valid = 0
- **Exit:** When EOI received for this vector → IDLE

##### Latched Signals

**Signals latched in IDLE → DELIVER transition:**

| Signal | Source | Purpose |
|--------|--------|---------|
| current_irq[4:0] | selected_irq | IRQ number being delivered |
| current_vector[7:0] | cfg_vector[selected_irq] | Vector for EOI matching |
| current_is_level | cfg_trigger_mode[selected_irq] | Determines path (IDLE vs WAIT_EOI) |

**These remain stable during DELIVER and WAIT_EOI states.**

##### Edge vs Level Interrupt Paths

**Edge-Triggered Interrupt:**
```
IRQ asserts → Edge detected → IRQ pending flag set →
Arbitration selects it → IDLE → DELIVER → 
CPU acknowledges → Pending cleared → IDLE
```
**Time:** Depends on arbitration delay, typically 1-2 cycles in IDLE then 1+ cycles in DELIVER

**Level-Triggered Interrupt:**
```
IRQ asserts → Level sensed → IRQ pending (if !Remote IRR) →
Arbitration selects it → IDLE → DELIVER → 
CPU acknowledges → Remote IRR set → WAIT_EOI →
EOI received → Remote IRR cleared → IDLE →
(If IRQ still asserted, pending again)
```
**Time:** Same as edge until WAIT_EOI, then waits for software ISR completion + EOI

#### Arbitration Logic

**Priority Encoding (Static Priority):**
```systemverilog
// In ioapic_core.sv
for (int j = 0; j < 24; j++) begin
    if (irq_eligible[j]) begin  // Pending and not masked
        selected_irq = j;
        irq_selected_valid = 1;
        break;  // Stop at first match (lowest wins)
    end
end
```

**Eligibility Criteria:**
```systemverilog
irq_eligible[i] = irq_pending[i] && !cfg_mask[i];
```

**Arbitration Timing:**
- Combinational logic (< 1 clock cycle)
- Result available same cycle for IDLE → DELIVER transition

#### Remote IRR Management

**Set Conditions:**
```systemverilog
// For level-triggered IRQs only
if (cfg_trigger_mode[i] == 1'b1) begin  // Level mode
    if (irq_selected_valid && selected_irq == i && state == IDLE) begin
        remote_irr[i] <= 1'b1;  // Set when starting delivery
    end
end
```

**Clear Conditions:**
```systemverilog
if (eoi_in && eoi_vector == cfg_vector[i]) begin
    remote_irr[i] <= 1'b0;  // Clear on EOI
end
```

**Effect on Pending:**
```systemverilog
// Level mode: Pending only if active AND Remote IRR clear
irq_pending[i] = irq_active[i] && !irq_remote_irr[i];
```

This prevents level interrupts from re-triggering while being serviced.

#### Multiple Pending IRQs

**Scenario:** Multiple IRQs asserted simultaneously

**Behavior:**
1. Arbitration selects lowest numbered IRQ
2. FSM delivers that interrupt (IDLE → DELIVER [→ WAIT_EOI])
3. Other IRQs remain pending
4. After current delivery complete, FSM returns to IDLE
5. Arbitration runs again, selects next lowest
6. Process repeats until all serviced

**Example Timeline:**
```
Time 0:   IRQ3, IRQ5, IRQ7 all assert
Time 1:   Arbitration selects IRQ3 (lowest)
Time 2-5: Deliver IRQ3, wait if level
Time 6:   Return to IDLE
Time 7:   Arbitration selects IRQ5 (next lowest)
Time 8-11: Deliver IRQ5, wait if level
Time 12:  Return to IDLE
Time 13:  Arbitration selects IRQ7
...
```

**Fairness:** Lower numbered IRQs starve higher if constantly asserting. This is intentional (priority system).

---

**See Also:**
- [ioapic_core Block](01_ioapic_core.md) - Detailed FSM implementation
- [Programming: Level Interrupts](../ch04_programming/04_level_triggered_irq.md) - FSM from software perspective

**Back to:** [Index](../ioapic_index.md) | [Block Overview](00_overview.md)
