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

The IOAPIC core has no delivery state machine. The delivery path is a one-entry valid/ready output stage fed by the arbiter, and the only other state that matters is a Remote IRR bit per pin. That is a smaller thing than the three-state FSM this chapter used to describe (idle / deliver / wait-for-EOI, retired with issue #48 on 2026-09-09), and it is smaller for a reason: the three states carried nothing the handshake and the per-pin bits do not. The corner cases still live in the edge/level split and the Remote IRR bookkeeping, so this is still the page to have open while reading `ioapic_core.sv`.

## Functional Description

### State Definitions

| State | Where it lives | Description |
| --- | --- | --- |
| **Stage empty** | `r_out_valid = 0` | Nothing presented to the CPU; the arbiter's pick, if any, loads next cycle |
| **Stage full** | `r_out_valid = 1` | One delivery presented on `irq_out_valid`/vector/dest; waiting for `irq_out_ready` |
| **In service** | `r_remote_irr[i] = 1` | Level pin `i` has been accepted and not yet EOI'd; that pin alone is masked from arbitration |

The old encoding mapped onto these as: idle = stage empty, deliver = stage full, and wait-for-EOI = "some pin in service". The difference is that the old wait state blocked everything, and "in service" blocks one pin.

### State Transition Diagram

```
                     w_sel_valid && (!r_out_valid || irq_out_ready)
                     (arbiter has a pick, stage empty or emptying)
          ┌──────────────────────────────────────────────────────┐
          │                                                      │
          ▼                                                      │
  ┌───────────────┐   irq_out_ready && no new pick   ┌───────────┴───┐
  │  STAGE EMPTY  │◄─────────────────────────────────│  STAGE FULL   │
  │ r_out_valid=0 │                                  │ r_out_valid=1 │
  │               │─────────────────────────────────►│ irq_out_valid │
  └───────────────┘   load pick                      └───────┬───────┘
                                                             │ accept =
                                                             │ r_out_valid && irq_out_ready
                                                             ▼
                                   ┌─────────────────────────┴──────────────────────────┐
                                   │ retiring pin i, this cycle:                        │
                                   │  - edge : r_irq_pending[i] <= 0 (a new edge wins)  │
                                   │  - level: r_remote_irr[i]  <= 1 (pin in service)   │
                                   │  - both : r_delivered_vector[i] <= r_out_vector    │
                                   │  - pin i masked from this cycle's arbitration      │
                                   └────────────────────────────────────────────────────┘

  Per level pin, independent of the stage:
     r_remote_irr[i]: 0 ──(accept, level)──► 1 ──(eoi_in && eoi_vector == r_delivered_vector[i])──► 0
```

### State Transitions

| Current State | Condition | Next State | Action |
| --- | --- | --- | --- |
| **Stage empty** | No eligible pin | Stage empty | Keep arbitrating |
| **Stage empty** | Eligible pin found | Stage full | Register pick: index, vector, dest, delivery mode, trigger mode |
| **Stage full** | !irq_out_ready | Stage full | Hold; outputs are registered and do not change |
| **Stage full** | irq_out_ready, another pin eligible | Stage full | Accept the current one, load the next in the same cycle (no bubble) |
| **Stage full** | irq_out_ready, nothing eligible | Stage empty | Accept, drop `irq_out_valid` |
| **Remote IRR[i] = 0** | Accept of level pin i | Remote IRR[i] = 1 | Pin i leaves arbitration; the stage is free immediately |
| **Remote IRR[i] = 1** | eoi_in && eoi_vector == delivered vector of pin i | Remote IRR[i] = 0 | Pin i re-enters arbitration next cycle if still asserted |
| **Remote IRR[i] = 1** | EOI with any other vector | Remote IRR[i] = 1 | Other pins unaffected; only pin i stays blocked |

### State Functions

**Stage empty:**
- **Entry:** From stage full when the CPU accepts and no other pin is eligible; from reset
- **Operations:**
  - Scan all 24 pins for eligible requests (requesting, unmasked, not in service, not being retired this cycle)
  - Apply priority arbitration (lowest IRQ number wins)
  - Load the winner into the output stage
- **Outputs:**
  - irq_out_valid = 0; vector, dest and delivery mode read as 0
- **Exit:** When an eligible pin exists

**Stage full:**
- **Entry:** From stage empty on a load, or from stage full when an accept and a load coincide
- **Operations:**
  - Hold irq_out_valid with the registered vector, destination and delivery mode
  - Wait for the CPU (irq_out_ready)
- **Outputs:**
  - irq_out_valid = 1
  - irq_out_vector = the vector registered at load time
  - irq_out_dest = the destination registered at load time
  - irq_out_deliv_mode = the delivery mode registered at load time
  - (registered, so a mid-delivery RTE rewrite does NOT change what is presented; the next delivery of that pin uses the new values)
- **Exit:** On accept (`r_out_valid && irq_out_ready`), every time - one accept retires exactly one delivery. Edge pins clear their pending latch on that accept, in the same cycle, which is what makes each edge deliver once.

**In service (level pins, per pin):**
- **Entry:** Accept of a level delivery - not presentation. An EOI that arrives while the delivery is still unaccepted finds Remote IRR clear and is dropped rather than pre-clearing anything
- **Operations:**
  - Remote IRR set; the pin is masked from arbitration
  - The input is still synchronized, so its live level is visible the moment Remote IRR clears
  - Every other pin keeps arbitrating and delivering
- **Outputs:**
  - status_remote_irr[i] = 1
- **Exit:** EOI whose vector equals the vector delivered on this pin (latched at accept). The compare runs on every pin, so one EOI clears every pin delivered with that vector - two pins sharing a vector leave service together. A lost or wrong-vector EOI leaves this pin, and only this pin, blocked.

### Latched Signals

**Signals registered when the stage loads:**

| Signal | Source | Purpose |
| --- | --- | --- |
| r_out_irq[4:0] | w_sel_irq | Pin being delivered; selects which pending/Remote IRR bit the accept touches |
| r_out_vector[7:0] | cfg_vector[w_sel_irq] | Presented on irq_out_vector; copied into r_delivered_vector on accept |
| r_out_dest[7:0] | cfg_destination[w_sel_irq] | Presented on irq_out_dest |
| r_out_deliv_mode[2:0] | cfg_deliv_mode[w_sel_irq] | Presented on irq_out_deliv_mode |

**Signal registered on accept, per pin:**

| Signal | Source | Purpose |
| --- | --- | --- |
| r_delivered_vector[i][7:0] | r_out_vector | The vector the CPU actually received; the EOI is matched against this, not the live RTE |

**These remain stable while the stage is full; the delivered vector stays until the pin's next accept.**

### Edge vs Level Interrupt Paths

**Edge-Triggered Interrupt:**
```
IRQ asserts -> rising edge of the polarity-adjusted level -> r_irq_pending set ->
arbitration selects it -> stage loads -> irq_out_valid ->
CPU accepts -> pending cleared (same cycle; a coincident new edge sets instead) -> done
```
**Time:** 3 sync cycles + 1 edge-detect cycle + 1 load cycle to `irq_out_valid`; the delivery retires on the first cycle the CPU holds `irq_out_ready`.

**Polarity:** flipping an RTE's polarity bit inverts the active level, which would read as a rising edge - so the edge detector for that pin is suppressed for one cycle after the bit changes, and the flip itself never latches a pending interrupt. Software may change polarity on an idle pin without a spurious delivery.

**Level-Triggered Interrupt:**
```
IRQ asserts -> synchronized level is the request (no latch, gated by Remote IRR) ->
arbitration selects it -> stage loads -> irq_out_valid ->
CPU accepts -> Remote IRR set, delivered vector latched, stage free ->
(other pins deliver meanwhile) ->
EOI with the delivered vector -> Remote IRR cleared ->
if the level is still asserted, it re-requests the next cycle and is delivered again, once
```
**Time:** Same as edge to the accept; the pin then waits for the ISR and its EOI, but the block does not.

### Arbitration Logic

**Priority Encoding (Static Priority):**
```systemverilog
// In ioapic_core.sv
for (int j = 0; j < NUM_IRQS; j++) begin
    if (w_irq_eligible[j]) begin
        w_sel_irq   = IRQ_IDX_W'(j);
        w_sel_valid = 1'b1;
        break;  // Stop at first match (lowest number)
    end
end
```

**Eligibility Criteria:**
```systemverilog
// Edge pins request from the latch, level pins from the live synchronized level
assign w_irq_request[i]  = cfg_trigger_mode[i] ? w_irq_active[i] : r_irq_pending[i];

assign w_irq_eligible[i] = w_irq_request[i]
                         && !cfg_mask[i]
                         && !r_remote_irr[i]
                         && !(w_deliv_accept && (r_out_irq == IRQ_IDX_W'(i)));
```

The last term masks the pin being accepted from the arbitration happening in the same cycle. Without it the retiring pin is still requesting while its latch is being cleared (or its Remote IRR set) and wins one more round - exactly the double delivery of issue #48.

**Arbitration Timing:**
- Combinational (< 1 clock cycle)
- Result loads into the output stage on the next edge whenever the stage is empty or being accepted:
```systemverilog
assign w_out_load = w_sel_valid && (!r_out_valid || irq_out_ready);
```

### Remote IRR Management

**Set Conditions:**
```systemverilog
// For level-triggered IRQs only, on the ACCEPT of this pin's delivery.
// The LIVE trigger mode arms this branch, not a copy sampled at load:
// an edge->level rewrite during an in-flight delivery must still land
// in service, or the live level would re-deliver forever.
if (cfg_trigger_mode[i] == 1'b1) begin
    if (w_deliv_accept && (r_out_irq == IRQ_IDX_W'(i))) begin
        r_remote_irr[i] <= 1'b1;
    end
```

**Clear Conditions:**
```systemverilog
    end else if (eoi_in && (eoi_vector == r_delivered_vector[i])) begin
        r_remote_irr[i] <= 1'b0;   // matched against the DELIVERED vector, not cfg_vector
    end
end
```

An accept and a matching EOI in the same cycle: the accept wins, because the pin has just re-entered service. An EOI for a pin whose Remote IRR is already clear is a no-op. The compare is per pin and every pin runs it on the same EOI, so two level pins delivered with the same vector both clear on one EOI, as on the 82093AA - sharing a vector is legal, it just means one EOI retires both.

**Effect on Eligibility:**
```systemverilog
// Level mode: the live level requests, but only while this pin is not in service
w_irq_eligible[i] = w_irq_active[i] && !cfg_mask[i] && !r_remote_irr[i] && ...;
```

This prevents a level interrupt from re-triggering while it is being serviced, and stops there: nothing about pin i's service state touches pin j.

### Multiple Pending IRQs

**Scenario:** Multiple IRQs asserted simultaneously

**Behavior:**
1. Arbitration selects the lowest numbered eligible pin
2. The stage presents it (`irq_out_valid`)
3. Other pins remain requesting
4. On accept, the retiring pin drops out (latch cleared or Remote IRR set) and the next lowest loads in the same cycle
5. Level pins in service are skipped; their EOIs arrive whenever the ISRs finish and do not gate anyone else
6. Process repeats until nothing is eligible

**Example Timeline:**
```
Cycle 0:   IRQ3 (level), IRQ5 (edge), IRQ7 (level) all become eligible
Cycle 1:   Stage loads IRQ3
Cycle 2:   CPU accepts IRQ3 -> Remote IRR[3] set; stage loads IRQ5 the same cycle
Cycle 3:   CPU accepts IRQ5 -> pending[5] cleared; stage loads IRQ7
Cycle 4:   CPU accepts IRQ7 -> Remote IRR[7] set; stage empty
...
Cycle N:   EOI(vector of IRQ7) -> Remote IRR[7] clears; IRQ3 still in service, unaffected
Cycle N+1: IRQ7 re-requests if its level is still asserted
```

**Fairness:** Lower numbered IRQs starve higher ones if they keep requesting, and a low-numbered level pin that is EOI'd promptly can hold the stage indefinitely. Static priority is the design choice; round-robin is tracked as RLB-008 in `vault/Tasks/RLB/open.md`, not as a defect.

## Navigation

**See Also:**
- [ioapic_core Block](01_ioapic_core.md) - Detailed delivery-stage implementation
- [Programming: Level Interrupts](../ch04_programming/04_level_triggered_irq.md) - The stage from the software perspective

**Back to:** [Index](../ioapic_index.md) | [Block Overview](00_overview.md)
