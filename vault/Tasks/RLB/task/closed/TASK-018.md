# TASK-018: per-IR-line PIC assertions, and overlap beyond two coincident sources

**Priority:** P2
**Status:** CLOSED 2026-09-28 -- all four criteria met with logged evidence;
see the Outcome, including what is deliberately NOT claimed.
**Owner:** done
**Filed:** 2026-09-28, from RLB TASK-017's "Deliberately not claimed, worth a
follow-up" section. Quoted there verbatim, so the scope is what that task
declined to claim -- not a re-derivation of it.

## What TASK-017 did NOT claim

1. **The PIC half is proven at the AGGREGATE, not per IR line.** Each of the six
   blocks is checked with `pic_int_out` plus the BFM's `expect_only()` on SOURCE
   names. That proves "this block fired and the PIC's INT rose and no other
   source moved" -- it does NOT prove the interrupt arrived on the block's own
   IR input. GPIO is the exception: its separate slave-vector test reads back the
   acknowledged vector. A per-IR-line assertion for PIT, UART, RTC, PM/ACPI and
   SMBus is the gap.
2. **Overlap is exercised with TWO coincident sources**, both slave-side (GPIO
   IRQ11 + PM/ACPI IRQ9, the only two driven by pure DUT inputs). Three or more,
   and master-side plus slave-side simultaneously, are not covered.

## Why per-IR-line is provable without new RTL

`pic_irq_in` is held at 0 for the whole of every fabric test -- that is already
asserted first in `_routing_verdict`. So:

- `w_fabric_irq[irq]` IS the per-line claim. It is a named module-scope
  `logic [15:0]` (rlb_top.sv:638).
- The SLAVE's `irq_in` is the inline expression `pic_irq_in[15:8] |
  w_fabric_irq[15:8]` -- not a named signal, so there is nothing else to probe.
  With `pic_irq_in` at 0 the slave's IR line IS `w_fabric_irq[irq]`.
- For IRQ 0-7 the master's input is the named `w_master_pic_irq`, so
  `w_master_pic_irq[irq]` is directly assertable. Mind the `& 8'hFB`: bit 2 is
  masked off every source and forced from the cascade, but no block maps to
  IRQ2, so no fabric line is affected.

IRQ map (rlb_top.sv:631-635, 93-94): PIT 0, UART 4, RTC 8, ACPI 9, SMBUS 10 and
GPIO 11 -- the last two are MODULE PARAMETERS, not localparams, so read them
from the parameters rather than hardcoding if they are ever overridden.

## Design notes

- **Use the existing BFM, per-bit.** `IRQMonitor.is_asserted(index)` and
  `events()` take a bit index, so registering `w_fabric_irq` as a 16-bit vector
  in the existing `IRQMonitorGroup` gives timestamped per-bit events. Prefer
  that over sampling the signal live at verdict time: a source whose pulse ends
  before the verdict runs would read as a routing failure.
- **`IRQMonitorGroup` SKIPS a signal the DUT does not expose**, with only a
  `log.warning`. Anything added to the group must ALSO be asserted present at
  setup, or a missing signal silently disables the check that was the point.
- `_routing_verdict` already receives `ioapic_irq=<irq number>` from all six
  tests, so the per-line check lands there with no signature change, and covers
  GPIO for free.

## Overlap: one test can close both halves

UART (IRQ4) asserts almost immediately from register writes and STAYS asserted
(TX-holding-empty); GPIO (IRQ11) and PM/ACPI (IRQ9) are pure DUT inputs. Three
coincident sources with UART on the MASTER side and the other two on the SLAVE
side exercises master IR4 and the cascade into IR2 at the same time. SMBus
(IRQ10, ~1500 pclk) and PIT (IRQ0, ~400 pclk) can extend it further, but their
latency makes precise coincidence harder -- prove three first.

## Done when

- [x] each of the six fabric tests asserts its own IR line, not just aggregate
      `pic_int_out`: `w_fabric_irq[irq]` set, every other `w_fabric_irq` bit
      clear, and `w_master_pic_irq[irq]` set for IRQ 0-7
- [x] a missing probe signal FAILS the test rather than warning and skipping
- [x] at least three sources are coincident in one test, spanning master and
      slave sides, with the cascade invariant still holding
- [x] rlb_top suite green at the full tier from `make clean-all`, and the area
      unaffected at the sign-off tier

## Outcome (2026-09-28)

**Per-IR-line, all six blocks plus the three-source case.** `_ir_lines_ok()`
reads the BFM's per-bit EVENTS, so a source whose pulse ends before the verdict
runs is still counted -- PIT and RTC are exactly that shape. Seven logged lines,
and they carry five DISTINCT shapes, which is what shows the check is not
trivially satisfied:

| Block | IRQ | fabric bits | master bits |
|---|---|---|---|
| GPIO | 11 | `[11]` | `[2]` |
| PM/ACPI | 9 | `[9]` | `[2]` |
| UART | 4 | `[4]` | `[4]` |
| PIT | 0 | `[0]` | `[0]` |
| RTC | 8 | `[8]` | `[2]` |
| SMBus | 10 | `[10]` | `[2]` |
| three coincident | 4+9+11 | `[4, 9, 11]` | `[2, 4]` |

Master-side blocks show their OWN bit and NOT bit 2; slave-side blocks show ONLY
bit 2. The master expectation is an EXACT set including bit 2 whenever a
slave-side IRQ is expected, so it proves both that the cascade appeared and that
nothing else moved on the master.

**A SECOND monitor group, deliberately.** The probes are NOT in `self.irqs`:
that group's value is its negative assertion and all seven fabric tests pass
SOURCE names to `expect_only()`. Folding `w_fabric_irq` in would have made it
`unexpected` in every one of them and failed the lot. `self.pic_lines` is
separate, cleared alongside `irqs` in `_fabric_preamble`, and referenced in
exactly three places.

**The slave PIC has no probeable input.** `u_pic_slave.irq_in` is the inline
expression `pic_irq_in[15:8] | w_fabric_irq[15:8]`, not a named signal. With
`pic_irq_in` held at 0 -- already asserted first in `_routing_verdict` -- the
slave's IR line IS `w_fabric_irq[irq]`, which is what makes this provable with
no RTL change.

**Three coincident sources, spanning both PICs.** UART (IRQ4, master) is
programmed first and holds; GPIO (IRQ11) and PM/ACPI (IRQ9) are pure DUT inputs
arriving at random offsets INSIDE it. The test asserts all three are
simultaneously high BEFORE waiting further, and fails rather than degrading into
a repeat of TASK-017's two-source case if UART is not already asserted.
Observed: master IR4 and the cascade IR2 together, IOAPIC delivering 0x44, 0x49
and 0x4B.

**The guard is load-bearing and proven, simulator-free.** `IRQMonitorGroup`
WARNS AND SKIPS a signal the DUT does not expose, so a missing probe would have
left the check inspecting a monitor that is not there -- passing while proving
nothing. Confirmed by construction against a stub DUT: the missing signal is
skipped and nothing is raised. `setup_components` now fails hard instead.
`_ir_lines_ok` was then positive-controlled 8/8 with the real `IRQMonitor` and
`IRQPacket`: absent monitors fail closed, and an extra fabric bit, a missing
cascade bit and a stray master bit are each rejected. A check that cannot fail
proves nothing, so the negative cases are the point.

**Evidence.** 15/15 at the full tier from `clean-all`; 81/81 across the area at
the sign-off tier (`run-all-full-parallel`, 6m55s, 15 test roots, REG_LEVEL=FULL)
with rlb_top's three cells passing inside that run and the seven per-IR-line
lines still present. `w_fabric_irq` IS reachable -- "12 source lines and 2
IR-line probes" in all three cells, so the guard never fired.

**Two measurement errors made while verifying this, recorded so they are not
repeated:**

- Greps for the evidence were run against MAKE'S STDOUT, which carries only
  pytest's xdist summary. The cocotb INFO stream goes to `LOG_PATH`
  (`dv/tests/logs/test_rlb_top_<level>.log`). The evidence sections came back
  empty while the run was green.
- From that emptiness plus "gate 181s vs full 177s" it was concluded the full
  method list had not run. That inference was WRONG: the three cells run
  CONCURRENTLY under xdist, so wall time is the slowest cell, not the sum. An
  earlier 563s figure was a differently-shaped run, not a contradiction.

**Deliberately not claimed, worth a follow-up:**

- `_ir_lines_ok` has NO permanent test. The 8/8 control above was an ad-hoc
  script and is gone; a future edit could silently lose the fail-closed
  behaviour. `bin/TBClasses/irq/tests/` is the precedent for where one would go.
- The per-IR-line check runs at the FULL tier only, because the fabric tests are
  in `full_methods`. gate and func log zero such lines by construction.
- `w_fabric_irq[IRQ_TIMER]` is `pit_timer_irq[0] | hpet_legacy_irq0` and
  `[IRQ_RTC]` is `rtc_alarm_irq | rtc_second_irq | hpet_legacy_irq8`, so a set
  bit proves the LINE, not which sub-source drove it. The BFM's source-name
  `expect_only()` covers that separately; nothing checks the two together.
- FOUR or more coincident sources are still not covered, and neither SMBus
  (~1500 pclk) nor PIT (~400 pclk) has been placed in a coincident set -- their
  latency makes precise overlap harder, which is why three came first.

## Dependencies

RLB TASK-017 (the BFM and the six routing tests) -- CLOSED 2026-09-28.
