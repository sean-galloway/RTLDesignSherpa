# TASK-017: an interrupt-line BFM, and per-block routing coverage for the rlb_top fabric

**Priority:** P2
**Status:** open (filed mid-flight -- the BFM half is already written, see Progress)
**Owner:** in progress

Filed 2026-09-28 at the owner's direction: "proceed with all of the most robust
testing you can manage. Do not hand roll any BFMs. If it seems like something
like an interrupt signal could use a bfm, create one."

**Why.** RLB TASK-015 built the rlb_top interrupt fabric but closed with its
first completion criterion only PARTLY met: GPIO was proven end to end and the
other five blocks ride structurally identical wiring that nothing exercises.
Closing that gap needs per-block stimulus -- and doing it with the polling the
tests used until now would multiply the problem rather than fix it.

**The observation problem, measured.** Interrupt lines were read by hand as
`int(dut.<sig>.value)` in TWELVE places across the RLB testbenches, each with
its own wait length and its own idea of what counts as an event. That kind of
poll misses a narrow pulse between samples, cannot say WHEN a line moved, and
gives no two call sites the same semantics.

**Scope:**
1. `TBClasses.irq` -- a BFM for plain interrupt lines: level or pulse, scalar
   or vector, one event per CHANGED BIT with a timestamp. `IRQMonitorGroup`
   watches many lines and answers the question a routing test actually asks:
   "exactly these lines moved and no others".
2. Wire it into `rlb_top_tb` and convert the existing fabric tests off polling.
3. Per-block routing coverage: PIT, RTC, SMBus, PM/ACPI and UART each driven to
   assert through the rlb_top window, each checked to reach its assigned PIC
   input and the IOAPIC.
4. Randomised inter-assert timing, since a level-sensitive OR fabric is exactly
   where coincident and overlapping asserts bite.

**Placement decision (owner, 2026-09-28):** the BFM lives in `bin/TBClasses/irq/`
rather than RDS-DV, deliberately, so it can be iterated without a package
reinstall -- the handbook's "missing BFM = add it to RDS-DV" is overridden here
with that reason. The package layout mirrors an RDS-DV component family
(`__init__` / `_packet` / `_components`) so promoting it later is a directory
move. Do not "correct" it into RDS-DV without that conversation.

**TRAPS FOUND WHILE READING THE BLOCKS' OWN TBs -- do not re-derive these:**
- **UART needs `MCR_OUT2` (1<<3) as well as `IER`.** OUT2 gates the IRQ pin. A
  UART configured with IER alone is fully set up and still never asserts, which
  looks exactly like a broken fabric.
- **PIT uses bit POSITIONS, everyone else uses pre-shifted MASKS.**
  `CONFIG_PIT_ENABLE = 0` means bit 0, so PIT needs `1 << CONFIG_PIT_ENABLE`
  while RTC/SMBus/PM/UART constants (`(1<<0)` etc.) are used bare. Mixing the
  conventions is a silent off-by-shift.
- **GPIO's `gpio_enable` resets to 1 and `int_enable` to 0** -- only the global
  interrupt enable needs setting.
- **`ioapic_irq_out_*` is NOT this BFM's job.** It has valid/ready/retry, so it
  is a handshake and belongs to GAXI per [[bfm-usage]].

**Progress (2026-09-28):**
- BFM written: `bin/TBClasses/irq/{__init__,irq_packet,irq_components}.py`.
- The decomposition is a PURE function (`diff_to_packets`) extracted from the
  sampling coroutine specifically so it is testable without a simulator.
- 16 unit tests pass in `bin/TBClasses/irq/tests/` (pytest collects package-local
  tests -- confirmed, 55 collected from the monbus precedent). They cover the
  coincident case `0b01 -> 0b10` in ONE transition, and pin the falsy-monitor
  trap shut as a regression: cocotb's `Monitor.__len__` makes an idle monitor
  FALSY, and an idle interrupt line is the normal case here, so this class
  deliberately does not define `__len__`.
- Wired into `rlb_top_tb.setup_components`, watching 12 of 12 interrupt outputs.

**Completion Criteria:**
- [ ] Each of the six blocks asserts through the rlb_top window and is observed
      arriving at its assigned PIC input and IOAPIC pin
- [ ] Each test also asserts the NEGATIVE: no other line moved, IRQ2 included
- [ ] The existing fabric tests use the BFM rather than polling
- [ ] Inter-assert timing is varied, not one clean edge per test
- [ ] rlb_top suite green, per-block suites unaffected
- [ ] BFM unit tests pass and run in CI's collection

**Dependencies:** RLB TASK-015 (the fabric) -- CLOSED 2026-09-28.

---
