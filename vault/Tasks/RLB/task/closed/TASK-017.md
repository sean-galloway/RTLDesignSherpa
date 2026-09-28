# TASK-017: an interrupt-line BFM, and per-block routing coverage for the rlb_top fabric

**Priority:** P2
**Status:** CLOSED 2026-09-28 -- all six criteria met with logged evidence;
see the Outcome, including what was deliberately NOT claimed.
**Owner:** done

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
- [x] Each of the six blocks asserts through the rlb_top window and is observed
      arriving at its assigned PIC input and IOAPIC pin
- [x] Each test also asserts the NEGATIVE: no other line moved, IRQ2 included
- [x] The existing fabric tests use the BFM rather than polling
- [x] Inter-assert timing is varied, not one clean edge per test
- [x] rlb_top suite green, per-block suites unaffected
- [x] BFM unit tests pass and run in CI's collection

**Outcome (2026-09-28):**

Six blocks, six vectors, observed rather than inferred. Each block is programmed
through its own rlb_top window, its IOAPIC redirection entry is unmasked FIRST
(an RTE resets MASKED and swallows the interrupt silently, which reads exactly
like a dead route), and the test asserts the vector the IOAPIC actually
delivered: 0x40 PIT, 0x44 UART, 0x48 RTC, 0x49 PM/ACPI, 0x4A SMBus, 0x4B GPIO --
`arm_ioapic_pin` programs 0x40+irq. The vector is LOGGED on success, so a run
carries positive evidence instead of the absence of a failure message.

Delivery is a valid/ready handshake with a multi-field payload, so it went to
GAXI and not the interrupt BFM, as this task's own trap list required. No
`signal_map` was needed: `field_base` is
`{prefix}{bus_name}{pkt_prefix}{field_name}`, so `prefix='ioapic_irq_out_'`
auto-discovers every pin. `ioapic_deliveries()` reads through
`get_observed_packets()` and NEVER truthiness -- `GAXIMonitor` defines
`__len__`, so an idle monitor is FALSY and `if monitor:` would skip the check
exactly when it matters. That is the same trap [[TBClasses.irq]]'s own unit
tests pin shut.

IRQ2 is checked as an INVARIANT, not as "never moves". rlb_top masks bit 2 off
every other source (`& 8'hFB`) and forces it from the slave's INT, so the claim
is `w_master_pic_irq[2] == w_spic_int`, checked on every block. "IR2 never
moves" would have been WRONG for four of the six -- for the IRQ8-15 blocks it
SHOULD rise, and that is the cascade working.

GPIO and PM/ACPI hand-rolled their own reset/cascade preamble and verdict, so
they would have silently missed all three new checks. Both are refactored onto
`_fabric_preamble`/`_routing_verdict`; `init_pic_cascade` call sites 3 -> 1.
GPIO also never called `irqs.clear()` and passed only because it ran first.

Criterion 4 was NOT claimed on jitter alone. Varying when a single edge lands
still leaves "one clean edge per test", which the criterion explicitly rules
out, and the scope line gives the reason: a level-sensitive OR fabric is where
COINCIDENT asserts bite. So a seventh test drives GPIO and PM/ACPI overlapping
-- both are DUT inputs, so the overlap is controlled exactly -- with the second
source arriving a random 1-20 pclk INSIDE the first's assertion. Both land on
the slave 8259, so one cascade INT must represent both while IR2 still equals
`w_spic_int`. Observed: gap 11 pclk, both 0x4B and 0x49 delivered coincident.

**Two assessments made in this lane were WRONG and are corrected here:**

- *"SMBus is blocked by a known RTL defect"* -- it is not. That came from the
  GH#58 defect map atop `smbus_tests_medium.py`, whose own header states it was
  written FIRST against the UNFIXED RTL. #58 closed 2026-09-10 and all six
  findings were fixed by 91c49a094; the `r_timeout_en` it describes exists
  nowhere in `rtl/smbus`. SMBus needed no bus model at all: `_idle_inputs`
  holds `smb_sda_i` high, nothing pulls the ACK slot low, `smbus_core` reads
  that as a NAK (`r_nak_received`, a `w_error_next` term), and with
  INT_ERROR_EN armed that raises `smb_interrupt`. The absent slave IS the
  stimulus. See [[feedback_refute_the_original_not_the_paraphrase]].
- *"RTC needs a simulated second"* -- `clock_select=1` drops the divider target
  to `DIV_TARGET_SYS=99`, and a whitebox poke of `r_clk_div_counter` rolls the
  tick in a few cycles. The RTC block's own periodic-tick test waits 500 cycles
  then passes whether or not the flag set, so it cannot fail; it was
  deliberately NOT used as a model.

**Evidence.** 14/14 at the full tier (`run-rlb_top-full`), six vectors logged,
both overlap vectors logged, no IRQ2 violation. 81/81 across the area at the
sign-off tier after `clean-all` (`run-all-full-parallel`, 9m14s, 15 test roots)
so no per-block suite moved -- that sweep measured the tree at ef58497fb, and
the overlap test added afterwards lives INSIDE the three existing rlb_top
cells, so the area cell count is unchanged and only rlb_top's cells moved.
CI green on 69d6be8e9 and ef58497fb, the latter with STEP-LEVEL confirmation
that "Interrupt BFM decomposition logic (simulator-free)" and its cocotb
install pass on a real runner. cocotb is needed as an IMPORT only:
`irq_components` imports it at module level for its triggers, so collection
fails without it even though the logic under test needs no simulator.

**Deliberately not claimed, worth a follow-up:**

- The IOAPIC half of criterion 1 is proven PER INDEX, because the delivered
  vector is 0x40+irq and the RTE is per-pin. The PIC half is proven at the
  AGGREGATE (`pic_int_out` plus the BFM's `expect_only`), not per IR line --
  except GPIO, where the separate slave-vector test reads back the acknowledged
  vector. A per-IR-line assertion for the other five is a follow-up.
- Overlap is exercised with TWO coincident sources. Three or more, and
  master-side plus slave-side simultaneously, are not covered.

**Dependencies:** RLB TASK-015 (the fabric) -- CLOSED 2026-09-28.

---
