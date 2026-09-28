# TASK-015: rlb_top interrupt fabric -- route block IRQs to the PIC/IOAPIC

**Priority:** P2
**Status:** CLOSED 2026-09-28 -- fabric built and verified; two criteria met
with stated limits, see the Outcome.
**Owner:** done

Filed 2026-09-28. The owner chose this explicitly ("Also build the mux in
rlb_top") and sequenced it behind RLB/pic_8259 TASK-001. Both prerequisites now
exist, which is what unblocks it.

**The gap, measured not assumed (2026-09-28):** every block's interrupt LEAVES
`rlb_top` on its own port -- `hpet_timer_irq`, `hpet_legacy_irq0/8`,
`pic_int_out`, `pit_timer_irq`, `rtc_alarm_irq`, `rtc_second_irq`,
`smb_interrupt`, `pm_interrupt`, `gpio_irq`, `uart_irq` -- while `pic_irq_in`
and `ioapic_irq_in` arrive from OUTSIDE. **Nothing inside rlb_top connects a
block's interrupt to either controller.** A board must currently wire all ten
back in externally, which is precisely the integration the subsystem exists to
absorb.

`PRD.md:515` states the requirement under the rlb_top Interface heading:
"**Aggregated interrupt output** combining all block IRQs".

**Two separable deliverables.** They are often conflated; they are not the same
thing:
1. **The mux (internal routing).** Block IRQs reach the PIC and the IOAPIC on
   their conventional legacy lines, so software programming the 8259 or the
   IOAPIC sees the peripherals without board-level wiring.
2. **The aggregated output.** One OR of every block IRQ as a single pin, which
   is what PRD.md:515 literally asks for -- useful to a SoC that wants one
   line into its own controller.

**Design already settled by what is in the tree:**
- **OR into the EXISTING inputs, do not replace them.** `w_boot_intx_pic_irq`
  already ORs into the master PIC's `irq_in`, so there is a precedent in this
  very file. Keeping `pic_irq_in`/`ioapic_irq_in` as inputs that the internal
  sources OR into means every existing test keeps its direct drive and no
  integrator loses the external path. Replacing them would be a silent
  port-contract change.
- **Blocks reset quiescent**, so the OR should be safe with no enable bit. That
  is a claim to VERIFY by running the suite, not to assert -- an always-on OR
  that raises the PIC where it previously stayed low would break the rlb_top
  smoke tests.
- **IRQ2 MUST STAY UNDRIVEN.** It is the 8259 cascade input, and RLB/pic_8259
  TASK-001 already masks it off the master's external inputs and drives it from
  the slave PIC's INT. Anything routed there reaches nothing. This is the trap
  that QEMU shipped.

**The assignment, and which parts are convention vs choice.** The authoritative
table is `docs/ioapic_mas/ch05_registers/01_register_map.md` ("Typical IRQ
Assignments"). From it, unambiguously:
  IRQ0 System Timer, IRQ2 Cascade, IRQ4 COM1, IRQ8 RTC Alarm, IRQ9 ACPI.
So PIT counter 0 -> IRQ0, UART -> IRQ4, RTC -> IRQ8, PM/ACPI -> IRQ9, and
HPET's `legacy_irq0`/`legacy_irq8` -> IRQ0/IRQ8 (they exist to REPLACE the PIT
tick and the RTC).

SMBus and GPIO have no traditional legacy line; the table only offers IRQ10/11
as "Available". **Those two are a CHOICE, not a convention**, so the mapping
belongs in a documented parameter an integrator can override rather than being
hardcoded as though the table dictated it.

**Scope:**
1. `rlb_top`: an internal IRQ vector assembled from the block outputs, OR-ed
   into `pic_irq_in` and `ioapic_irq_in`, with the map as a parameter.
2. `rlb_top`: the single aggregated output pin (PRD.md:515).
3. DV: the rlb_top suite gains coverage that each block's IRQ reaches the PIC
   and the IOAPIC, and that IRQ2 is NOT driven by the fabric.
4. Docs: the address/interrupt map in `rlb_top.sv`, `rlb_top.f`, and the
   component README.

**Completion Criteria:**
- [~] Each block IRQ reaches its assigned PIC input and IOAPIC pin -- **GPIO is
      proven end to end** (`gpio_irq` -> IRQ11 -> slave IR3 -> slave INT ->
      master IR2 -> `pic_int_out`, with `pic_irq_in` held at 0 throughout, and
      acknowledged as the SLAVE vector 0x2B rather than the master's 0x22).
      The other five ride structurally identical wiring but are **NOT tested**.
      Marked as a limit rather than ticked: one proven path is evidence the
      mechanism works, not that every assignment is right.
- [~] The fabric drives nothing onto IRQ2 -- proven STRUCTURALLY (the assigned
      bits are exactly TIMER/UART/RTC/ACPI/SMBUS/GPIO; IRQ2 is never written),
      **not in simulation**. It is not directly observable: GPIO arrives on a
      slave line and the slave's INT legitimately raises master IR2, so an
      "IR2 stays low" test would assert the wrong thing.
- [x] External `pic_irq_in`/`ioapic_irq_in` still work -- they remain inputs the
      fabric ORs into, so every existing test kept its direct drive and none
      were changed
- [x] A single aggregated interrupt output exists (PRD.md:515) -- `rlb_irq_out`,
      low at rest and high with `pic_int_out`
- [x] rlb_top suite green (8/8, 5/5, 1/1 by METHOD), and the per-block suites
      are unaffected BY CONSTRUCTION: the fabric touches only `rlb_top.sv`, and
      each block suite drives its own `apb4_*` DUT, not rlb_top
- [x] The map is a parameter, with the convention-vs-choice split documented

**Dependencies:** RLB/hpet TASK-003 (legacy_irq0/8) and RLB/pic_8259 TASK-001
(IRQ8-15 exist) -- both CLOSED 2026-09-28.

**Note:** `PRD.md:514` says the subsystem sits at `0x4000_0000`; the RTL's
`BASE_ADDR` is `32'hFEC00000` and every test uses that. The PRD line is stale
and should be corrected while this task is in the file.

---

## Outcome (2026-09-28)

**Built.** Block interrupts reach both 8259s and the IOAPIC internally on the
lines from the "Typical IRQ Assignments" table: IRQ0 PIT ch0 + HPET legacy timer
0, IRQ4 UART, IRQ8 RTC + HPET legacy timer 1, IRQ9 PM/ACPI, IRQ10 SMBus, IRQ11
GPIO -- plus `rlb_irq_out`, the aggregated pin PRD.md:515 asks for.

**OR-ed into the external inputs rather than replacing them**, following the
`w_boot_intx_pic_irq` precedent already in the file. `pic_irq_in` and
`ioapic_irq_in` stay inputs, so integrators keep the external path and every
existing test kept its direct drive -- no test changed to accommodate this.

**No enable bit, and that is verified rather than assumed.** An always-on OR is
safe only if blocks reset quiescent; this task recorded that as a claim to TEST,
and the rlb_top suite passing unchanged is the evidence.

**IRQ2 is never driven** -- it carries the slave 8259's INT (RLB/pic_8259
TASK-001). `pic_int_out` is likewise excluded from the fabric sources: feeding
the PIC's own output back into its inputs is a combinational loop. It appears
only in the aggregate, which drives no logic.

**A choice is overridable; a convention is not.** `IRQ_SMBUS` and `IRQ_GPIO` are
MODULE PARAMETERS -- the table offers only "Available" for those two. IRQ0/4/8/9
stay localparams, because letting an integrator move them invites silently
diverging from what every driver assumes. The first implementation used
localparams throughout, which does NOT satisfy this task's own criterion of "a
parameter an integrator can override"; re-reading that criterion caught it.

**Consequence recorded, not left to be found:** `BOOT_INTX_PIC_MAP` still names
legacy input 2, but master IR2 is masked off the external inputs, so a
boot-interrupt reroute onto IOAPIC pin 2 now reaches nothing. The comment there
says so. The existing boot-intx test passes only because it uses IRQ3 -- checked,
not assumed.

**A pre-flight gate paid for itself.** Before spending a 3-minute run, it caught
a missing `PIC8259RegisterMap` import that would have raised NameError. Its
first version PRINTED without asserting -- a check that cannot fail -- and was
tightened so all four assertions can genuinely fail.

**Not done, worth a follow-up:** only GPIO is proven end to end. A test per block
needs each programmed through its own window -- a larger piece of work than the
fabric itself.
