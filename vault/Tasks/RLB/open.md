# RLB — Open (accepted, not started)

---

### RLB-006: scrub the tests for completeness (retro legacy blocks)

**Priority:** P2. Blocks the coverage/formal push, not day-to-day work.
**Status:** open 2026-09-04. Raised by Sean: test scrubbing was meant to be
part of the kimi review packets and got dropped along the way. Applies to the
components suites as well as rtl/.

**Sequencing.** A FOCUSED pass, run after qc/humanize is finished everywhere
and BEFORE coverage and formal are driven clean. Doing it after coverage would
mean chasing numbers produced by tests nobody has audited.

**Scope:** `projects/components/retro_legacy_blocks/dv/tests/` -- 9 test files covering the 8259/8254/16550/SMBus/PM-ACPI/RTC cores.

**The capability already exists and was simply never run here.**
`bin/review/run_batch.py` has a `testqc` mode alongside `qc` and `humanize`,
with `bin/review/TEST_REVIEWER_BRIEF.md` as its brief and
`bin/review/build_test_review_bundle.py` to build the units. The brief audits
test collateral against the project's test contract and treats the
CocoTBFramework as reviewed ground truth rather than an audit target. Start
there rather than inventing a method.

**Why this is not busywork.** A test that passes because the RTL is broken is
worse than no test, and the repo has already produced them. The template is
apb5 (2026-09-04): nothing drove `rsp_ready`, so the response skid filled and
never drained, and the TB's completion check returned True on exactly the
state the defect produced. The suite was green BECAUSE the RTL was broken. The
witness added with the fix counted 59 protocol violations across 70 bus
completions on the unfixed design that no prior test had noticed.
**Area-specific:** several cores here have not been touched since 2025-11 and
their `_core` modules are undocumented, so the tests are currently the only
statement of intended behaviour. That makes an unaudited test in this area
more load-bearing than elsewhere, not less.

**What "complete" has to mean, at minimum:**

- Every `test_*.py` actually exercises the DUT it names.
- No test asserts a condition the bug itself satisfies.
- Inputs the DUT needs are actually driven.
- gate/func/full levels mean something distinct, not three names for one run.
- No `run()` call pins `testcase=` to a single cocotb test. A pinned
  `testcase=` silently hides every OTHER `@cocotb.test` in that module, so a
  test can sit in the file for months and never execute. `test_apb5_master.py`
  did exactly this (2026-09-04) -- a witness added beside the basic test ran
  zero times until the pin was widened. A comma-separated list is the fix when
  a pin is genuinely wanted.
- A fix landed with a test has a mutation check recorded: the test was seen
  RED against the unfixed RTL. Without that the test is decoration.

**Related:** [[TASK-078]], [[COMMON-025]], [[MATH-010]], [[CDC-001]] are the
same task in the rtl/ areas.

### RLB-007: all RDL lives in an rdl area, as it does elsewhere

**Priority:** P3. Hygiene, and cheaper here than anywhere else in the repo.
**Status:** open 2026-09-04. Raised by Sean, for consistency with
[[MISC-001]]: all RDL belongs in an `rdl` area rather than scattered under
`rtl/`.

**Current layout.** Nine `.rdl` sources, each alone in its own
`rtl/<block>/peakrdl/` directory, and no `rdl/` directory exists in the area
at all:

| Block | Source |
|---|---|
| gpio | `rtl/gpio/peakrdl/gpio_regs.rdl` |
| hpet | `rtl/hpet/peakrdl/hpet_regs.rdl` |
| ioapic | `rtl/ioapic/peakrdl/ioapic_regs.rdl` |
| pic_8259 | `rtl/pic_8259/peakrdl/pic_8259_regs.rdl` |
| pit_8254 | `rtl/pit_8254/peakrdl/pit_regs.rdl` |
| pm_acpi | `rtl/pm_acpi/peakrdl/pm_acpi_regs.rdl` |
| rtc | `rtl/rtc/peakrdl/rtc_regs.rdl` |
| smbus | `rtl/smbus/peakrdl/smbus_regs.rdl` |
| uart_16550 | `rtl/uart_16550/peakrdl/uart_16550_regs.rdl` |

**This one is genuinely cheap, unlike MISC-001.** Only seven references exist
across the whole repo, and five are each block's own `*_regmap.py`:

- `rtc_regs.rdl` — `rtl/rtc/rtc_regmap.py`
- `hpet_regs.rdl` — `rtl/hpet/hpet_regmap.py`
- `pic_8259_regs.rdl` — `rtl/pic_8259/pic_8259_regmap.py`
- `pit_regs.rdl` — `rtl/pit_8254/pit_regmap.py`
- `gpio_regs.rdl`, `ioapic_regs.rdl`, `pm_acpi_regs.rdl`, `smbus_regs.rdl`,
  `uart_16550_regs.rdl` — **no references at all**

The remaining two hits are in `bin/peakrdl_to_regmap.py` and
`bin/peakrdl_generate.py`, and both are USAGE EXAMPLES in help text
(`%(prog)s hpet_regs.rdl -o hpet_regmap.py`), not path dependencies. They do
not need to change, though they are worth a glance for whether the example
should name the new location.

**Layout: PER BLOCK.** Decided by Sean 2026-09-04 -- `rdl/<block>/<name>.rdl`,
not a flat directory:

    rdl/gpio/gpio_regs.rdl
    rdl/hpet/hpet_regs.rdl
    rdl/ioapic/ioapic_regs.rdl
    rdl/pic_8259/pic_8259_regs.rdl
    rdl/pit_8254/pit_regs.rdl
    rdl/pm_acpi/pm_acpi_regs.rdl
    rdl/rtc/rtc_regs.rdl
    rdl/smbus/smbus_regs.rdl
    rdl/uart_16550/uart_16550_regs.rdl

Apply it uniformly. Half-application is exactly the state MISC-001 exists to
fix.

**Also worth deciding while in there:** three of the `peakrdl/` directories
carry a `README.md` (hpet, rtc, smbus). Per the handbook, methodology does not
live next to the code -- a README beside a tool restating how to use it is the
copy nobody edits. Fold anything real into the handbook or the block's MAS
rather than moving these along with the sources.

**Method.** Move, update the four `*_regmap.py` references, then REGENERATE
through `bin/peakrdl_generate.py` rather than hand-editing any generated
output -- it emits RTL, docs and regmap in lockstep, and a raw `peakrdl
regblock` desyncs the regmap. Run the RLB tests afterwards.

### RLB-008: IOAPIC features deferred past the #48 fix

**Priority:** P3. The block is functionally complete for its MVP scope and
36/36 green in all six configurations; nothing here is a defect.
**Status:** open 2026-09-09. Raised while closing issue #48. These items were
the surviving content of `rtl/ioapic/TODO.md`, which was deleted with that fix
along with `INTERRUPT_DELIVERY_DEBUG.md` -- both described the delivery FSM
that the #48 fix removed, so keeping them in sync would have meant rewriting
two stale trackers next to the code instead of recording the open work here.

**Deferred by design (82093AA features the MVP does not implement):**

- Logical destination mode. `dest_mode` is stored in the RTE and forwarded to
  the core, which ignores it -- `cfg_dest_mode` is deliberately unused and
  shows as UNUSEDSIGNAL in lint. Physical delivery only.
- LowestPriority delivery mode: needs CPU priority tracking the block has no
  interface for. The mode bits are carried on `irq_out_deliv_mode` unmodified,
  so SMI/NMI/INIT/ExtINT are already "supported" in the sense the DV suite
  tests -- the IOAPIC forwards them, it does not act on them.
- Dynamic priority rotation. Arbitration is static, lowest IRQ number wins,
  and a continuously asserted high-priority level pin can starve the rest
  whenever software EOIs it promptly. Round-robin would fix it; that is a
  behaviour change, not a bug fix, so it is not being smuggled into #48.
- Multi-IOAPIC routing, boot-interrupt (INIT-SIPI-SIPI) delivery, MSI/MSI-X.

**Worth doing sooner than the rest:** the starvation note above deserves a
directed test before anyone relies on the priority scheme, and
`ioapic_regs.rdl` fixes the table at 24 entries while `ioapic_core` scales
with NUM_IRQS -- the mismatch is caught today only by a simulation-time
`$error` in `ioapic_config_regs`. Making the RDL entry count generated from
the same parameter would remove the guard's reason to exist.

### RLB-009: PM_ACPI features deferred past the #54 fix

**Priority:** P3. The block is functionally complete for its MVP scope and
6/6 configurations green at FULL (basic 8/8, medium 10/10, full 12/12, GH#54
17/17); nothing here is a defect.
**Status:** open 2026-09-09. Raised while closing issue #54. These items were
the surviving content of `rtl/pm_acpi/TODO.md`, which was deleted with that
fix: most of it described work already done (the DV suite, the helper-script
plan) or behaviour the fix changed (the "W1C edge detection / auto-clear
fields" architecture note, the "reset tracking simplified" limitation), so
keeping it would have meant maintaining a stale tracker next to the code.
Same disposition as [[RLB-008]] for ioapic.

**Deferred by design (MVP scope, stated in `rtl/pm_acpi/README.md`):**

- Clock-gate and power-domain transitions are INSTANT. No ramp, no sequencing
  delay, no per-domain ordering. Real silicon wants a sequencer with
  programmable inter-domain delays and an acknowledge per rail.
- No S5 (soft off). The FSM is S0/S1/S3 plus a transition state.
- GPE is rising-edge only and one bank of 32. No level mode, no per-event
  edge/level choice, no GPE1, no run-vs-wake split.
- PM timer is 32-bit with a single divider. No 64-bit mode, no prescaler
  options, no comparators.
- Buttons get a 3-flop synchronizer, not a debouncer: no configurable
  threshold and no long-press (the ACPI 4-second power-button override) --
  which is why `PM1_CONTROL.pwrbtn_ovr` is documented storage-only rather
  than wired to an invented meaning.
- `RESET_STATUS.wdt_reset` / `.ext_reset` always read 0. Making them real
  needs new device pins on `apb4_pm_acpi` (a watchdog-expired input and an
  external-reset input); the fields are documented as unobservable instead.
- Legacy replacement routing (IRQ0 timer, IRQ8 RTC) and processor C/P-state
  hints are out of scope.

**Worth doing sooner than the rest:** the power-domain sequencer. Instant
`power_domain_en` transitions are the one MVP simplification that a real
integration cannot paper over, because rail ordering is a board-level
correctness property, not a performance one. It is a behaviour change with new
register state, so it was deliberately not smuggled into #54.
