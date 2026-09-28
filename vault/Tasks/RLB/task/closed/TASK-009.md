# TASK-009: PM_ACPI features deferred past the #54 fix

> Migrated 2026-09-27 from `vault/Tasks/RLB/closed.md` as **RLB-009** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.

**Priority:** P3. The block is functionally complete for its MVP scope and
6/6 configurations green at FULL (basic 8/8, medium 10/10, full 12/12, GH#54
17/17); nothing here is a defect.
**Status:** closed 2026-09-14. DONE apart from what was always out of scope. The two
reset-source pins landed 2026-09-10 in 6978cf935; S5 soft off, the button
debouncer with its long-press override, the PM timer prescaler / 64-bit mode /
comparator, the rail sequencer and the GPE work (level mode, the second bank,
the run/wake split) all landed the same day. Only legacy replacement routing
and the processor C/P-state hints remain, and both were scoped out rather than
deferred. Raised while closing issue #54. These items were
the surviving content of `rtl/pm_acpi/TODO.md`, which was deleted with that
fix: most of it described work already done (the DV suite, the helper-script
plan) or behaviour the fix changed (the "W1C edge detection / auto-clear
fields" architecture note, the "reset tracking simplified" limitation), so
keeping it would have meant maintaining a stale tracker next to the code.
Same disposition as [[RLB-008]] for ioapic.

**Deferred by design (MVP scope, stated in `rtl/pm_acpi/README.md`):**

- ~~Clock-gate and power-domain transitions are INSTANT. No ramp, no
  sequencing delay, no per-domain ordering. Real silicon wants a sequencer
  with programmable inter-domain delays and an acknowledge per rail.~~ FIXED:
  `PWR_SEQ_CONFIG.seq_enable` turns the instant transition into a walk -- rail
  7 down to rail 0 on the way out, rail 0 up to rail 7 on the way in, with
  `seq_delay` cycles between steps, the clocks gated before the rails drop and
  restored only after they are all back. `seq_ack_enable` makes each step wait
  for `power_domain_ack[N]`; a rail that never answers stalls the walk and
  `PWR_SEQ_STATUS` says which one. There is deliberately no timeout: a made-up
  one turns a board fault into a silent half-powered state. The sequencer is
  OFF at reset, which is the behaviour every existing integration has.
- ~~No S5 (soft off). The FSM is S0/S1/S3 plus a transition state.~~ FIXED:
  S5 is a real state. It gates every clock and every rail but the always-on
  one, like S3, but retains nothing, so LEAVING it pulses `sys_reset_req` -- a
  wake from soft off is a boot, not a resume. The two-bit `current_state`
  field reports encoding 2 for it, the one the three previous states left free.
- ~~GPE is rising-edge only and one bank of 32. No level mode, no per-event
  edge/level choice, no GPE1, no run-vs-wake split.~~ FIXED: `GPEx_TRIGGER`
  picks edge or level per source -- a level source's status bit follows the
  source, so a W1C while it is still asserted has no lasting effect, which is
  how software tells an event it missed from one still happening. `gpe1_events`
  is the second ACPI GPE block with its own status / enable / trigger / wake
  registers, sharing the interrupt and wake terms with bank 0.
  `ACPI_CONTROL.gpe_split_enable` splits the single mask in two: with it set,
  `GPEx_ENABLE` arms the runtime interrupt and `GPEx_WAKE_EN` arms the wake, so
  a source can wake a sleeping machine without interrupting a running one. With
  it clear the block behaves exactly as before.
- ~~PM timer is 32-bit with a single divider. No 64-bit mode, no prescaler
  options, no comparators.~~ FIXED: a power-of-two prescaler sits ahead of the
  divider (`PM_TIMER_CONFIG.timer_prescale`), extending the slow end of the
  range without widening a field software already uses; the counter is always
  64 bits and `timer_64bit` chooses which carry counts as an overflow, so
  widening does not cost the 32-bit overflow software may already watch;
  `PM_TIMER_MATCH` is an equality comparator on the low word that sets
  `ACPI_STATUS.timer_match` and drives `pm_interrupt` through
  `ACPI_INT_ENABLE.timer_match_enable`. `PM_TIMER_VALUE_HI` is a SNAPSHOT
  latched when the low word is read, so a pair of reads cannot straddle a
  carry and return a value the counter never held.
- ~~Buttons get a 3-flop synchronizer, not a debouncer: no configurable
  threshold and no long-press (the ACPI 4-second power-button override) --
  which is why `PM1_CONTROL.pwrbtn_ovr` is documented storage-only rather
  than wired to an invented meaning.~~ FIXED: a candidate level has to hold
  for `BUTTON_TIMING.debounce_cycles` before it is accepted, and holding the
  accepted level for 2^`BUTTON_TIMING.long_press_shift` cycles forces S5.
  `PM1_CONTROL.pwrbtn_ovr` now ENABLES that escape hatch rather than
  commanding it: as a command, any register sweep that happened to set the bit
  parked the machine in S5, which broke four existing tests.
- ~~`RESET_STATUS.wdt_reset` / `.ext_reset` always read 0.~~ FIXED 6978cf935:
  `wdt_reset_n` and `ext_reset_n` are device pins now, synchronized like the
  other board inputs and LATCHED rather than sampled, because the pulse that
  caused a reset is long gone by the time software reads the register.
- Legacy replacement routing (IRQ0 timer, IRQ8 RTC) and processor C/P-state
  hints are out of scope.

**Still open:** nothing in this entry that was deferred. Legacy replacement
routing (IRQ0 timer, IRQ8 RTC) and processor C/P-state hints stay out of
scope.

---
