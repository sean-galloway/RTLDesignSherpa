# TASK-019: the RLB follow-up batch -- three DV coverage gaps and two documentation inconsistencies

**Priority:** P3
**Status:** OPEN
**Owner:** unassigned
**Filed:** 2026-09-29 at the owner's direction ("file the batch into 19"). These
five were RECORDED in closed tasks but never filed, so nothing tracked them.
Sources: TASK-018's "Deliberately not claimed" list (items 1-3) and TASK-016's
"Two findings recorded, not acted on" (items 4-5).

## 1. The per-IR-line check runs at the FULL tier only

`_ir_lines_ok` is reached from `_routing_verdict`, which only the seven fabric
tests call, and those live in `full_methods`. `gate` and `func` log zero
`per-IR-line OK` lines by construction. Decide whether that is right -- the
fabric tests are slow and the tiering may be deliberate -- or promote one
representative block to `func`.

## 2. A set fabric bit proves the LINE, not the sub-source

`w_fabric_irq[IRQ_TIMER]` is `pit_timer_irq[0] | hpet_legacy_irq0` and
`w_fabric_irq[IRQ_RTC]` is `rtc_alarm_irq | rtc_second_irq | hpet_legacy_irq8`.
So bit 0 or bit 8 being set does not say WHICH source drove it. The BFM's
source-name `expect_only()` covers that separately, and nothing checks the two
together: a test could see the right fabric line and the wrong source and pass
both halves independently. Cross-check them in one assertion.

## 3. Four or more coincident sources are uncovered

TASK-018 proved three (UART IRQ4 master + GPIO IRQ11 + PM/ACPI IRQ9 slave).
SMBus (~1500 pclk to its NAK error) and PIT (~400 pclk to terminal count) have
never been placed in a coincident set, because their latency makes precise
overlap harder to arrange than a level input.

**Heed the defect TASK-018's own verification found here:** the three-source
test originally sampled "all sources high" only `gap2` (1-12 pclk) after the
last one was asserted, but PM/ACPI needs tens of cycles to reach `pm_interrupt`.
A four-source test must let the SLOWEST source settle before sampling, and the
settle must not be confused with the randomised arrival offsets -- those are the
coincidence being tested. All the sources are level-held, so a settle does not
weaken the overlap claim.

## 4. No RLB block has its generated markdown checked

All nine RLB manifest entries in `bin/check_rdl_regen.py` emit only
`<block>_regs.sv` and `<block>_regs_pkg.sv` (four also emit a `regmap.py`), and
none emits or compares a docs markdown. STREAM's entry, by contrast, emits
`regs/generated/docs/stream_regs.md` and compares it, as do pumice, rapids, misc
and the Genesys2/ddr2_char harnesses.

So RLB register documentation is not generated into a compared tree at all.
Either RLB should join the convention, or the inconsistency should be recorded
as deliberate. Note the trap closed TASK-016 already hit: a hand-written
`pm_acpi_regs.md` sat outside any generated tree, nothing regenerated it and
nothing compared it, and it had drifted -- it was deleted for exactly that
reason. Regenerate ONLY via `bin/peakrdl_generate.py` with an explicit `-o`
(CLAUDE.md Rule #0).

## 5. Eleven beside-code READMEs are standalone guides, not link pages

**TASK-016 recorded this as "rtl/<block>/README.md x10" and as a possible rule-2
violation. Both details were wrong, corrected here:**

- There are **eleven**, not ten. The missed one is
  `rtl/hpet/filelists/README.md`.
- [[doc-placement]] rule 2 forbids a README "anywhere under `rtl/`", but its
  next sentence is explicit: *"Outside `rtl/`, in project areas, a README is
  still allowed and still must be a link rather than a second copy."* These are
  in a PROJECT area, so rule 2 does NOT forbid them existing.

What they DO violate is that second clause, and rule 3 (one source per fact).
They are 4.5 KB to 34 KB of standalone specification:

| File | Size |
|---|---|
| `rtl/smbus/README.md` | 34 KB |
| `rtl/hpet/README.md` | 33 KB |
| `rtl/rtc/README.md` | 27 KB |
| `rtl/uart_16550/README.md` | 17 KB |
| `rtl/pm_acpi/README.md` | 17 KB |
| `rtl/pic_8259/README.md` | 16 KB |
| `rtl/pit_8254/README.md` | 10 KB |
| `rtl/apbx_xbar/README.md` | 10 KB |
| `rtl/ioapic/README.md` | 10 KB |
| `rtl/hpet/filelists/README.md` | 9 KB |
| `rtl/gpio/README.md` | 5 KB |

Each block already has a MAS book under `docs/`. Establish for one block whether
the README duplicates the book -- if it does, the README becomes a pointer and
the content stays in the book; if it carries mechanics a reader of that
directory genuinely needs, [[doc-placement]] rule 1 protects it and it stays.
Do NOT delete on size alone.

## Done when

- [ ] items 1-3: each either implemented with logged evidence, or recorded as a
      deliberate non-goal with the reason
- [ ] item 4: RLB either joins the generated-docs convention or the divergence
      is recorded as deliberate in the manifest
- [ ] item 5: each of the eleven READMEs is a pointer, or is justified under
      rule 1 as directory mechanics
- [ ] rlb_top suite green at the full tier from `make clean-all`, and the area
      unaffected at the sign-off tier, for any change touching DV

## Dependencies

RLB TASK-016 and TASK-018 -- both CLOSED; this is their unfiled remainder.
