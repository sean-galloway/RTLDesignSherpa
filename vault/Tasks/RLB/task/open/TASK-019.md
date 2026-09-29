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
`per-IR-line OK` lines by construction. **Measured 2026-09-29, and the premise this task was filed with was WRONG.**
Filed text said "the fabric tests are slow and the tiering may be deliberate".
They are not slow: the whole 15-method full list runs in **6.15 s**
(02:06:02.281 -> 02:06:08.432 in the cocotb log), the seven fabric tests being
0.4-1.4 s each. The ~3m47s cell time is almost entirely Verilator compile, which
every tier pays anyway. So there is no cost argument for the current tiering and
promoting a representative block to `func` is nearly free.

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

**Measured 2026-09-29: the filed description was too simple. RLB is in THREE
inconsistent states, not one.**

| Artifact | State |
|---|---|
| `rdl/hpet/generated/docs/hpet_regs.md` | untracked, **gitignored** (`rdl/.gitignore:5 generated/`), drifted 264 lines from its RDL -- sanctioned local build debris, NOT a defect |
| `rdl/ioapic/generated/docs/ioapic_regs.md` | untracked, gitignored, identical to a fresh regeneration |
| `rtl/smbus/docs/smbus_regs.md` | **TRACKED, generated, hand-edited, drifted 224 lines** |

The smbus one is the real defect and it is the exact trap CLAUDE.md Rule #0's
inverse-failure section names: a generated file edited by hand. Its diff opens
`0a1,23` -- the committed copy carries a 23-line documentation header the
generator never emits -- and its git history shows it last touched 2026-09-27 by
a tracker-id repointing sweep while its RDL last changed 2026-09-11. A docs
sweep edited a generated artifact.

**And beside it, `rtl/smbus/docs/` holds 8.0 MB across 75 TRACKED files**: a
complete PeakRDL HTML export (`smbus_regs.html/`) with 34 binary font files, 3
Windows `.bat` launchers, a Firefox `user.js`, JS, CSS and search indices.
Nothing references it -- zero external references to either the bundle or the
markdown. Every RLB manifest entry passes `--no-html`, so the current toolchain
would never reproduce it. Repo-wide only three such exports exist and the other
two sit in gitignored or proper `generated/` trees, so committing one into
`rtl/` is an outlier rather than a convention.

Deleting 75 tracked files including binaries is consequential and is left for an
explicit decision, not folded into this task silently. Either RLB joins the
convention, or the divergence is recorded as deliberate. Note the trap closed TASK-016 already hit: a hand-written
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

**Surveyed 2026-09-29, all eleven. The answer is PER BLOCK and a uniform
treatment would destroy specification content.** README lines vs MAS book pages:

| README | lines | MAS pages | Reading |
|---|---|---|---|
| `rtl/hpet/` | 791 | 16 | book is substantial -- likely duplicate |
| `rtl/smbus/` | 666 | **5** | README is the ONLY copy |
| `rtl/rtc/` | 468 | 6 | README is the only copy |
| `rtl/pic_8259/` | 395 | 5 | README is the only copy |
| `rtl/uart_16550/` | 371 | 26 | book is substantial -- likely duplicate |
| `rtl/pm_acpi/` | 344 | 5 | README is the only copy |
| `rtl/hpet/filelists/` | 290 | (n/a) | a FILELISTS directory README -- rule 1 tool mechanics |
| `rtl/apbx_xbar/` | 280 | **0** | no MAS book exists at all |
| `rtl/pit_8254/` | 259 | 14 | book is substantial -- likely duplicate |
| `rtl/ioapic/` | 201 | 12 | book is substantial -- likely duplicate |
| `rtl/gpio/` | 150 | 23 | book is substantial -- likely duplicate |

Concretely: `gpio`'s 150-line README (Features / Architecture / Parameters /
Register Map / Integration / Test Plan) is covered by a 23-page book, while
`smbus`'s 666 lines carry the open-drain contract, bit timing, clock
stretching, timeout, bus recovery, PEC, the FIFO contract and known limitations
against a 5-page book that is only an overview plus a register map. Gutting that
one would delete the specification.

Expected shape of the outcome: roughly five become pointers, four stay because
they are the only copy, and two (`apbx_xbar`, `hpet/filelists`) stay under rule
1. Confirm per block before editing; do NOT delete on size alone.

## Done when

- [x] **item 1 DONE 2026-09-29.** `Fabric routes GPIO to the 8259` moved from
      `full_methods` to `func_methods`, so `func` now exercises the per-IR-line
      check. Measured: func 5/5 with **0** per-IR-line lines -> **7/7 with 1**;
      full unchanged at 15/15 with 7.

      **The move broke the suite first, and the trap is worth recording.** The
      GPIO vector test has no `_fabric_preamble`: it requires the interrupt the
      routing test raised to be STILL PENDING. Moving only the routing test down
      put `Boot interrupt reaches the 8259` -- which calls `reset_and_init_pic()`
      -- between them, clearing the interrupt, and the vector test failed its own
      precondition (full 14/15). The runner's comment said "the routing test must
      run BEFORE the vector test", and a replacement comment asserting "func runs
      before full, so that ordering still holds" was WRONG: the real constraint is
      not ordering, it is that **nothing may RESET between them**. Both tests now
      live adjacent in `func_methods`.
- [x] **item 2 DONE 2026-09-29.** The source/line cross-check. `FABRIC_SOURCE_IRQ`
      (transcribed from rlb_top.sv's `w_fabric_irq` block) and
      `source_irq_consistent()` live in `rlb_top/ir_lines.py`, wired into
      `_routing_verdict` ahead of `_ir_lines_ok`. The hole it closes: a test
      naming `gpio_irq` while asserting fabric line 9 satisfied the source-name
      `expect_only()` and the per-IR-line check INDEPENDENTLY, and passed. An
      unknown source is an error rather than a skip, so adding a source without
      mapping it fails loudly instead of silently losing coverage. Unit tests
      18 -> 23, still simulator-free (verified with cocotb hidden and with
      PYTHONPATH stripped).
- [x] **item 3 DONE 2026-09-29.** Four coincident sources, including both slow
      ones. `test_fabric_handles_four_coincident_asserts`: SMBus (IRQ10) started
      FIRST because its NAK path is the slowest, UART (IRQ4, master) armed next
      and held, then GPIO (IRQ11) and PM/ACPI (IRQ9) as level inputs at random
      offsets. Logged: `per-IR-line OK: fabric [4, 9, 10, 11], master [2, 4]` --
      one master IR line direct, one cascade bit standing for three slave-side
      sources -- and IOAPIC delivery of 0x44, 0x49, 0x4A and 0x4B with all four
      coincident.

      **The settle waits for the SLOWEST source, not the last one armed** (1500
      pclk for SMBus). That is the defect TASK-018's three-source test shipped
      with: it sampled at the jitter offset, read `pm=False` with gap2=2, and
      failed its own simultaneity guard. All four sources are level-held, so
      waiting cannot weaken the overlap claim.
- [ ] item 4: RLB either joins the generated-docs convention or the divergence
      is recorded as deliberate in the manifest
- [ ] item 5: each of the eleven READMEs is a pointer, or is justified under
      rule 1 as directory mechanics
- [x] **DONE 2026-09-29 for items 1-3.** `rlb_top` full from `clean-all`:
      **16/16 with 8 per-IR-line lines** (was 15/15 with 7); `func` **7/7 with 1**
      (was 5/5 with 0); `gate` 1/1. Area sign-off `run-all-full-parallel`:
      **81 passed, 0 failures**, 6m07s, 15 roots, REG_LEVEL=FULL -- unchanged,
      because the new method lives inside the existing `rlb_top` cells rather
      than adding a test root. Re-run for items 4-5 when they are worked.

## Dependencies

RLB TASK-016 and TASK-018 -- both CLOSED; this is their unfiled remainder.
