# RLB — Closed (done)

Completed retro-legacy-block work. Kept for history.

---

## RLB-001 — MAS/RTL quality review (9 blocks) via Kimi
**Status:** closed 2026-07-22

Ran a Kimi (kimi-k3) accuracy review of all 9 MAS-bearing RLB blocks (gpio,
hpet, ioapic, pic_8259, pit_8254, pm_acpi, rtc, smbus, uart_16550), each MAS
spec checked against its RTL as ground truth. No HAS docs exist — MAS only.
Pipeline + snapshots: `/mnt/data/github/rlb-doc-review/` (build_rlb_bundle.py,
RLB_REVIEWER_BRIEF.md, dispatch_rlb.py, send_rlb_round.py); reports and
`_DIGEST.md` in `results/kimi-k2/round_1/`. Findings filed as 18 GitHub issues
(#43–#60) + tracking #61: one `documentation` (MAS-wrong) and one `bug`
(RTL-BUG) issue per block. Every block had Critical findings.

---

## RLB-002 — Fix wrong-map MAS register documentation (5 blocks)
**Status:** closed 2026-07-22

The five blocks whose entire register map was wrong. Each MAS register chapter
+ ch01 summary (+ wavedrom README where it held a duplicate map) rewritten
against the RTL decode. Every offset independently re-derived from the RTL
`*_regs.sv` decode by the main session (not just agent-attested) — the check
script is `scratchpad/verify_regmap.sh` (RTL decode vs doc table offsets).

- **pic_8259** — commit `2fe735d1`, issue #49. Flat decode replaces the
  8259 A0=0/A0=1 model; documented PIC_CONFIG (pic_enable gates all operation)
  + PIC_STATUS. 11/11 offsets verified.
- **pm_acpi** — commit `5da2b442`, issue #53. Real ACPI_*/PM1_*/GPE0 map;
  documented the clock-gate/power-domain/wake/reset block at 0x50–0x6C that the
  review itself missed. 21/21 offsets verified.
- **rtc** — commit `ea724866`, issue #55. Every offset was wrong; removed
  phantom registers (century/weekday/date/alarm-date), fixed HR24 polarity,
  documented the time_set_mode protocol. 13/13 offsets verified.
- **smbus** — commit `cd415977`, issue #57. STATUS/CONTROL were swapped;
  documented INT_STATUS/PEC/BLOCK_COUNT the review stopped short of. 15/15.
- **uart_16550** — commit `871e34bc`, issue #59. DLAB remapping doesn't exist;
  flat map, all ch04 examples corrected, RBR-in-[15:8], W1C on LSR/MSR. 11/11.

RTL bugs surfaced by the review are NOT fixed here — tracked in the `bug`
issues (#50/#54/#56/#58/#60) and RLB-004 below.

---

## RLB-003 — Fix remaining MAS register documentation (4 blocks)
**Status:** closed 2026-09-08

The four targeted-fix blocks, integrated from the FULL round_1 critiques (not
just the issue-body Critical/High subset), every finding re-verified against
the current RTL first — a month of tree movement inverted one finding
(pit_8254 H4: CDC has since been implemented, 6/6 both configs on a clean
build) and healed parts of another (gpio L12 via the apb4 rename).

- **gpio** — commit `cb620291`, issue #43. CONTROL[1] INT_ENABLE documented
  at 8 surfaces (cited 4); 4 missing registers added to every map; reset
  values fixed; interrupt semantics rewritten to the RTL; atomic-write
  change-detection documented as a deviation (#44). Bonus: rtl/gpio/README.md
  had a fictional 16-bit LO/HI map.
- **hpet** — commit `368dcf83`, issue #45. HPET_ID hardcoded reality (+
  recomputed examples); dead timer_value_set (6 sites incl. the seeding RTL
  header comment); registered irq; sticky-in-both-modes; ghost
  HPET_CAPABILITIES swept 18 -> 0; wavedrom/graphviz maps redrawn (10 SVGs).
- **ioapic** — commit `1fceb370`, issue #47. Real direct decode documented
  (0x008-0x0D0 reachable without IOREGSEL/IOWIN); latency, glitch, FSM-output
  and status-page fixes; #48 deviation notes at both fire-once claims.
- **pit_8254** — commit `19c703de`, issue #51. Real interface (12-bit PADDR,
  PPROT, pit_resetn); no-SLVERR + 0x20 aliasing; PIT_STATUS reset recomputed
  0x00404040; RTOS-tick ISR fixed (readback-reload storm); count range
  1-65535.

Cross-block status surfaces reconciled in `81e09db8` (CLAUDE.md table said 8
implemented blocks were "Planned"; RLB_MODULE_AUDIT.md got the
historical-snapshot banner). Pre-commit sv-parse gate fixed en route
(`9d976529`: nested filelists were invisible to its index). All four issues
closed with commit references; RTL-bug issues #44/#46/#48/#52 re-verified
with dated comments.

---

## RLB-005 — Clean up rtc wavedrom README third register-map copy
**Status:** closed 2026-09-08

Commit `a1b76d08`. The README's third, contradictory map (TIME_LO@0x00,
REG_A/B/C, UIP, rate-select — a CMOS-style RTC this RTL never was) replaced
with the real 13-register map from rtc_regs.rdl; signal list and scenarios
rewritten to the RTL; rtc_periodic_interrupt.{json,svg,png} redrawn (it
contradicted the caption RLB-002 had already corrected);
rtc_update_in_progress.{json,svg} deleted (no UIP exists; nothing embedded
it). Verified against rtc_core.sv (irq gating at :439).
