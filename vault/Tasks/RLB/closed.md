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

## RLB-004 — Triage & fix the RTL bugs found by the MAS/RTL review
**Status:** closed 2026-09-14

The 9 `bug`-labeled issues from RLB-001, all fixed and all CLOSED on GitHub:
#44 gpio, #46 hpet, #48 ioapic, #50 pic_8259, #52 pit_8254, #54 pm_acpi,
#56 rtc, #58 smbus, #60 uart_16550, plus tracking #61.

This entry sat in `active` claiming "awaiting owner design decisions, not
started in RTL" for four days after the work had landed. It was STALE, not
paused: the fixes went in 2026-09-10/11 with commit references recorded in
[[RLB-008]], [[RLB-010]], [[RLB-011]], [[RLB-012]] and [[RLB-013]], and the
issues were closed at the same time. A tracker that claims active work which
is finished is worse than no tracker, because nobody re-reads it.

**Verified green today, not taken on trust.** A clean
`make clean-all && make run-all-full-parallel` across all nine blocks at
REG_LEVEL=FULL: **63 passed, 0 failed** in 343.60s.

pm_acpi was re-checked specifically, because a long-running agent reported it
"17/21 green with 4 genuine RED findings". That report was a stale snapshot of
a tree that moved under it (the agent ran ~119 hours; its files date 09-09 to
09-11). The GH#54 suite runs and passes 21/21 -- 21 distinct PASS strings, each
in 4 of the 6 cells, the gate-level cells not running it by design -- including
all four tests it named. The RTL it described as pending had already landed:
`pm_acpi_core.sv` edge-detects `cfg_sys_reset` (904/910/1268) because
`peakrdl_to_cmdrsp` holds `regblk_req` for the accept cycle plus one, so a
`singlepulse` field otherwise asserts for two cycles. Same mechanism and same
remedy as rapids' kick refactor -- worth knowing it bites in both components.

**What stays open is not a defect:** [[RLB-008]] (ioapic -- LowestPriority is
delegated by Sean's call; multi-IOAPIC routing, boot-interrupt delivery and MSI
are scoped out) and [[RLB-010]] (rtc -- the combinational clock mux is
DELIBERATELY not fixed and documented as a constraint). The one genuine open
work item anywhere in RLB is RLB-010's "no formal area exists for
retro_legacy_blocks".

**Owner decision RESOLVED 2026-09-14: nothing was stranded.** This entry once
claimed several unpushed RLB-001/002 doc-fix commits sat on branch
`dmas-reorg-and-stream-perf`, and a later reader correctly noted the branch was
gone -- but read that as work possibly lost. It was not: the branch was MERGED
through six pull requests (#38 and #40 on 2026-07-18, then #62-#65 on
2026-07-22/23) and deleted afterwards, which is why no ref remains.

Verified rather than assumed: the RLB-001/002 doc-fix commits `243affb32`,
`a1b76d082` and `dc88e1a65` are all ancestors of both `HEAD` and `origin/main`,
and EVERY commit touching `vault/Tasks/RLB/` or the RLB docs is on main. There
is no unpushed RLB work anywhere.

(A stale copy of the old wording survives in the `pumice-ataglance-modes`
worktree's RLB pages. That checkout is ~677 commits behind main and carries no
RLB commits of its own, so it is a snapshot, not unmerged work; it corrects
itself when that branch takes main.)

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
