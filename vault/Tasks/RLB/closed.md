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
delegated by Sean's call, and its consumer-side arbiter now ships as a
companion module; multi-IOAPIC routing, boot-interrupt delivery and MSI remain
scoped out). [[RLB-010]] has since CLOSED 2026-09-14: the formal area was
created, and the clock mux -- named here as deliberately not fixed -- was
resolved by `rtc_clk_mux`, which supplies the device-specific cell the entry
itself said was the real answer. This paragraph's claim that RLB-010's missing
formal area was "the one genuine open work item anywhere in RLB" is kept for
history and is no longer true.

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

---

## RLB-010 — RTC leftovers after the #56 fix
**Status:** closed 2026-09-14

All three bullets are resolved. The entry had stayed open only to HOLD the
clock-mux constraint -- explicitly "rather than because anything is pending" --
and that constraint now lives in the RTL itself, worded per branch, so the
reason to keep it open is gone.

`apb4_rtc` was 60/60 at the full level after the #56 rewrite (ten review rounds
on the clock-domain crossing); nothing in this entry was ever a defect. The
durable lessons are in the handbook: [[cdc]] Rules 1-7 and
[[no-assertions-in-rtl]].

- ~~Two shared CDC primitives are not verilator -Wall clean.~~ FIXED
  2026-09-10 in `dc4ea9db7`: the handshake's timeout counter now lives inside
  the generate branch that uses it, so at TIMEOUT_CYCLES = 0 it does not exist
  rather than existing unused; `glitch_free_n_dff_arn`'s waveform-only
  flattened copy is waived where it is declared rather than deleted; and
  `reset_sync`'s four power-on initialisers carry a scoped PROCASSINIT waiver,
  because the initialiser is deliberate on a device with no reset before the
  first clock.

- ~~`selected_clk` is a combinational clock mux.~~ RESOLVED 2026-09-14 in
  `ae03c6b43`. The reasoning that kept it open was sound and still stands: a
  PORTABLE glitch-free mux is a break-before-make handshake needing BOTH clocks
  running, while the whole point of `clock_select` is running from pclk when
  the crystal may be absent -- so a portable version cannot switch away from a
  dead clock and would replace the documented constraint with a worse one. The
  entry named the real answer, a device-specific cell, and `rtc_clk_mux` is it:
  BUFGCTRL with IGNORE0/IGNORE1 on XILINX (the IGNOREs are the point -- they
  complete the switch without waiting for the departing clock's edge, which is
  the stopped-crystal case), ALTCLKCTRL on INTEL, and the original expression
  bit for bit everywhere else.

  The fallback is deliberately IDENTICAL rather than improved: one that quietly
  behaved differently from the cell would be worse than no fallback. So the
  rtc_enable-low constraint STILL APPLIES on the default branch, and all
  thirteen constraint statements now say which branch they apply to instead of
  claiming the hazard is gone. Seven of those thirteen were sites a narrower
  sweep had missed -- one wrapped across a line break, one in ch01_overview that
  named no mux at all, and two TB comments quoting the old inline expression.
  Enumerating every mention of the term found them; grepping the sites already
  known did not.

- ~~No formal area exists for retro_legacy_blocks.~~ CREATED 2026-09-14.
  `formal/retro_legacy_blocks/` exists on the rapids pattern (aggregator
  Makefile -> per-block Makefile -> sv2v flatten -> sby), with the
  `rtc_config_regs` proof wired into the top-level `formal:` goal in the same
  edit that added it.

  **PROVED: the RTC_STATUS W1C strobe.** `clear_alarm_flag`,
  `clear_second_tick` and `clear_commit_timeout` are each asserted for at most
  one cycle per W1C transaction. It matters because `peakrdl_to_cmdrsp` holds
  `regblk_req` for the accept cycle PLUS one, so a strobe derived from it is
  presented twice unless edge-detected -- the same two-cycle hold that produced
  defects in rapids (kick) and pm_acpi (`cfg_sys_reset`) the same week.
  MUTATION-CHECKED: removing `&& !r_status_sw_wr_d` makes the proof FAIL and
  restoring it makes it PASS; all three covers are reached at step 2; the named
  properties appear in `design_smt2.smt2` (the SMT model -- NOT
  `design_smt2.log`, which contains none of them; grepping the log is itself a
  false vacuity test).

  **STILL UNPROVED, and known to be unprovable here: the seconds-read latch
  alignment.** It is a property of `w_seconds_latch`, an internal signal, and
  internal visibility is unavailable for this block in this toolchain. Four
  routes were tried and all fail:
    1. `dut.<sig>` with the DUT read as flat Verilog and the harness as SV --
       "ERROR: Failed to resolve identifier".
    2. the same with `hierarchy`/`proc`/`flatten` before `prep` -- identical.
    3. the same with harness and DUT sv2v'd into ONE file -- identical.
    4. `bind` -- yosys drops the checker silently and the proof passes with no
       property cells; caught by MUTATION, not by reading the log. sv2v cannot
       parse `bind` at all ("unexpected token 'bind'").
  Reading the RTL as SystemVerilog instead (how `formal/apbx_xbar` gets
  internal visibility) is closed off: yosys cannot parse the generated package
  -- "rtc_regs_pkg.sv:10: ERROR: Only PACKED supported at this time". So it
  stays CHECK BY INSPECTION in the module header, which
  [[no-assertions-in-rtl]] sanctions as the accepted state. If the bridge's
  capture cycle ever changes, re-derive the alignment by hand.

Verified before closing: `make clean-all && make run-all-full-parallel` across
all nine blocks, **63 passed / 0 failed in 343.50s** (known-good baseline
343.60s), with all six RTC cells showing zero failure markers.

Design decisions to know before touching the block (all stated in
`rtc_core.sv`'s header and the MAS): the commit handshake is deliberately not
cancellable (a timeout reports and releases the register block, the transfer
lands late rather than never; a one-sided cancel was tried and is a trap); the
queued commit slot carries its own watchdog and two marks (expired per
occupant, reported per slot); `COMMIT_TIMEOUT_CYCLES=0` disables both watchdogs
and then a commit on a dead clock hangs busy unreported; the counter domain's
reset release needs pclk running.

---

## RLB-012 — regblock reset polarity composed by hand
**Status:** closed 2026-09-14 (fixed 2026-09-10, `b953fd582`)

All nine wrappers instantiated their PeakRDL register block with
`.rst(~rst_n)`. The block does take an active-high reset, so the inversion is
right while the build is active-low and wrong the moment it is not:
`reset_defs.svh` makes polarity a compile-time property, so under
`-DRESET_ACTIVE_HIGH` the register file was held in reset permanently. No field
latched, every write acked and read back its default, and lint could not see
it -- all four permutations compiled clean.

Fixed by asking the macro instead: `` `RST_ASSERTED(rst_n) `` is "is reset
asserted", which is what an active-high reset port wants at either polarity.
Measured on gpio, writing 0xA5A51234 to GPIO_DIRECTION and reading it back:

| build | before | after |
|---|---|---|
| default | 0xA5A51234 | 0xA5A51234 |
| `-DRESET_ACTIVE_HIGH` | 0x00000000 | 0xA5A51234 |

**Verified in the TREE before closing, 2026-09-14, not taken from this entry.**
All nine `*_config_regs.sv` carry `.rst(`` `RST_ASSERTED(rst_n)``)`, and
`grep` finds no surviving `.rst(~rst_n)` anywhere in the area's RTL.

One discrepancy chased and resolved, recorded so nobody re-chases it: the fix
commit touched EIGHT files, not nine -- uart_16550 is absent from it. That is
not a gap. uart_16550's regblock instantiation was written later and written
correctly (`4e05b3d76`, then `3d6bd04e0`), so the tree is nine-of-nine even
though the commit is eight-of-nine. Counting files in the fix commit is the
wrong check here; grepping the tree is the right one.

Residual of the same defect class lives elsewhere: the FIFO primitives
underneath had it ([[COMMON-026]], fixed), and what remains is [[COMMON-027]].
[[RLB-015]] (SYNCASYNCNET under `-DRESET_ACTIVE_HIGH`, family-wide) is a
DIFFERENT finding in the same area and stays open.

---

## RLB-015 — SYNCASYNCNET under -DRESET_ACTIVE_HIGH, family-wide
**Status:** closed 2026-09-14 — measured, then fixed

Filed REPORTED-NOT-VERIFIED. It has now been measured across all nine blocks
at both polarities, and the five affected blocks are waived. Four things in the
original entry were wrong, and each is worth knowing because each came from a
plausible-looking check.

**1. The counts were LINE counts, not warning counts.** The entry reported
`RESET_ACTIVE_HIGH=3` for four blocks. `grep -c SYNCASYNCNET` returns 3 because
Verilator prints the warning plus two boilerplate lines ("For warning
description see ...", "Use lint_off ..."). Counted as `%Warning-SYNCASYNCNET`,
every affected block has exactly ONE. I reproduced the 3s exactly before
noticing I was reproducing the same artifact with the same broken instrument.

**2. The sweep was incomplete, in both directions.** Measured 9/9:

| block | default | RESET_ACTIVE_HIGH | note |
|---|---|---|---|
| gpio, pic_8259, pit_8254, rtc, uart_16550 | 0 | 1 | affected |
| hpet, ioapic, pm_acpi | 0 | 0 | genuinely clean |
| smbus | 0 | 0 | clean ONLY because already waived |

`pic_8259` is affected and was never in the report. `smbus` was cited as
evidence for a theory about its #58 reset rework; it is actually suppressed by
`lint_off -rule SYNCASYNCNET` in `smbus_regs.vlt`, wired in at
`apb4_smbus.f:36`. A "clean" block that is merely waived is not a data point.

**3. The rejected file:line citation was RIGHT.** The entry dismissed
`peakrdl_to_cmdrsp.sv:117` as "the closing paren of an ALWAYS_FF_RST macro, not
a reset usage". Line 117 is `` `ALWAYS_FF_RST(aclk, aresetn, ...) ``, which
under `-DRESET_ACTIVE_HIGH` expands to `always_ff @(posedge aclk or posedge
aresetn)` -- a genuine async reset usage, and exactly what Verilator names.
Reading the macro at the DEFAULT polarity is what made it look wrong. Only the
path was stale (`rtl/amba/shared/` -> `projects/components/converters/rtl/`).
The original reporter was correct and the rebuttal was the artifact.

**4. It is NOT a shared-file change.** The entry concluded that if the counts
held, the fix belonged in `converters` and needed owner sign-off before editing
a file every block instantiates. It does not. In every affected block the SYNC
side is the block's own generated `<block>_regs.sv` (`gpio_regs.sv:264`,
`pic_8259_regs.sv:313`, `pit_regs.sv:207`, `rtc_regs.sv:349`,
`uart_16550_regs.sv:399`), and Verilator names the net at that block's own cell
input -- so the waiver must attach there, which is what `smbus_regs.vlt` already
says in its own comment. Nothing shared was touched.

**The mechanism.** `reset_defs.svh` makes `RST_ASSERTED(rst)` expand to
`!(rst)` at default and `(rst)` under `RESET_ACTIVE_HIGH`, while
`ALWAYS_FF_RST` is asynchronous at BOTH polarities (`negedge rst` / `posedge
rst`). At default the inversion creates a derived net, so the async user and
the synchronous generated block see two different nets. Under
`RESET_ACTIVE_HIGH` the macro passes the net through and one net reaches both.
The warning is therefore a visible consequence of RLB-012's CORRECT fix, not a
regression from it.

**Fix applied 2026-09-14:** a `*_regs.sv`-scoped `.vlt` per affected block, on
the smbus pattern -- new `gpio_regs.vlt`, `pic_8259_regs.vlt`, `pit_regs.vlt`,
`rtc_regs.vlt` wired into their filelists ahead of the generated sources, and a
SYNCASYNCNET clause appended to the already-wired `uart_16550_regs.vlt`.
Verified per block: the one SYNCASYNCNET removed, total warning count down by
exactly one, default-polarity totals unchanged (gpio 26, pic_8259 32,
pit_8254 26, rtc 31, uart_16550 13). All nine blocks now 0/0 at both
polarities. filelist_registry --check 53/53, --audit PASS.

**NOT explained, recorded rather than guessed:** why hpet, ioapic and pm_acpi
are genuinely clean. Two rules were proposed and both refuted by measurement --
"inline ternary vs named intermediate wire" (smbus uses an inline ternary and
is affected) and "CDC default" (gpio still warns with `-GCDC_ENABLE=1`, smbus
still clean with `-GCDC_ENABLE=0`, both on runs confirmed to have executed). It
does not change the remedy, so it is left open rather than given a rule that
the evidence does not support.

**Spun out:** the entry said "retro_legacy_blocks has no lint target, so
nothing here is measured". The target EXISTS -- `projects/components/Makefile`
generates `lint-<component>` and advertises it in `make help` -- but it
delegates to `$(MAKE) -C <component>/rtl lint-all` and this area has no
`rtl/Makefile`. Filed as [[TOOL-017]]; `lint-apbx_xbar` is broken the same way.
