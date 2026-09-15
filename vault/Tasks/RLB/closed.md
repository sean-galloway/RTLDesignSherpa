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

## RLB-006 — scrub the tests for completeness (retro legacy blocks)

**Priority:** P2. Blocks the coverage/formal push, not day-to-day work.
**Status:** closed 2026-09-14. DONE for retro_legacy_blocks 2026-09-11. Raised by Sean
2026-09-04: test scrubbing was meant to be part of the kimi review packets and
got dropped along the way. This entry covered the RLB suites; the same task in
the rtl/ areas is [[TASK-078]], [[COMMON-025]], [[MATH-010]], [[CDC-001]].

**What the pass found, criterion by criterion.** Each was checked
MECHANICALLY where a machine could check it, because the alternative is a
reviewer's impression:

1. *Every test exercises the DUT it names.* Clean. All nine wrappers build the
   `apb4_<block>` matching their filename.
2. *No test asserts a condition the bug itself satisfies.* ONE FINDING, fixed.
   `test_gh58_r4_10_tx_fifo_pstrb` imported the framework's `APBPacket` behind
   a try/except that returned **True** when the import failed -- a test that
   passes on the failure of its own precondition, so a framework rename would
   have turned it green while it drove nothing. The import is unconditional
   now.
3. *Inputs the DUT needs are actually driven.* Clean: 120 input ports across
   the nine tops, every one driven. The checker that proved it first reported
   `hpet_clk` and `rtc_clk` as undriven because it only recognised `.value =`
   and not `Clock(self.dut.x)`; a checker with false positives is one nobody
   reads, so it was fixed before its output was believed.
4. *gate/func/full mean something distinct.* THE BIG ONE, fixed. MEASURED
   BEFORE: pm_acpi's gate, func and full cells each logged
   `Starting FULL PM_ACPI` and each ran the identical 57 tests. All nine
   blocks were in that state, and hpet was worse -- every one of its six cells
   was pinned at `'full'`, so it had never run a gate or a func depth at all.
   Cause is TOOL-016: `cocotb_test.set_env` copies `os.environ` over
   `extra_env`, so the conftest `REG_LEVEL -> TEST_LEVEL` stamp beat every
   per-cell value. Converted both halves in one commit per the bridge's worked
   example -- every wrapper now parametrizes on `reg_level_grid()` and passes
   `level_env()`, and the stamp is gone. The grid moves now: GATE 21 cells,
   FUNC 41, FULL 61, where all three used to collect 49 and run them all deep.
5. *Every test offers gate/func/full.* ONE EXCEPTION, fixed 2026-09-11 after
   Sean restated the requirement: `test_rtc_gh56_timeout_sweep` collected
   exactly one cell at GATE, FUNC and FULL alike. It is levelled now, and
   what the levels MEAN there is deliberately unlike the rest of the area --
   every other test grades by how many suites run, this build exists for one
   narrow thing so it grades by how hard the watchdog is pushed: gate is the
   headline case, func adds the queued-commit orderings, full adds the
   same-edge races that sweep eight points apiece. The contract is that all
   three exist and differ, not that they differ the same way everywhere; a
   component's levels will not mean what a generic fub's do. Verified by
   collecting all three grids: every test is now 1/2/3 or 2/4/6, none flat.
6. *No `run()` pins `testcase=`.* Two pins in `test_apb4_rtc.py`, both
   JUSTIFIED and both covered: the module holds two `@cocotb.test()`
   functions that need different `COMMIT_TIMEOUT_CYCLES` builds, and each
   pytest cell pins its own. Checked by AST that no cocotb test in any module
   is unreachable. Nothing hidden.
7. *A fix landed with a test has its mutation check recorded.* Reported
   PARTIAL; **RETRACTED 2026-09-14 -- the gap does not exist.** ioapic,
   pit_8254 and rtc carried it in the test file; pm_acpi carries it in the
   GH54 suite; gpio and hpet had it only in commit messages and now carry it
   in the test files.

   This entry then said "**smbus, uart_16550 and pic_8259 have NO record that
   their defect-regression tests were ever seen RED**". That is FALSE, and it
   was checked before being retracted. All three carry one, two of them
   prominently:
   - pic_8259: `pic_8259_tests_medium.py:30`, "this suite was authored RED
     (2026-09-09) against the pre-fix RTL", plus per-test "expected RED
     against current RTL" notes in `test_apb4_pic_8259.py`.
   - smbus: `test_apb4_smbus.py:109`, "GH#58 RED regression tests -- written
     FIRST, against the unfixed" RTL, and the RED result named as the
     deliverable finding.
   - uart_16550: `uart_16550_tests_medium.py:524` and `:1128`, the GH60 and
     GH60-R2 batches both described as RED tests against the pre-fix RTL.

   **How the original claim went wrong is the lesson.** It was produced by a
   search that missed the phrasing those files actually use ("authored RED
   against the pre-fix RTL", "written FIRST against the unfixed"). The first
   re-check repeated the mistake with a pattern that ALSO returned zero for
   ioapic -- a known-present case -- which is what exposed it. A checker that
   returns zero for a case you know is present is measuring nothing; test the
   instrument against a known positive before believing its negatives. Nobody
   should revert a fix on the strength of the retracted claim.

**Still open elsewhere:** the same scrub for the rtl/ areas, and the
`bin/review/run_batch.py testqc` round, which has never been run for any
projects/components area (BRIDGE-007). This pass applied the brief's criteria
directly rather than routing them through the external reviewer; a testqc
round would still add value on the parts a machine cannot check.

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

---

## RLB-007 — all RDL lives in an rdl area, as it does elsewhere

**Priority:** P3. Hygiene, and cheaper here than anywhere else in the repo.
**Status:** closed 2026-09-14. DONE 2026-09-11. Raised by Sean 2026-09-04 for consistency with
[[MISC-001]]: all RDL belongs in an `rdl` area rather than scattered under
`rtl/`. All nine sources now live at `rdl/<block>/<name>.rdl` and all nine
register blocks regenerate from there byte-for-byte identically.

**The "only seven references" estimate below was wrong: there were about
forty.** Most are prose in READMEs, TASKS.md and DV comments rather than path
dependencies, so none of them broke the build -- but every one of them would
have become a wrong path. They were swept mechanically. The lesson is the
same one this ledger keeps teaching: count with a script, not by hand.

**Three things the move turned up:**

- `rtl/rtc/rtc_regs.sv` was a DIRECTORY, not a file, holding `rtc_regs.sv`
  and `rtc_regs_pkg.sv`, with the filelist pointing inside it. Someone had
  once run the generator with `--copy-rtl rtc_regs.sv`. Flattened to match
  every other block, filelist fixed.
- The seven `peakrdl/README.md` files were retired rather than moved, per the
  ledger's own instruction and the handbook rule: a README beside a tool
  restating how to run the tool is the copy nobody edits. They had already
  rotted into third copies of the register map. The generation command lives
  in the component `CLAUDE.md`, which now shows the new invocation --
  `--copy-rtl` has to name the RTL directory explicitly, since the RDL and
  the RTL are no longer parent and child.
- `BLOCK_STATUS.md` was retired. It presented itself as current status while
  calling GPIO and UART "Future" and PIC and IOAPIC "In Progress", all four of
  which have shipped with MAS books. The live table is in `CLAUDE.md`.
  `STRUCTURE_SETUP_SUMMARY.md` was kept: it is explicitly a dated record of a
  one-time 2025-10-29 task, so its old paths are accurate to that date.

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

---

## RLB-008 — IOAPIC features deferred past the #48 fix
**Status:** closed 2026-09-14

Every feature this entry tracked is built. Four of them ship as COMPANION
modules, which is what kept apb4_ioapic's delivery-channel interface intact
(Sean's 2026-09-11 decision): payload + valid/ready + status, so a bridge can
carry that shape onto a bus. `apb4_ioapic.f` references none of the four.

- **Logical destination mode** — FIXED 4bce6badc. The IOAPIC forwards the
  field and the mode; the local APICs match.
- **Round-robin arbitration** — `IOAPICARBCFG.rr_enable`, IOWIN selector 0x03.
- **LowestPriority, delegated** — the IOAPIC half landed 2026-09-11
  (`irq_out_retry`); the arbitration half ships as `ioapic_lowest_pri_arb`
  (7a4096b24), formal prove+cover PASS, system-context tested fab087467.
- **Multi-IOAPIC routing** — `ioapic_deliv_merge` (e0c77afc9), N channels
  merged round-robin with each message tagged by source id so an EOI routes
  back to the IOAPIC holding that pin's Remote IRR. Tested 72484a498.
- **MSI** — `ioapic_msi_emit` (4e60ac88b) plus programmable address and data
  (1bf991778: IOAPICMSIADDR/IOAPICMSIDATA at selectors 0x04/0x05) and seam
  tests (b274ccb6b). I had filed MSI as BLOCKED on "an APB slave has no
  initiator port"; Sean: *"Isn't msi just a write to an address"*. He was
  right — the emitting is the companion's job and the block stayed a slave.
- **Boot interrupt** — `ioapic_boot_intx` (21f071b93), gated on an enable bit
  AND the RTE mask, with the pin-to-legacy-IRQ map specified in rlb_top
  (identity for pins 0-7, no reroute above). This entry had carried a
  category error for weeks, mine: it described INIT-SIPI-SIPI, which is a
  local APIC's AP-startup IPI. The real feature is chipset INTx rerouting.

**One design question survives the close, already ruled on.** `deliv_retry` is
inert while the MSI write is posted: the delivery handshake closes when the
write is QUEUED (deliv_ready is the master's cmd_ready) and PSLVERR returns
strictly later, while ioapic_core samples retry AT the handshake. Measured --
handshakes=1, retry_asserts=1, retry_at_handshake=0. Sean: *"Silently drop is
bad. We at least need to count when that happens."* So drops are counted in
IOAPICMSIDROP (c9a3f0d40), in pclk with a gray-coded crossing; a counter in
ioapic_core read 0 in both CDC cells, which MED-9 caught.

**Verified at close:** 75 passed / 0 failed at REG_LEVEL=FULL (63 when the
arc began), formal 10/10 prove+cover through the retro_legacy_blocks
aggregator, and every new claim mutation-checked.

---

## RLB-009 — PM_ACPI features deferred past the #54 fix

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

## RLB-011 — SMBus features deferred past the #58 fix

**Priority:** P3. Raised 2026-09-10 while fixing issue #58 (master engine
rewrite). None of these is a defect in the master path; each is a feature
the block advertises in its RDL/MAS header but has never implemented.
**Status:** closed 2026-09-14. DONE. Arbitration and the read-direction quick command landed
2026-09-10 in 6978cf935, and target mode the same day.

- ~~**Slave mode.** `SMBUS_OWN_ADDR` and `slave_addr_int` exist; the slave FSM
  is a stub that never ACKs. The rewrite keeps it inert (it cannot touch SDA,
  the PEC accumulator or the master sequencer). A real slave needs: address
  match on the bus-sampled address byte (incl. general call / ARP if
  wanted), an ACK/NAK policy, an RX path into the RX FIFO with its own
  interrupt, a TX path from the TX FIFO for reads addressed to us with
  clock stretching while software fills it, PEC check/generate on the slave
  side, and arbitration with the master half for the shared pins (one
  engine on the wire at a time).~~ FIXED: `smbus_slave_engine.sv` is a
  separate module because the master owns the clock and a target does not --
  every target action is a response to an edge somebody else produced. It
  does address match (own address plus the general call behind
  `SMBUS_SLAVE_CTRL.gc_en`), an ACK policy (NAK the address when software
  says it is busy, NAK a data byte when the RX FIFO is full), the RX path
  into the shared RX FIFO, the TX path out of the shared TX FIFO with
  optional clock stretching while software fills it, its own PEC accumulator,
  and three new interrupt sources. ARP is still not implemented and is now
  recorded as a limitation rather than as deferred work.

  Two design points worth keeping. The target PEC NEVER COUNTS BYTES: a
  correct trailing PEC drives a CRC-8 to zero, so a write is checked by
  testing the running value at the STOP, and a read sends the running value
  once the queue is dry. And the ownership claim is "our target is
  ANSWERING", not "the bus is busy" -- claiming the wire for every observed
  START also claims it for a stuck one, since SDA held low under a high SCL
  looks exactly like a START that never ends, and the master could then never
  run the bus recovery that exists to clear it. That was caught by the
  existing GH58-R3-6 recovery test going red on the first, broader rule.

- **The framework's SMBusMaster BFM cannot see a clock stretch.** It releases
  SCL and then waits a fixed delay, so a stretching target is clocked straight
  through. The RLB smbus TB carries its own `ExternalSMBusMaster` that waits
  for SCL to actually read high, because slave mode is the feature stretching
  exists for. Worth fixing in RDS-DV so every block gets it.
- ~~Multi-master arbitration.~~ FIXED 6978cf935: every transmitted bit is
  read back in the SCL-high phase, and a 1 that reads as 0 means another
  master won. On loss both lines are released within the bit and the
  sequencer reports `arb_lost` and idles WITHOUT framing a STOP, because the
  winner's transfer is still in progress. Retry is software's.
- ~~Quick Command with R/W=1.~~ FIXED 6978cf935: transaction type 0xA is the
  read-direction form. The R/W bit IS the payload of a quick command, so each
  direction has its own code rather than a direction bit that would mean
  nothing for the other nine types.

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

## RLB-013 — UART 16550 features deferred past the #60 fix

**Priority:** P3. Raised 2026-09-10 while fixing issue #60. None of these was
a defect; each was a 16550 feature this block advertised in its register map
but had never implemented.
**Status:** closed 2026-09-14. DONE 2026-09-10, commit 3d6bd04e0. All five landed together with
the MAS flip. Kept here as the record of what they were.

- **Character-timeout interrupt.** `int_timeout` is tied to 0, so IIR never
  reads 0x0C and there is no four-character-time timeout. Software polling a
  partially filled RX FIFO below the trigger level has no interrupt to wait
  for. Needs a receive idle counter in the baud-tick domain, the IIR encoding
  (already reserved) and the read-side clear.
- **Auto flow control (AFE).** MCR[5] does not exist; CTS does not gate TX and
  RTS is not driven from the RX FIFO level. Needs both halves plus the
  threshold rule.
- **1.5 stop bits** for 5-bit words (LCR[2] with a 5-bit character produces one
  stop bit today).
- **DLAB remapping.** The map is flat: DLL/DLM have their own offsets and DLAB
  is a stored bit that remaps nothing. Legal for this block and documented, but
  it is not what a driver written against a standard 16550 expects.
- **DMA mode select.** FCR[3] is stored and never read.


---

## RLB-014 — the 800-line core cap is honored in the breach

**OWNER DECISION 2026-09-14, Sean: "800 is more of a guideline. Going over is
fine."** That settles it -- nothing here was a violation, so there is no work
in this entry and it closes.

For the record, because this was raised once by an agent and will be measured
again by another: the 800 figure is not a repo requirement. It lives in the
owner's personal cross-project coding-style rules ("200-400 lines typical, 800
max", under a MANY SMALL FILES heading written for software). It appears
nowhere in GLOBAL_REQUIREMENTS.md, any CLAUDE.md, the handbook, the skills, or
any checker or hook. This entry's phrase "the repo's 800-line guidance" was
wrong on that point.

Measured across the repo while closing: 144 of 660 files under
projects/components exceed 800 lines, and 18 of 422 under rtl/. Within RLB,
FIVE of the nine files over the line are PeakRDL-generated (pm_acpi_regs 2791,
smbus_regs 1499, uart_16550_regs 1282, rtc_regs 958, pic_8259_regs 850) and
cannot be split at all -- they regenerate from the RDL.

WORTH KEEPING, and the reason this entry was not pure noise: the cores are not
hard to split because they are long, they are hard to split because the DV
WHITEBOXES them. Measured distinct internal references from dv/:
  u_rtc_core    18   r_commit_busy, r_commit_pend, r_second_tick,
                     selected_clk, plus eight sub-instances
  u_uart_core    7   the coupling this entry already documented
  u_pm_acpi_core 5
So the ordering is inverted -- the LARGEST core (rtc, 1726) is the most
coupled and the hardest to refactor, and pm_acpi is the most tractable. That
coupling, not line count, is what would block any future restructuring. It is
recorded here rather than filed as its own task; open one if it ever matters.


**Priority:** P3. Hygiene and reviewability, not a defect — every block is
green. Raised 2026-09-14 by the uart_16550 verification agent and confirmed
by measurement.
**Status:** closed 2026-09-14. open, and it is a POLICY question for the owner, not a fix an
agent should take unilaterally.

Measured `wc -l` on the nine RLB cores:

```
1706  rtc/rtc_core.sv
1328  pm_acpi/pm_acpi_core.sv
 888  smbus/smbus_core.sv
 842  uart_16550/uart_16550_core.sv     <- 759 before the RLB-013 features
 705  hpet/hpet_core.sv
 666  pic_8259/pic_8259_core.sv
 552  ioapic/ioapic_core.sv
 331  pit_8254/pit_core.sv
 227  gpio/gpio_core.sv
```

Four are over the repo's 800-line guidance. smbus is the pointed one: it was
held to exactly 800 during the #58 review and has since grown to 888.

**The obvious cut in uart is blocked by DV.** The tests whitebox
`r_tx_state`, `r_tx_wr_ptr`, `r_tx_rd_ptr`, `w_tx_fifo_count`, `w_tx_bit` and
the RX equivalents at `u_uart_core` scope, so extracting TX or RX breaks tests
that an RTL agent may not edit. That constraint is why round 2 split modem and
intr instead, and the sweep confirmed that split was DV-safe (zero references
into `u_intr` or `u_modem`). Any split here is a DV change first and an RTL
change second.

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

---

## RLB-016 — an unmapped APB address hung the RLB bus
**Status:** closed 2026-09-14

The RLB crossbar was a HAND-WRITTEN sibling outside the apbx-xbar generator
flow, so it never received a fix the rest of the family got. Two divergences:

1. **No decode-miss agent.** `apbx_xbar_rlb_1to10` drove `m_cmd_ready` only
   inside `if (m_cmd_valid && addr_in_range)`, so an access outside the 40KB
   window was never accepted: `apb4_slave` never left IDLE, PREADY never
   asserted, and there was no timeout anywhere in that path. Its response-mux
   `default:` did set `m_rsp_pslverr = 1'b1`, but was unreachable --
   `r_slave_sel` only updates on an ACCEPTED command.
2. **Raw-PADDR decode.** It selected on `m_cmd_paddr[15:12]` where the family
   uses the OFFSET (`paddr - BASE_ADDR`). Latent: benign only because
   BASE_ADDR[15:12] is zero at 0xFEC00000; it breaks on any re-base.

**The finding was never "the responder is missing" -- it was that a hand-rolled
copy sat outside the generator flow.** The fix lives in the generator
(guarded `if N > 1`), whose own comment reads: "Emitting the decode without
this is what shipped that bug in every decoding variant."

**FIX.** `rlb_top` now instantiates the GENERATED `apbx_xbar_1to10.sv`, and the
variant is REGISTERED in `apbx-xbar/bin/generate_xbars.py` (an `external` list;
the only variant emitted outside apbx-xbar, at 0xFEC00000 with 4KB windows vs
the family's 0x10000000/64KB). Registration is the actual fix -- regenerating
once would simply have drifted again, which is what produced this entry.
`apbx_xbar_rlb_1to10.sv` and its orphan `.f` are deleted.

Full regeneration verified twice: all five shipped variants stay byte-identical
to HEAD and the RLB file reproduces exactly.

**Integration cost.** The generator emits indexed `sN_apb_*` carrying the FULL
address while all nine peripherals take `[11:0]`. rlb_top widens its ten
internal PADDR wires to [31:0] and slices `[11:0]` at each peripheral -- no
shadow signals, truncation visible at the consumer. Port count is unchanged at
112. The reserved slave-9 tie-off (0xDEADBEEF/PSLVERR/PREADY) stays in rlb_top;
the generator has no reserved-slave concept and does not need one.

**EVIDENCE (measured, not inferred).**
- `rlb_top` FULL: 3 cells, 5/5 checks PASSED, 426s.
- New `test_unmapped_address_errors` (func) probes BOTH failing edges of
  `addr_in_range` -- 0xFEBFFFFC below the map, 0xFEC0A000 the first address
  past it, 0xFEC0F000 well past -- each completing with PSLVERR, then a normal
  HPET read (0x01010180, PSLVERR=0) proving the single `r_m0_decerr_pending`
  bit CLEARS. Without that last check the test would pass against a crossbar
  that errors permanently after the first miss. 4 counted checks.
- **Negative control:** mutating the decerr branch to `m0_rsp_pslverr = 1'b0`
  makes it FAIL ("returned PSLVERR=0 ... must be reported, not silently
  served") while the three sibling checks stay green -- so the checker is armed
  and specific, not passing blindly. RTL restored and sha256-verified.
- Lint elaborates rlb_top with a passing negative control (a mis-named pin
  gives PINNOTFOUND); zero PINMISSING across all 112 connections.

This was previously recorded as untestable -- the BFM's completion loop would
hang until the cocotb timeout. That was true of the OLD crossbar; the generated
one completes the miss, so the case became reachable and is now encoded.

**Known cosmetic cost:** the generated crossbar adds 2 CASEINCOMPLETE warnings
(179 -> 181 in the rlb_top lint). Generator-wide -- no shipped variant emits
`default:` -- and benign: outputs are pre-assigned before the case and
slave_sel is bounded by addr_in_range, so 0xa-0xf are unreachable. The DV build
passes -Wno-CASEINCOMPLETE. NOT hand-patched, per the same rule this entry is about.

---
