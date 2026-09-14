# RLB — Open (accepted, not started)

---

### RLB-006: scrub the tests for completeness (retro legacy blocks)

**Priority:** P2. Blocks the coverage/formal push, not day-to-day work.
**Status:** DONE for retro_legacy_blocks 2026-09-11. Raised by Sean
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

### RLB-007: all RDL lives in an rdl area, as it does elsewhere

**Priority:** P3. Hygiene, and cheaper here than anywhere else in the repo.
**Status:** DONE 2026-09-11. Raised by Sean 2026-09-04 for consistency with
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

### RLB-008: IOAPIC features deferred past the #48 fix

**Priority:** P3. The block is functionally complete for its MVP scope and
36/36 green in all six configurations; nothing here is a defect.
**Status:** open. One item remains -- boot-interrupt -- and it is MIS-SCOPED,
not blocked; it needs re-scoping before anyone implements it.
Logical destination mode landed 2026-09-10 in 4bce6badc and round-robin
arbitration the same day; LowestPriority's IOAPIC half landed 2026-09-11. The
table-size note was examined 2026-09-14: the actionable part was a false claim
in the module header, now fixed; the rest cannot be done in SystemRDL.

Two of the four remaining items shipped 2026-09-14 as COMPANION modules, which
keeps Sean's 2026-09-11 interface decision intact -- apb4_ioapic's port list is
unchanged and apb4_ioapic.f references neither file:
  - LowestPriority's delegated arbitration half: `ioapic_lowest_pri_arb`
    (7a4096b24), formal prove+cover PASS, mutation-checked. SYSTEM-CONTEXT
    TESTED 2026-09-14 (fab087467): four seam tests against a real apb4_ioapic
    delivery channel, themselves mutation-checked -- mis-wiring `deliv_dest`
    fails both cells, tying `cpu_can_accept` high fails only the cell that
    owns the retry test.
  - Multi-IOAPIC routing: `ioapic_deliv_merge` (e0c77afc9), N delivery
    channels merged in round robin with each message tagged by source id so an
    EOI routes back to the IOAPIC holding that pin's Remote IRR. Formal
    prove+cover PASS, mutation-checked. SYSTEM-CONTEXT TESTED 2026-09-14
    (72484a498): four seam tests against TWO real apb4_ioapic instances, with
    three mutations each breaking exactly the cells that make the matching
    claim (3 / 2-of-3 / 1-of-3 failures).

  Why the seam tests exist when formal already passes: formal proves each
  companion's contract at its OWN ports with free inputs, and for the merge one
  claim is not checkable there at all -- `m_src_id` is self-consistent under
  formal whatever it names, so a merge that routed payloads correctly and
  mislabelled the ORIGIN would prove clean and break EOI routing on silicon.
  The seam tests use real producers; the consumer is still the testbench, so
  behaviour against a real LAPIC or a genuine multi-IOAPIC system remains
  uncovered.

MSI SHIPPED 2026-09-14 as a third companion, `ioapic_msi_emit` (4e60ac88b),
which bridges the delivery message onto an `apb4_master_stub` as a posted write
and returns PSLVERR as `deliv_retry`. I had filed MSI as BLOCKED on the grounds
that `apb4_ioapic` is a slave with no initiator port. Sean: "Isn't msi just a
write to an address". That was right, and the block stayed a slave -- the
emitting is the companion's job.

Its address and data are REGISTERS, not parameters (Sean's call, 2026-09-14):
IOAPICMSIADDR at IOWIN selector 0x04 and IOAPICMSIDATA at 0x05, both reserved
on the real 82093AA, surfaced as `cfg_msi_addr` / `cfg_msi_data`. Those two
outputs are the only ports apb4_ioapic has grown beyond the delivery channel,
and they are quasi-static config rather than the live per-CPU state Sean's
2026-09-11 decision rejected.

STILL OWED on MSI: the emitter has formal proofs but NO DV test, and Sean has
asked for one. Adding the two ports also broke every consumer that does not
connect them -- 6 regression cells in the two companion TB tops, plus
`rlb_top.sv`, which no test elaborates and which therefore failed silently.
`bin/check_port_consumers.py` catches exactly this, and it DOES run
automatically -- as a pre-commit hook, which is what would have caught the
break had the ports been added in a commit rather than sitting in the worktree
across a regression. Run by hand with nothing staged it exits 0 having examined
nothing, so to check before staging it must be passed the changed files.

Boot-interrupt is what remains, and it needs RE-SCOPING before anyone
implements it -- the requirement as written here was wrong. See the two
bullets below.

Raised while closing issue #48. Those deferred features were the surviving
content of `rtl/ioapic/TODO.md`, which was deleted with that fix along with
`INTERRUPT_DELIVERY_DEBUG.md` -- both described the delivery FSM that the #48
fix removed, so keeping them in sync would have meant rewriting two stale
trackers next to the code instead of recording the open work here.

**Deferred by design (82093AA features the MVP does not implement):**

- ~~Logical destination mode.~~ FIXED 4bce6badc: `irq_out_dest_mode` carries
  the RTE's mode alongside the destination. An IOAPIC does not decode logical
  destinations itself - it forwards the field and the mode, and the local
  APICs match - so forwarding the mode is the whole of this block's
  responsibility for logical delivery.
- **LowestPriority delivery mode: the IOAPIC half is DONE 2026-09-11, and it
  is delegated.** Sean's call. An IOAPIC does not track CPU priority and
  never did: on the APIC bus it broadcast the message and the local APICs
  arbitrated among themselves using their Arbitration Priority Registers,
  and one of them accepted. So the destination, the destination mode and the
  delivery mode were already forwarded unmodified -- the missing half was
  never the choosing, it was being told the choice FAILED.

  `irq_out_retry` is that half. Qualified by the delivery handshake, it says
  the receiver consumed the message and nobody could accept, so the interrupt
  must be offered again. The core now separates two events that used to be
  one: `w_deliv_done` frees the output stage and moves the rotation, while
  `w_deliv_accept` (done AND not retry) is what retires an edge latch, sets
  Remote IRR and latches the delivered vector. Tie the pin low and the
  channel behaves exactly as it did before.

  WHAT A CONSUMER STILL OWES: the arbitration itself. A LAPIC cluster hanging
  off this channel receives (vector, destination, destination mode, delivery
  mode), and for mode 001 it picks the lowest-priority CPU in the destination
  set and accepts, or refuses with retry if none can. Nothing about that lives
  here, which is the point of delegating it.

  Known sharp edge, documented rather than papered over: under STATIC priority
  a refused pin is the lowest eligible number and wins the next arbitration
  immediately, so a persistent refusal monopolises the channel. Round robin
  fixes it, which is the same answer static priority's starvation has
  everywhere else in this block.

  The other modes are still only forwarded: SMI/NMI/INIT/ExtINT ride
  `irq_out_deliv_mode` unmodified and the IOAPIC does not act on them.

- **Context for the interface shape (Sean, 2026-09-11):** the intent is to
  hang an open-source IA core, moved onto AMBA, off this block. That is why
  the delivery channel stays a payload plus a valid/ready handshake plus a
  status, rather than growing per-CPU priority inputs: a bridge can carry
  that shape onto a bus (the retry becomes a response), whereas a bundle of
  live per-CPU priority registers could not cross a bus at all without going
  stale.
- ~~Dynamic priority rotation. Arbitration is static, lowest IRQ number wins,
  and a continuously asserted high-priority level pin can starve the rest
  whenever software EOIs it promptly. Round-robin would fix it; that is a
  behaviour change, not a bug fix, so it is not being smuggled into #48.~~
  FIXED: `IOAPICARBCFG.rr_enable` (IOWIN selector 0x03, reserved on the real
  part) starts the scan just above the last ACCEPTED pin and wraps, so every
  eligible pin is served before any pin is served twice. The pointer moves
  only on an accept, or a stalled consumer would walk it round the ring. Off
  at reset, so a driver written for the 82093AA sees the 82093AA scheme. The
  directed test asked for below is the one that ships with it: it parks the
  pointer between two contenders and checks that the two policies deliver
  them in opposite orders, with the static run as its own control.
- ~~Multi-IOAPIC routing.~~ SHIPPED 2026-09-14 as `ioapic_deliv_merge`
  (e0c77afc9), a companion rather than a port change, and system-context
  tested in 72484a498. The area grid moved 63 -> 66 -> 69 cells at FULL as the
  two companion tests landed; both run inside
  `make clean-all && make run-all-full-parallel`, not only standalone.
- **Boot-interrupt delivery. MIS-SCOPED -- the requirement needs restating
  before anything is built.** This entry has been carrying a category error,
  and it was mine: `git log -S "INIT-SIPI-SIPI"` traces the framing to
  23df0dbf0 / 105c1b186, my own commits, citing no source. The MAS references
  only the 82093AA datasheet, which contains neither SIPI nor a boot-interrupt
  section.

  The two things it conflates are unrelated:
  * **INIT-SIPI-SIPI** is the AP startup sequence one LOCAL APIC sends another
    as an IPI. An IOAPIC never originates it. "No SIPI encoding in the
    delivery-mode field" is true and beside the point -- the field would not
    carry it even on real silicon.
  * **Boot interrupt** is the chipset behaviour where a PCI device's INTx is
    rerouted to the legacy PIC when IOAPIC delivery is masked or disabled, so
    an interrupt raised before the OS programs the IOAPIC is not lost.

  If the second is what is wanted, it is a real and implementable feature, and
  it is about the INTERACTION between this block and `apb4_pic_8259` rather
  than about a delivery-mode encoding -- which makes it a different design
  question than the one this entry has been posing. If the first is wanted,
  it belongs to a LAPIC, not here.

  NOT IMPLEMENTED, deliberately: building to a mis-stated requirement would be
  worse than leaving it. What is needed first is which of the two is meant.
- ~~MSI/MSI-X.~~ SHIPPED 2026-09-14 as `ioapic_msi_emit`, a third companion.

  **This entry called it BLOCKED and that was wrong.** MSI is a posted write of
  one data word to one address; the claim "no initiator port exists" was true
  but the conclusion did not follow, and this bullet's own parenthetical held
  the answer -- "or bridge the existing delivery channel onto one". Sean's
  2026-09-11 interface decision says the channel stays payload + valid/ready +
  status precisely so "a bridge can carry that shape onto a bus (the retry
  becomes a response)". That sentence describes the module. apb4_ioapic is
  untouched and apb4_ioapic.f does not reference it.

  It consumes the delivery channel, drives `apb4_master_stub`, and maps the
  write's PSLVERR back to `deliv_retry`. Its `deliv_*` ports are field-for-field
  identical to `ioapic_core`'s `irq_out_*` AND to `ioapic_deliv_merge`'s `m_*`,
  so a multi-IOAPIC system chains merge -> emitter with no adapter.

  Formal prove+cover PASS, five covers reached. MUTATION-CHECKED with four,
  each breaking exactly the properties that make the matching claim: moving the
  destination field (ap_addr_dest + ap_cmd_packing), reading prdata's top bit
  instead of pslverr (ap_retry_iff), swapping address/data order (all five
  field properties), and swapping vector with delivery mode (ap_data_vector +
  ap_cmd_packing). The third is the one that tested the PROOF rather than the
  design: the harness builds the expected command from the SPEC, so a
  restatement that had quietly copied the DUT would have survived it.

  **TWO OPEN DECISIONS, both deliberately not made unilaterally:**
  1. *Posted-write retry timing.* `deliv_ready` follows `cmd_ready`, so the
     delivery handshake completes when the write is ACCEPTED, while PSLVERR
     arrives later. A refusal can therefore land after ioapic_core has retired
     an edge pin's latch -- losing the interrupt instead of re-offering it. The
     alternative holds `deliv_ready` until the response, which serialises to
     one MSI in flight. The posted form is what shipped.
  2. *The encoding is a default, not a derivation.* Nothing in the RTL, RDL or
     MAS commits to an MSI format, so this uses the x86 convention:
     addr[19:12]=destination, data[7:0]=vector, data[10:8]=delivery mode,
     data[11]=destination mode. Two `always_comb` blocks are the whole format.

  Address and data arrive as PORTS, not registers, to keep it a pure companion.
  Register-backing them is a separate change: new RDL at a reserved selector
  (0x04/0x05 are free, following the IOAPICARBCFG @ 0x03 / 0xD4 precedent),
  regblock offsets 0xD8/0xDC free, regenerated only via
  `bin/peakrdl_generate.py` -- it touches generated files and the block's
  decode, so it is not bundled here.

**The table-size note, re-stated 2026-09-14 after examining it.**
`ioapic_regs.rdl` fixes the table at 24 entries (`IOREDTBL[24] @ 0x14`) while
`ioapic_core` scales with NUM_IRQS. The original suggestion -- "make the RDL
entry count generated from the same parameter" -- CANNOT BE DONE as written:
SystemRDL has no parameters, which this repo already records at
`projects/components/misc/rtl/tally_regs.rdl:22` ("RDL has no parameters").
It would mean templating the `.rdl` itself, i.e. generating the source of a
generated file, which exists nowhere here -- a large mechanism for a P3 note.

What was actually wrong was the HEADER, and that is fixed. It claimed
"Nothing in the RTL rejects another value" while the elaboration-time
`param_check` at the bottom of the same file `$error`s on exactly that. Both
landed in `c67e9c31a`, whose message says the `initial ... param_check` guards
stay; the header swept the surviving guard in with the deleted SVA. gpio and
hpet carry the same guard with no such claim, so this was an ioapic-only
wording slip. The guard is the correct mechanism and is untouched.

**Considered and declined: driving `IOAPICVER.max_redir` from NUM_IRQS.**
It is `sw=r, hw=na` with a hardcoded `8'h17`, referenced nowhere in the
generated block, `ioapic_config_regs` or `ioapic_core` -- so software reads 23
whatever NUM_IRQS says. Making it track the parameter costs an RDL change, a
PeakRDL regeneration of two files, a new RTL driver, a DV change
(`ioapic_tests_basic` fails if `max_redir != 23`) and a MAS change -- to report
a value the guard in the same file already forces to 24. Revisit only if
NUM_IRQS ever becomes genuinely free, which needs the RDL problem solved first.

**Still open: boot-interrupt, and it is MIS-SCOPED rather than blocked.** The
requirement as filed conflated two unrelated things; see its bullet. Nothing
should be built against it until it is restated.

All three of the other deferred 82093AA features shipped 2026-09-14 as
companion modules, outside apb4_ioapic's port list by design: multi-IOAPIC
routing (e0c77afc9), LowestPriority's delegated arbitration half (7a4096b24),
and MSI delivery (`ioapic_msi_emit`).

### RLB-009: PM_ACPI features deferred past the #54 fix

**Priority:** P3. The block is functionally complete for its MVP scope and
6/6 configurations green at FULL (basic 8/8, medium 10/10, full 12/12, GH#54
17/17); nothing here is a defect.
**Status:** DONE apart from what was always out of scope. The two
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

### RLB-011: SMBus features deferred past the #58 fix

**Priority:** P3. Raised 2026-09-10 while fixing issue #58 (master engine
rewrite). None of these is a defect in the master path; each is a feature
the block advertises in its RDL/MAS header but has never implemented.
**Status:** DONE. Arbitration and the read-direction quick command landed
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

### RLB-013: UART 16550 features deferred past the #60 fix

**Priority:** P3. Raised 2026-09-10 while fixing issue #60. None of these was
a defect; each was a 16550 feature this block advertised in its register map
but had never implemented.
**Status:** DONE 2026-09-10, commit 3d6bd04e0. All five landed together with
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

### RLB-014: the 800-line core cap is honored in the breach

**Priority:** P3. Hygiene and reviewability, not a defect — every block is
green. Raised 2026-09-14 by the uart_16550 verification agent and confirmed
by measurement.
**Status:** open, and it is a POLICY question for the owner, not a fix an
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

