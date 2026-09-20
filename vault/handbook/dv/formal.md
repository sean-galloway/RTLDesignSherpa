---
title: Formal
summary: sv2v/SBY flow; in-RTL properties; mutation rule; vacuity traps.
---

# Formal (SymbiYosys via sv2v)

Flow: tools/gen_formal_deps.py regenerates each formal dir's Makefile DEPS
closure (run after RTL moves). Flatten runs sv2v --define=FORMAL
--exclude=Assert.

Rules - each guards against a proof that PASSES while checking nothing:
- sv2v silently DELETES immediate assertions without --exclude=Assert.
  Verify the flat .v contains your asserts (grep count).
- Properties live IN the RTL under `ifdef FORMAL - full internal
  visibility, and every proof including the module checks them.
- MUTATION-CHECK every property: break the RTL -> prove FAIL; restore ->
  prove PASS. A property that never failed has never been tested. (The old
  block_ready property restated the assign - tautological - and the wedge
  shipped under passing formal.)
  - **A mutation that PASSES can be the CORRECT answer, not a weak property.**
    If the term you broke is redundant, the mutant is semantically identical
    and passing is right. *Case (2026-09-11): dropping `m_apb_PENABLE` from
    apb4_master_cg's wake term left the proof passing. PSEL and PENABLE are
    both master OUTPUTS and APB never asserts PENABLE without PSEL, so that
    term can never be the only thing awake.* Before concluding a property is
    weak, ask whether anything else already covers the term you removed; then
    mutate the term nothing else covers (here PSEL), which fails. That
    failure doubles as the NON-VACUITY check -- the antecedent has to be
    reachable for the property to fail at all, so one good mutation retires
    two doubts.
- Vacuity traps: hierarchical refs to nonexistent nets elaborate as FREE
  WIRES (watch yosys warnings); unconnected inputs model constant-x; a
  harness sized below the engagement threshold makes gated logic constant.
- SCRIPT ORDER decides whether an undriven input is pinned. sby's own plain
  `prep` runs `setundef -undriven -anyseq`, so an input the harness never
  drives, or never even connects, is FREE -- measured 2026-09-11: the
  axi_master_wr_splitter harness reaches fub_awaddr 0x40 AND 0x80 with those
  nets undriven. But a custom `[script]` that runs an `opt` pass BEFORE any
  `setundef` folds the undriven net to a constant first, and that input is
  pinned for the whole proof. Loud form: a cover needing it is unreachable
  whatever the RTL does -- the four axi4 *_mon monbus covers were unreachable
  for as long as they existed, with sixteen inputs pinned, and became
  reachable at step 11 the moment `setundef -undriven -anyseq` ran first.
  Silent form: everything passes with the input held at one value.
  **The fix is the order, not the harness**: every custom script frees
  undriven nets before its first `opt` (all 25 that did not were changed
  2026-09-11). `bin/formal_audit_stimulus.py` reports only tasks whose script
  still folds. *Corrected the same day: this bullet first said any undriven
  input is pinned. That was true of the scripts I had been reading and false
  of plain prep, and it put a wrong premise into TASK-092 and the audit tool
  until a probe was run.*
- MUTATING RTL IN A SHARED TREE: restore by ABSOLUTE path, and verify by
  byte-compare. The worktree is shared, so a mutated `rtl/` file is live for
  every other agent until it is put back. *Case (2026-09-11): a mutation run
  restored through `trap 'cp -p BAK $RTL' EXIT` with `$RTL` relative. The
  subshell had `cd`'d into the formal task directory to run the proof, so the
  trap's relative path pointed nowhere, `cp` failed, and the shared
  axi_master_rd_splitter.sv stayed mutated -- while a full-depth proof I had
  just launched rebuilt its flat file from the mutant. Caught only because
  the next line byte-compared the file against the backup.* A trap that
  restores is not a restore until `cmp` says so; check `grep -c MUTANT` and
  `git diff --stat` on the file after every mutation run, and never launch a
  proof of the real RTL in the same breath as a mutation.
- FIND YOUR OWN BACKGROUND JOB BY EXACT ARGV, NEVER `pgrep -f <script>`. The
  shell running your command has the script's name in ITS command line too,
  so `pgrep -f` matches it and `kill -- -$pgid` kills the command doing the
  killing, mid-way. *Case (2026-09-11): stopping a timing run that way killed
  the stop command itself; its output ended at the first echo.* Match on
  argv instead: `ps -eo pid,cmd | awk '$2=="bash" && $3=="/path/to/job.sh"'`
  -- your own shell is `/bin/bash -c ...` and cannot match.
- PROVING A FORK IS WORSE THAN NO PROOF. Three arbiter monbus tasks each held
  a hand-copied `<module>_formal.sv` beside the harness -- 251 to 287 lines
  divergent from the shipped RTL -- plus a cut-down package stub, because
  yosys could not resolve package-typed ports. They were green-by-construction
  about code nobody ships. sv2v resolves those types, so the fork is never
  needed: flatten the real module. Any `*_formal.sv` copy of an RTL file in a
  formal directory is this smell ([[silent-fallbacks]] rule 15).
- A PASSING PROOF ONLY COVERS THE PROPERTY YOU WROTE. Ask what the property
  does NOT say before trusting it as coverage of a contract.
  *Case: formal_axi_monitor_addr_check proved "addr_pkt_valid is sticky" and
  passed through all FIVE instances of an AMBA-MONBUS-STABILITY violation,
  because sticky VALID is not sticky PAYLOAD -- the half of the valid/ready
  contract actually being broken. A directed test found each instance one at a
  time; adding `ap_payload_stable` (data == $past(data) while valid &&
  !ready) FAILS at step 5 against the unfixed RTL and covers the whole class
  by proof.* For any valid/ready interface, BOTH halves are properties:
  valid is sticky AND payload is stable until accept. Writing only the first
  is the easy mistake, and it looks like coverage.
- "prove" here is BMC depth 25, not induction - claim accordingly.
- Formal at small N is blind to synthesis pathology
  ([[priority-logic-depth]]) - synthesis is its own gate.
Trackers: formal/FORMAL_TODO.md, formal/FORMAL_PRIORITY.md.

## Two sv2v/yosys traps met on wb4 (2026-09-09)

- **`'0` inside `$past()` does not flatten.** `$past(x) != '0` becomes
  `{$bits(type($past)) {1'sb0}}` and yosys fails with "Can't resolve function
  name `\type'". Write `$past(x) != 0`.
- **`// synthesis translate_off` is not a guard for yosys.** A `$display` in a
  translate_off block becomes a `$check` cell and async2sync refuses it
  ("TRG_WIDTH > 1"). Wrap simulation-only report blocks in `` `ifndef FORMAL ``
  as well; the flatten runs with `--define=FORMAL`.
- **A sim loop cannot reach what the peer never does.** The wb4 master/slave
  loop test caught two of three RTL mutations; "slave terminates outside
  CYC" survived because wb4_master never drops CYC with transfers in flight.
  The slave harness's FREE master reaches that abort (cover `cp_abort`,
  step 5) and the mutation FAILs the proof. When the DV peer is a
  well-behaved sibling block, the environment-rule properties belong in
  formal with a free peer, not in the loop.

## Mutate the PROPERTIES, not just the RTL (2026-09-10)

A passing proof says the properties you wrote hold. It says nothing about
whether they describe the contract. Mutation testing is the only cheap way to
find out, and it is worth running against formal exactly as against a test:
break the RTL, and a proof that still passes has a hole in its property set,
not a bug in the design.

*Case: `wb4_to_axil4_core` merges AXI4-Lite's two independent response
channels back into Wishbone's in-order termination. The first property set
proved every ordering rule -- write pairs AW with W, one direction per
command, only the head's channel is consumed, the open count is bounded, the
status mapping -- and it still PASSED a mutation that asserted `rsp_valid`
whenever EITHER channel had a response, which returns a status and data read
off a channel that has nothing. Simulation caught it as a hang; formal did
not. The missing property was that a presented termination must be BACKED by
a real response on the head's own channel (`ap_rsp_backed`). Adding it made
the mutation fail, which is the only evidence that the property earns its
place.*

The general shape: ordering properties constrain WHICH response is taken and
say nothing about whether one EXISTS. Any time a property set talks about
selection, check that something also asserts presence.

Mutating the flattened `*_flat.v` rather than the RTL keeps the source clean
while iterating, and the harness rebuild is skipped -- but restore it and
re-prove before believing the green.

## The direct-SV flow is the fragile one; sv2v is the front end (2026-09-11)

A formal task here reads its RTL one of two ways: **direct**, where the `.sby`
`read -formal -sv`s the SystemVerilog itself, or **flatten**, where a per-task
Makefile runs sv2v first and the `.sby` reads plain Verilog. The newest work
(wb4, the monitors) uses flatten. Most older tasks use direct.

Measured across every task for repo-root `rtl/`: **every single unrunnable
proof in the direct flow failed for the same reason -- yosys's own
SystemVerilog frontend could not read the RTL.** Not one was a property
defect. The constructs it choked on:

| Construct | Seen in |
|---|---|
| nested size cast `8'(32'(x))` | apb4/apb5 monitor |
| `N'(signed'(...))` casts | bf16 exp2, reciprocal, log2, goldschmidt, newton-raphson |
| package-typed ports (`pkg::type_t`) | arbiter monbus wrappers -- the port is silently DROPPED, and the error is "no port named ..." |
| unpacked array ports (`logic [W:0] d [8]`) | all five softmax_8 |
| non-constant parameter width range | gaxi_fifo_async, so every APB CDC task |
| elaboration `$error` | the APB stubs |
| part-select of a function call `f(a)[7:0]` | bf16 log2 -- legal SV, not Verilog-2005, and sv2v passes it THROUGH |

All of them ran once moved to the flatten flow. **So a direct-flow task that
errors is not a broken proof, it is a task on the wrong flow** -- convert it
rather than deleting it or marking it deferred.

Three corollaries worth keeping:

- **A documented deferral outlives its reason.** Five softmax proofs carried
  "Yosys does not support unpacked array ports" and listed, as option 2,
  "a wrapper that flattens the array ports into packed vectors". sv2v IS that
  wrapper and was already in the repo. The note was right when written and
  had simply never been retested. Re-test the stated blocker before believing
  a deferral; the yosys half was still true, the conclusion was not.
- **Flatten does not fix everything.** A clocked `$display` becomes a `$check`
  cell that `async2sync` refuses. Drop it in the sby script with
  `delete t:$print` rather than switching the model to `clk2fflogic` -- the
  message is a simulation aid, not part of the design.
- **Part-selecting a function call is a portability bug, not a tool bug.**
  Hoist it into an intermediate in the RTL; several synthesis tools refuse the
  form too.

## A proof nobody runs is a proof nobody notices breaking (2026-09-11)

`make formal` ran common, cdc, stream and rapids. There was no `formal-amba`
target and no `formal/amba/Makefile`, so **sixty AMBA task directories had no
entry point at all**, and `formal/common/Makefile` hardcoded 34 modules while
222 task directories existed. Two consequences, both invisible:

- Twelve of twenty AMBA flat files had drifted from their RTL. One was proving
  against a **synchronous** reset where the module is asynchronous.
- Two monitor proofs could not elaborate at all, and had never been able to.

The fix is not a longer list. **Discover the task set from the tree**
(`$(wildcard */*.sby)`); a list that must be hand-edited goes stale the first
time someone forgets, and a missing entry looks exactly like a passing run.
Check a tracker's claims against a measured sweep before believing them -- see
[[escape-analysis]] on integration status being measured, never inferred.

## A proof's cost flips the day it starts passing (2026-09-13)

`axi_master_rd_splitter` prove FAILED in under a second, at step 4, for as
long as the AXI A3.3.1 bug was in it. With the bug fixed the same task takes
103 minutes (6175 s) to exhaust its 25 steps. Nothing got slower: the solver
went from exhibiting ONE counterexample to proving absence over the whole
depth. Budget for the PASSING cost, not the failing one -- a CI budget tuned
while a proof is red will start "timing out" the day it goes green.

## Constrain to the documented range; file the hazard (2026-09-13)

When a counterexample lands OUTSIDE the design's stated operating range,
constrain the environment and FILE it -- never weaken the property to get
past it. Proving that splitter first produced a one-beat read at 0xFFFC,
where `axi_split_combi`'s `(addr | mask) + 1` overflows the address space, so
`transaction_end_addr >= next_boundary_addr` compares against 0 and splits a
transaction that crosses nothing. The module documents "Assumption 4: No
Address Wraparound", so the harness assumes the next boundary exists and the
overflow became TASK-095.

The first attempt at that constraint was wrong in an instructive way: it
assumed the TRANSACTION does not wrap. The solver walked straight back in,
because the BOUNDARY arithmetic overflows first -- 0xFFFC + 4 ends exactly at
the top of the space without wrapping. Constrain the expression that actually
overflows, not the one you had in mind.

## Internal visibility is not always available (2026-09-14)

The rule above says properties live in the RTL under `` `ifdef FORMAL ``. That
is `rtl/**` practice. It does **not** apply to `projects/components/**`, where
[[no-assertions-in-rtl]] is an owner standing decision and `c67e9c31a` removed
in-module SVA from seven RLB blocks. There, properties go in the external
`formal_<block>.sv` binding -- and for a **PeakRDL-backed block** that binding
can only see PORTS. Four routes to internal signals were measured on
`rtc_config_regs` and all fail:

1. `dut.<sig>`, DUT read as sv2v-flattened Verilog + harness as SV:
   `ERROR: Failed to resolve identifier \dut.w_status_wr_event`.
2. the same with `hierarchy` / `proc` / `flatten` before `prep`: identical.
3. the same with harness and DUT sv2v'd into ONE file: identical.
4. `bind`: yosys drops the checker (`Removing unused module
   $abstract\<checker>`) and the proof passes with NO property cells. sv2v
   cannot parse `bind` at all (`unexpected token 'bind'`).

Reading the RTL as SystemVerilog instead -- how `formal/apbx_xbar` legitimately
reaches `dut.s0_arb_grant` -- is closed off by the generated package:
`rtc_regs_pkg.sv:10: ERROR: Only PACKED supported at this time`. That is why
every sv2v-flow area (rapids, stream, converters) asserts on ports only.

**So scope the contract to what ports can see, and leave the rest as CHECK BY
INSPECTION** -- which the rule explicitly calls the accepted state, not a gap
to paper over.

## A sequential DUT needs a reset sequence, or anyinit invents counterexamples (2026-09-14)

The setundef bullet above covers undriven INPUTS. Uninitialised FLOPS are a
separate trap and they bite the moment a harness moves from combinational to
sequential RTL.

A harness whose `clk`/`rst_n` are plain inputs of the formal top never applies
reset. yosys then starts every flop in the DUT at an `anyinit` value, the
solver picks the worst one, and properties fail against RTL that is correct.

*Case: `formal_ioapic_deliv_merge`. `ap_ready_onehot0` -- at most one source
ready at a time -- FAILED at step 1. The RTL was right: `arbiter_round_robin`
computes `w_next_grant = '0` then sets one bit, and clears grant on reset, so
grant is one-hot-or-zero in operation. The trace named the real cause in
plain sight: `u_arb/_witness_/anyinit_procdff_428…463`, i.e. the arbiter's
grant/grant_valid/grant_id flops free at step 0 with no reset ever applied.
The sibling `formal_ioapic_lowest_pri_arb` needed none of this because that
module is combinational and holds no state -- which is exactly why the trap
is easy to walk into on the second proof in an area.*

The fix is the standard idiom already used by `formal_drain_ctrl_beats.sv` and
`formal_axi_write_engine.sv` -- hold reset for the first two cycles:

    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk)
        if (f_past_valid >= 2) assume (rst_n);

**Read `_witness_/anyinit_*` in a cex as "no reset", not as a design bug.** Note
the shape of the mistake: the property was correct, and the counterexample was
genuine in the MODEL but unreachable in the hardware -- the model permitted a
start state the design cannot occupy. That is the same judgement as "Constrain
to the documented range; file the hazard" below -- constrain the environment,
never weaken the property. The second
failure in that same proof was the other half of it: in arbiter ACK mode a
grant is HELD, so a source withdrawing `valid` mid-grant leaves the merged
channel valid for a source no longer asking. No conforming producer does that
(`ioapic_core` drives `irq_out_valid` from a registered stage that empties only
on `irq_out_valid && irq_out_ready`), so it too is an assumption, and
`ap_src_requesting` stayed exactly as written.

## `design.log` cell counts are NOT a vacuity test

Route 4 above passed, and three separate readings of `design.log` gave three
wrong answers about whether it proved anything:
- `Removing unused module $abstract\<checker>` looked like the checker being
  dropped. The `$abstract` form is also printed for modules yosys later
  resolves normally.
- `PASS 0 0` in `status` looked like "zero properties". The second field is
  ELAPSED SECONDS -- `PASS 0 11854` pairs with "Elapsed process time (11854)".
- `Checking assertions in step N` looked like proof of life. sby prints it per
  BMC step **whether or not any assertions exist**.

What actually discriminates:
- **grep the property NAMES in `model/design_smt2.smt2`** -- the SMT MODEL,
  not `design_smt2.log`, which contains none of them. Measured 2026-09-14:
  the .smt2 holds all six `ap_*` / `cp_*` names while the .log holds zero,
  so grepping the log is itself a false discriminator of exactly the kind
  this section warns about;
- **`Reached cover statement ... at <file>:<line>`** in the cover log;
- and above all **MUTATE**. Route 4's proof passed both mutations; the
  port-only rewrite failed the one that matters and passed the documented
  control. Nothing short of the mutation settled it.

## An sby task with no Makefile target is invisible (2026-09-16)

`bin/formal_status.py` drives each task through its Makefile, so a task listed
in the `.sby` but missing from the Makefile is never run and reports NORESULT
-- not FAIL, not PASS, just absent from the measured table.

Caught the same day it was introduced: extending
`formal/cdc/cdc_4_phase_handshake` from 2 sby tasks to 6 without adding the
four matching make targets turned a previously-measured PASS into NORESULT,
and would have hidden the CDC-002 data-loss finding entirely -- the failing
proof simply would not have been run. The measurement caught it because the
arithmetic did not add up: 28 mode-runs but only 24 results.

When you add an sby task, add its make target in the same edit (see
`formal/amba/wb4_slave` and `wb4_retry` for the shape), and put a
deliberately-red task LAST in `all` -- make stops at the first failure, so
anything after it never runs.
