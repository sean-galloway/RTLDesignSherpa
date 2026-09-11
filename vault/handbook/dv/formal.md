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
  formal directory is this smell ([[test-the-justification]]).
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
