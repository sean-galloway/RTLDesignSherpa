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
