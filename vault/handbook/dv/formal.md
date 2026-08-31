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
