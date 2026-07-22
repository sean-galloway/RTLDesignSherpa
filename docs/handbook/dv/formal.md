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
- "prove" here is BMC depth 25, not induction - claim accordingly.
- Formal at small N is blind to synthesis pathology
  ([[priority-logic-depth]]) - synthesis is its own gate.
Trackers: formal/FORMAL_TODO.md, formal/FORMAL_PRIORITY.md.
