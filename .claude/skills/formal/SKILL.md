---
name: formal
description: Formal verification flow - SymbiYosys via sv2v flatten, in-RTL ifdef FORMAL properties, mutation-checking every new assertion, harness vacuity traps. Use when writing properties, regenerating proofs, or after changing any module with a formal dir.
---

# Formal (SymbiYosys + sv2v)

Trackers: formal/FORMAL_TODO.md (infrastructure), formal/FORMAL_PRIORITY.md
(module priorities). Dep regeneration: tools/gen_formal_deps.py (regenerates
each formal dir's Makefile DEPS closure; run it after moving/renaming RTL).

Hard-won rules - each guards against a proof that PASSES while checking
nothing:
- sv2v silently DELETES immediate assertions unless the flatten step passes
  --exclude=Assert (the template does; never remove it). Check the flat .v
  actually contains your asserts.
- Put properties IN THE RTL under `ifdef FORMAL (sv2v defines FORMAL), not
  only in the harness - in-RTL properties see internal state and ride into
  every proof that includes the module.
- MUTATION-CHECK every new property: break the RTL, prove FAIL; restore,
  prove PASS. A property that never failed has never been tested.
- Harness vacuity traps (all real): a hierarchical reference to a
  non-existent net elaborates as an implicit FREE WIRE (property checks
  nothing - watch yosys warnings); an unconnected input models as constant-x;
  a harness MAX_TRANSACTIONS below the threshold under test makes the gated
  logic constant. Size the harness so the property can actually engage.
- "prove" mode in these dirs is BMC (depth 25), not induction - state that
  honestly in claims; deep-state bugs need bigger N or induction work.
- Formal at small N is structurally blind to synthesis pathologies (the
  242-level pick_oldest cone shipped under PASSing formal). Synthesis is a
  separate gate; run it before calling monitor-class RTL done.
