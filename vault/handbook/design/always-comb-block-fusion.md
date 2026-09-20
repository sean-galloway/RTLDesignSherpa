---
title: always_comb block fusion
summary: Verilator schedules a block as one node; mixing independent signals in one always_comb invents dependencies and fakes combinational loops.
---

# always_comb block fusion

**Verilator schedules an `always_comb` as a SINGLE node.** Every signal
written in the block inherits the dependencies of every signal read in it,
whether or not the RTL actually connects them. Put an independent signal in
the same block as a dependent one and the independent signal acquires
dependencies it does not have.

When that manufactured dependency closes a ring, Verilator reports
`UNOPTFLAT: Circular combinational logic` on RTL that has no loop.

Real case: `axi_monitor_trans_mgr.sv` had two blocks mixing alloc-dependent
with alloc-independent signals -

- the per-bank -> flat flattening wrote `addr_match_oh` and `addr_alloc_oh`
  in one block, so match inherited alloc's dependency on `addr_wants_alloc`;
- the per-bank reduction wrote `wb_addr_pend_any` and `wb_data_bypass_any`
  in one block, and the bypass derives from the addr-alloc mirror.

Either one closes `addr_hit_any -> addr_wants_alloc -> ... -> addr_hit_any`.
The design is acyclic: an allocation pick never feeds a match result. Fix was
to split both blocks on the alloc boundary - identical right-hand sides,
identical single driver per signal, purely a bracketing change ([[TASK-081]],
commit 0db59d75).

Rules:
- **Group an `always_comb` by dependency, not by convenience.** "All the
  per-bank flattening in one loop" reads tidily and is exactly the mistake.
  If some outputs of a block depend on a signal the others do not, split it.
- A `for` loop assigning ten different vectors is ten fused signals. The loop
  is not the unit; the block is.
- When you cut such a loop with a local mirror instead of a split, the mirror
  only cuts the path you routed around it. The same fusion reappears wherever
  else the two families share a block - which is exactly how this one came
  back at the bank level after being fixed once inside the CAM.
- Add a comment saying the split is load-bearing. Someone will otherwise
  merge the blocks back for tidiness.

## You will not see this from lint

It takes three things, and the first two find nothing:

| invocation | UNOPTFLAT |
|---|---|
| `verilator --lint-only -Wall` | 0 |
| `verilator -cc -Wall` (real model build) | 0 |
| `verilator -cc --public-flat-rw --trace` (what cocotb runs) | 4 |

`--lint-only` never runs the scheduling analysis. A plain `-cc` build
optimises across the loop and it vanishes. It takes `--public-flat-rw` -
which cocotb always passes, so every signal stays addressable and nothing is
flattened - to make the cycle real. See [[silent-fallbacks]] rule 9:
elaborating is necessary and not sufficient, the gate must run the flags the
consumer runs. `make build-check` in `projects/components/bridge/rtl` is the
gate that does.
