# The riscv-formal Flow

## What it is

riscv-formal is the open-source RISC-V formal-verification framework:
per-instruction *specification models* written as Verilog (a BEQ model,
an LW model, ...), paired with checkers that relate a core's RVFI beats
to the model's expected behavior on every cycle, discharged by bounded
model checking. Where simulation shows the programs you thought of
behave, riscv-formal makes claims about *every* stimulus up to a proof
depth — including the perverse ones no test author would write.

## kestrel's setup

`formal/kestrel/riscv-formal/` holds a thin `rvfi_wrapper` around
`kestrel_core` in the shape riscv-formal's reference cores use
(picorv32's), a `checks.cfg`, and a Makefile driving genchecks and sby.
The wrapper is worth understanding because it is small:

- Memory inputs (`imem_rdata`, `dmem_rdata`) are free
  `rvformal_rand_reg` values — there is no memory array. The checkers
  relate the core's *reported* rvfi_mem channels and writeback to the
  ISA model, so random read data is exactly the right stimulus, and no
  imem-stability assumption is needed even across the two-cycle retry.
- The core lacks `rvfi_halt/rvfi_intr/rvfi_mode/rvfi_ixl` ports, so the
  wrapper generates them: `rvfi_halt = rvfi_valid & halt` (for a core
  with no trap handler, the Task-8 trap beat *is* the final retirement —
  precisely rvfi_halt semantics), `rvfi_intr = 0`, `rvfi_mode = M`,
  `rvfi_ixl = 32`. `RVFI_CONN` is not used.
- `RESET_ADDR` stays at the core default: a parameter is an
  elaboration constant and cannot be made symbolic without touching
  RTL; the checks are address-agnostic, so no proof is weakened.

## The checks and depths

genchecks generates 42 checks from `isa_rv32i.txt`: the 37 instruction
models plus five consistency checks — `reg` (register file integrity),
`pc_fwd`/`pc_bwd` (PC monotonicity both directions), `liveness`
(something eventually retires), and `unique` (no duplicate retirement
orders). This pinned genchecks emits no `mem`/`causal`/`ill`/`hang`/
`cover` checks; load/store semantics are covered by the instruction
models plus `reg`. Depths: instruction and consistency checks at 6 —
enough for reset plus a two-cycle cross-word access with headroom —
with liveness/unique at trigger 6, check 30 per the picorv32
configuration. Solver: z3 via smtbmc.

## The flow's three honest workarounds

None weakens a proof; all are recorded because the next rung inherits
the flow:

1. **sv2v pre-conversion.** This yosys (0.62+95) cannot parse the RTL's
   module-body `import kestrel_pkg::*;`, so the Makefile converts the
   RTL into plain Verilog before genchecks runs; the wrapper is still
   read as SystemVerilog.
2. **`const rand reg` workaround.** The same yosys rejects
   `const rand reg` (used by five consistency checkers), and this build
   has no `system` command to patch copies at run time. The Makefile
   therefore builds the checks directory as a symlink farm around a
   sed-patched *copy* of `rvfi_macros.vh` (`const rand reg` →
   `(* anyconst *) reg`, verified semantically identical); the vendor
   tree is untouched.
3. **genchecks' working-directory contract.** This pin's genchecks reads
   its config from the current directory and requires cwd to sit exactly
   two levels below the riscv-formal root; the Makefile runs it from
   `formal/kestrel/riscv-formal` accordingly.

## Results

The first clean build proved the flow end to end and returned 34/42
passing — the eight failures all counterexamples of one genuine core
bug, told in the next section. After the fix, a clean rebuild reports
**42/42 PASS** (z3/smtbmc), reproduced identically across three full
runs including one from `make clean`:

```bash
export PATH=/mnt/data/tools/oss-cad-suite/bin:/tmp/sv2v/sv2v-Linux:$PATH
make -C formal/kestrel/riscv-formal checks   # generate + run all 42 sby tasks
```

Per-check evidence lives in `checks/<check>/status` (PASS/FAIL with step
counts) plus logs and VCD counterexamples under `checks/<check>/`.

**Source:** task-9 report and fix round 1 (check list, wrapper notes,
flow deviations, depths, results); `formal/kestrel/riscv-formal/`
(formal_kestrel.sv, checks.cfg, Makefile)
