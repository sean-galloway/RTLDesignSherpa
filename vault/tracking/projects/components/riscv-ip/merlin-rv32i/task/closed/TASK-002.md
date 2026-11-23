# TASK-002: merlin follow-ups from the TASK-001 final review

**Priority:** P3
**Status:** CLOSED (2026-11-23)
**Owner:** Claude (owner, 2026-11-23: "do 1 please")

Filed 2026-11-01 from the merlin TASK-001 SDD final review (two deferred
minors the reviewer asked to be tracked, not silent):

1. `merlin_hazard.idex_rd_wen` is an intentionally unused input (the
   load-use stall keys only on `idex_is_load` + rd!=0). Either document
   the intent in the module header or remove the port.
2. `test_merlin_hazard.py` matrix gaps: no `rd_wen=0`-blocks-forwarding
   case and no port-B both-pending case (RTL is symmetric and rv32ui
   covers it; the unit test should still pin them).

Also in the same cleanup pass (ledger minors): load-use "distances 1/2/3"
vs brief "0/1/2" docstring terminology; `MERLIN_ROOT` export belongs in
`make/formal_flat.mk` beside `KESTREL_ROOT` (currently a documented
`override export` in formal/merlin/riscv-formal/Makefile); the csr_forward
test's csrrci/csrrsi comment nit.

## Done when

- The hazard port is documented or removed, the two unit-test cases exist
  and pass, the docstring/comment nits are fixed, and `MERLIN_ROOT` lives
  in `make/formal_flat.mk` (kestrel+merlin Makefiles both still work).

## Outcome (2026-11-23)

1. **The port is removed.** `merlin_hazard.idex_rd_wen` is gone from the
   module, `merlin_core` and `merlin_hazard_tb_top`. It could never change
   the stall: `idex_is_load` already carries the ID/EX valid bit, and every
   RV32I load writes rd. The module header says so.
2. **Four new unit cases** in `test_merlin_hazard.py`:
   - 5b: both producers pending on port B; EX/MEM wins.
   - 5c: `rd_wen=0` on both producers with matching addresses; the
     regfile is selected on both ports.
   - 5d: EX/MEM `rd_wen=0`, MEM/WB live on the same register; MEM/WB is
     selected on both ports.
   - Each case catches the bug it targets. Dropping `exmem_rd_wen` from
     port A's select failed 5c. Checking MEM/WB before EX/MEM on port B
     failed 5b, which the old matrix (priority on port A only) passed.
     The restored RTL passes.
3. **Distance wording.** "Distance" is the number of instructions between
   producer and consumer, as PRD section 5 and the csr_forward test
   already count it, so the instruction right after a load is distance 0.
   The load-use tests in `test_merlin_hazards.py` and
   `test_merlin_core_regression.py`, the load-to-branch messages, and
   `programs/README.md` now use 0/1/2. The `d1/d2/d3` variables are
   renamed `d0/d1/d2`.
4. **csr_forward comment.** The instruction at 0x04 is `csrrwi` (funct3
   101), not `csrrci` as the comment said.
5. **`MERLIN_ROOT`** is exported in `make/formal_flat.mk` beside
   `KESTREL_ROOT`; the `override export` in
   `formal/merlin/riscv-formal/Makefile` is gone.

**Verification.**
- merlin suite from clean (`make clean-all && make run-all-full-parallel`):
  60 passed.
- riscv-formal from clean (`make clean && make checks`): merlin 42/42 and
  kestrel 42/42, both on the shared export.
