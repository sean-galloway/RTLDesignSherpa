# TASK-002: merlin follow-ups from the TASK-001 final review

**Priority:** P3
**Status:** open
**Owner:** TBD

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
