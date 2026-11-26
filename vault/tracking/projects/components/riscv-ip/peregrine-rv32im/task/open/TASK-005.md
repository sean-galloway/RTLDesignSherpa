# TASK-005: bus error handling -- load/store access faults on AXI SLVERR / DECERR

**Priority:** P3
**Status:** open (filed 2026-11-25; owner: "add a task for the future for error handling"), not scheduled
**Owner:** TBD (filed from riscv-ip/peregrine-rv32im TASK-002)

## Why

PRD §3 and §4.3 planned load and store access faults on an AXI error
response. They were never built: `peregrine_uc_axi` ignores `rresp` /
`bresp`, the I$ ignores `rresp`, amber does not report an error on its CPU
port, and the core has no cause 5 / 7 path. The PRD was amended to the
RTL on 2026-11-25; this task is the future work.

## What

- Load access fault (cause 5) and store/AMO access fault (cause 7), with
  `mtval` = the faulting address, taken precisely at MEM like the other
  synchronous traps (§4.3).
- Sources: the uncached port (`rresp` / `bresp` of SLVERR or DECERR) and
  the D$. The D$ needs amber to return an error on its CPU response for a
  fill or write-back that failed: a cache-ip change, to be filed against
  cache-ip/amber-mesi-l1 when this task starts, with its own decision on
  what a failed write-back of a dirty line means.
- Decide whether an instruction access fault (cause 1) on an I$ fill error
  is in scope; PRD P6 left it out.
- RVFI reports the trap with its cause; the shadow CSR model and spike
  lockstep (which needs a way to see the same error) learn it.

## Done when

- A directed test drives error responses on each source and checks the
  trap, `mepc`, `mcause` and `mtval`; a mutant dropping each source is
  caught.
- PRD §3 and §4.3 are amended back to "built"; the HAS/MAS trap chapters
  describe it.
- peregrine FULL, amber FULL and the formal suites are green.
