---
title: Bus faults are taken where the response lands
summary: A load/store access fault is known only from the access's response, which a registered-read pipeline delivers a stage after the commit point. Take that one trap where the response lands, and hold the younger instruction uncommitted through the error response; an error response is never a completion. A write-back error has no instruction to blame, so it is an imprecise interrupt plus a sticky status (peregrine TASK-005, 2026-11-27).
---

# Bus faults are taken where the response lands

**A precise load or store access fault needs two things the ordinary
commit point does not give it: the error, which arrives with the response,
and a younger instruction that has not committed when it arrives.**

## The shape

peregrine commits traps at MEM. Its D side accepts a load or store in MEM
and answers it in WB (a 1-cycle D$ hit fits the stage-1 registered-read
contract), so a SLVERR / DECERR is known only with the instruction in WB,
one stage past the commit point. Holding every access in MEM until its
response would make the error MEM's, at the price of a cycle on every hit:
rejected, OKAY responses must keep their cycles.

What was built (riscv-ip/peregrine-rv32im TASK-005):

- **An error response is not a completion.** It holds the core one more
  cycle and does not free the port: the next access is accepted on an OKAY
  response only (`w_rsp_ok = valid & ~err`). The error is captured like a
  response that arrives under a hold, so the core sees it from a flop.
- **The trap is WB's.** WB retires the faulting instruction as a trap beat;
  everything MEM would commit (a CSR write, its own trap, `mret`, `fence.i`,
  the move to WB) is qualified by "no fault in WB", and MEM's instruction is
  killed with everything younger.
- **Keep the kill off the request cone.** The first build also gated MEM's
  data request by the fault in the core: one more LUT level on the core ->
  D$ accept path that limits the 75 MHz build, and `MUL_DSP=1` fell from
  +0.329 to +0.015 ns (OOC, 0.2 ns uncertainty in). The fault comes from a
  flop in the D-side wrapper, so the wrapper blocks MEM's request (and does
  not hold for it) in the fault cycle instead, beside its other flop terms.
  Measure the limiter before and after any term added to a commit gate.
- **Still precise.** Everything older retired; the instruction in MEM was
  held through the error response, so nothing younger committed. The one
  cost: the killed instruction had already trained the branch predictor,
  which is not architectural.

## A failed write-back has no instruction

A dirty line's write-back runs long after the store that dirtied it. There
is nothing to trap, so the cache drops the line, latches its address in a
sticky status (overflow bit for a second failure), and raises a platform
interrupt; software reads and clears it through a CSR. Owner decision,
2026-11-27 (amber TASK-008: `wb_err_*`; peregrine `mip.16`, `mbuserr`).

## How the precision check was found wanting

The mutant that let an error response free the port (`w_rsp_valid` for
`w_rsp_ok` in the accept) survived the first directed program: the
instruction behind every faulting load was an ALU op, so nothing was in
MEM to be accepted. It was caught once a store and a load sat directly
behind a faulting access, by the request count, which counts a faulting
access as one request ([[precise-trap-checks]]). Put an access directly
behind every kind of fault.

## Related

- [[precise-trap-checks]]: the request count and spike's unmapped-address
  faults.
- [[interrupts-must-not-discard-finished-work]]: the other rule that moves
  a trap boundary.
