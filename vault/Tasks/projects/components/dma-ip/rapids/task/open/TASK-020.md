# TASK-020: AXI response-error injection in the byte-RAPIDS Genesys 2 harness

**Priority:** P2 -- the byte-perf report states that RRESP/BRESP error
handling is not exercised on silicon; it is the one gap left in the
byte-RAPIDS characterization.
**Status:** open, filed 2026-09-30 from rapids TASK-019.
**Owner:** TBD

The harness memory model always answers OKAY, and the harness has no hook to
change that, so the sink's B-response error path and the source's R-response
error path are covered only in the unit and macro sims.

## Done when

- [ ] a harness CSR (by name, through the generated regmap) selects an error
      response for a chosen transaction on R and on B
- [ ] directed sequences drive RRESP=SLVERR and BRESP=SLVERR and check the
      channel error status, the monbus error packet, and recovery through
      channel reset
- [ ] the sequences pass in the UART sim harness before any board run
- [ ] a new bitstream is built, proven on the board, and the byte perf
      report lists the error rows
