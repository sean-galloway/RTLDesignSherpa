# TASK-015: regs/README.md: the stream_regs example names five ports the generated block does not have

**Priority:** P3
**Status:** open
**Owner:** TBD
**Filed:** 2026-09-29 (fanned out from tooling TASK-016)

`bin/check_doc_examples.py` (widened 2026-09-28 to beside-code README.md and
PRD.md) reports that the `stream_regs` instantiation example in
`projects/components/dmas/stream/regs/README.md` names ports the generated
block does not have: `ch0_ctrl_desc_addr`, `ch0_rd_burst`,
`global_ctrl_enable`, `paddr`, `pclk`.

Two likely causes, and the owner picks: the example predates a PeakRDL
regeneration (hwif field names and the APB port prefix moved), or it is a
hand-drawn sketch of the register block that was never meant to compile. A
stale example is fixed against `regs/generated/stream_regs.sv`; a sketch is
marked so on the page.

The finding is held by `BASELINE` in `bin/check_doc_examples.py` (7 as of
2026-09-29). **Drop it by one in the same commit as the fix** -- the script
prints "baseline can be lowered to N" when it can.

**Done when:**

- [ ] the example compiles against the generated module header, or is marked
      illustrative on the page
- [ ] `BASELINE` lowered by one
