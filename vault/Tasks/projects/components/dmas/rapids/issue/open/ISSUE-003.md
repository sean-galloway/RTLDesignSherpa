# ISSUE-003: RAPIDS monitor registers answer normally when the monitors are not built

**Status:** open 2026-09-24. Raised while fixing the same shape in STREAM
(stream TASK-002), which is where the parameter pattern was copied FROM.

`rapids_config_block.sv:45` has `parameter bit USE_MON_REGS = 1'b1`, and lines
304-318 strap every `cfg_desc_mon_*` output to zero when it is 0. That half is
correct and is what STREAM has now been given.

What RAPIDS does NOT do is gate the DECODE. `rapids_engine_regs.rdl:702`
instantiates `rapids_mon_regs MON @ 0x800` unconditionally, and the header of
`rapids_regs.rdl` states the intent plainly:

> A build-time parameter (USE_AXI_MONITORS in the config block, following
> STREAM) selects whether those registers are wired to monitor logic, so the
> monitor block can be dropped **without changing the base address map**.

So on a `USE_MON_REGS=0` build the MON registers still accept writes and read
back the written value while driving nothing.

**Why this is filed as an issue and not a bug.** Holding the address map stable
across monitor-present and monitor-absent builds is a deliberate, documented
choice, and it has real value: one host image addresses both. The cost is that
a host cannot tell "not built" from "built and set to zero" -- it arms a monitor
register, reads back exactly what it wrote, and concludes the monitor is
configured. Read-back success is normally the strongest evidence a host has that
configuration took, so the bus is affirmatively misleading rather than merely
silent. Which of those two properties RAPIDS should keep is the owner's call,
not mine.

**What STREAM did, for reference.** Kept the address map identical and added a
guard in front of the PeakRDL adapter that returns an error response for the
MON window when `USE_MON_REGS=0` (stream_top_ch8.sv). The map does not change;
only the answer does. The guard cannot live in the regblock because generated
PeakRDL ties `cpuif_wr_err` to `'0`, so a MON WRITE can never be reported as
failed from inside it -- that constraint applies to RAPIDS identically.

**If this is taken up, the shape is known:**
- RAPIDS' MON is at `+0x800` within a 4KB engine regfile, and there are TWO
  halves (`SRC @ 0x0000`, `SNK @ 0x1000`), so the decode term is not a single
  address bit as it was in STREAM. That is the one part that does not port
  across directly.
- The negative test to copy is
  `projects/components/dmas/stream/dv/tests/top/test_stream_top_mon_gate.py`:
  it asserts through the BFM packet's `pslverr` (the TB's `read_reg` discards
  it), proves the flag is observable before trusting it, and carries a non-MON
  positive control before and after so a wedged bus cannot read as a pass.

**Scope note.** Raised from STREAM work under the standing rule that RAPIDS is
in scope for STREAM ports; not acted on here because nothing asked for it and
the address-map tradeoff is a design decision.
