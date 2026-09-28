# TASK-013: replace the hand-rolled protocol responders in the rapids TBs with framework BFMs

**Priority:** P2. Correctness of the checks is already in place (TASK-003);
this is the "always use BFMs" rule applied to the last three places that
still drive or observe a bus by hand.
**Status:** open 2026-09-27. Split out of TASK-003 when that closed, so the
residue is a tracked item rather than a paragraph in a closed record.

## What is still hand-rolled

| TB | Hand-rolled piece | Framework replacement |
|---|---|---|
| `dv/tbclasses/ctrlrd_engine_tb.py`, `ctrlwr_engine_tb.py` | AXI AR/R and AW/W/B responders | `create_axi4_slave_rd` / `_wr` + `MemoryModel`; blocked on the narrow-read lane gap in the slave read BFM (see the AXI4-slave-BFM narrow-read note in the reference memory) -- fix the BFM first or wrap it |
| `dv/tbclasses/rapids_beats_top_tb.py`, `rapids_core_beats_tb.py` | AXIS egress monitor and AXIL capture responder | `create_axis4_slave` monitor with a callback; AXIL slave BFM with `data_width=64` and `reset_bus()` (the monbus TB shows the pattern) |
| `dv/tbclasses/src_data_path_axis_test_beats_tb.py` | hand-rolled AXIS egress capture; end-to-end compare against `expected_data` not yet wired | AXIS slave BFM callback feeding the existing `_compare_memory`-style check |
| `dv/tbclasses/scheduler_group_beats_tb.py`, `scheduler_group_array_beats_tb.py` | hand-rolled descriptor AXI read responder and ctrlrd/ctrlwr responders (found by the 2026-09-27 survey; not in the original list) | `create_axi4_slave_rd` (256-bit, memory-backed) for `desc_*`, 32-bit read/write slaves for `ctrlrd_*`/`ctrlwr_*`, captures through AR/AW/W callbacks |

**Survey note (2026-09-27).** STREAM's TBs already sit on the framework
responders (descriptor engine, core, data paths) and their remaining direct
drives are level controls on the DUT's own scheduler-side ready inputs; the
hand-rolled responders were a rapids-only deviation. Four rapids tbclasses
are dead (`scheduler_group_tb`, `scheduler_group_array_tb`, `program_engine_tb`,
`src_datapath_beats_tb`: no runner imports them) and are out of scope here.

## Done when

Each TB above drives and observes its buses only through framework
components, the same checks pass at GATE/FUNC/FULL, and the review bundle
for the area reports no hand-rolled driver findings.
