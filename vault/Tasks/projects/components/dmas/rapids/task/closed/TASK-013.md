# TASK-013: replace the hand-rolled protocol responders in the rapids TBs with framework BFMs

**Priority:** P2. Correctness of the checks is already in place (TASK-003);
this is the "always use BFMs" rule applied to the last three places that
still drive or observe a bus by hand.
**Status:** CLOSED 2026-09-27 (closing note at the end); was open 2026-09-27. Split out of TASK-003 when that closed, so the
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

## Closing note (2026-09-27)

Done in commit 9757373d9: all seven rapids TBs (the three in the table plus
ctrlwr and the two scheduler-group TBs the survey added) drive and observe
their buses only through framework components -- memory-backed AXI4 read and
write slaves, the AXIS slave with its callback, the AXI-Lite write slave the
monbus TB already used. SLVERR injection goes through the read slave's
`resp_override` hook and the write slave's out-of-range contract; retry-then-
match swaps the word in memory from the AR monitor callback. The clean full
rapids regression after the change: 744/744 (fub 48, fub_beats 425, macro 12,
macro_beats 249, top_beats 10).

Two things changed shape rather than being replaced one-for-one:

- `ctrlrd_engine_tb.test_channel_reset` is now a between-operations clear,
  like ctrlwr's. The old mid-read abort depended on the hand-rolled responder
  withdrawing an R beat, which no real slave can do (ctrlrd_engine only raises
  `r_ready` in READ_WAIT_DATA). Mid-read abort needs engine drain-on-reset,
  already tracked in `CONTROL_ENGINE_INTEGRATION.md`.
- **Coverage gap, deliberate and recorded.** The ctrlrd lane walk (addr[2]
  across a 64-bit bus, formerly in `test_back_to_back`) is gone: the shared
  slave read path returns narrow reads in the low word, so a correct lane
  select cannot be tested against it. Every ctrlrd test now strides addresses
  by the bus width. Restoring the coverage means lane-positioning narrow reads
  in `CocoTBFramework` `AXI4SlaveRead._generate_read_response` (RTLDesignSherpa-DV;
  installed as a non-editable wheel; ~80 consumers, the dwidth-converter tests
  issue narrow reads on purpose) -- an owner decision, not something to slip
  into a rapids commit.

The LLM review bundle was not rerun for this close; the criterion it would
check (no hand-rolled driver findings) is satisfied by inspection: the only
direct `.value =` writes left on protocol signals are reset-time zeroing before
the BFMs exist.
