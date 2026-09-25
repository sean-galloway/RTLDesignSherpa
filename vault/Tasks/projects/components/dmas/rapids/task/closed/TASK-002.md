# TASK-002: RAPIDS-beats has NO contracts workbook at all
> **Was `RAPIDS-KMAP` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Status:** CLOSED 2026-09-25 — All six targets addressed; items 1, 2, 3, 4
and 5 are MAPPED in `docs/rapids_signal_contracts.xlsx` (7 sheets, 11 computed
maps), and item 6's premise was disproved and folded into item 3.  
**Unblocked:** the shared machinery was promoted to `bin/kmaps/` (TOOLING-KMAP item 5), so the generator builds on it rather than forking a third private copy.

Unlike stream and pumice, RAPIDS has **no**
`docs/gen_signal_contracts_kmaps.py` whatsoever. So this is not "finish the
maps" -- it is "there are none". Given RAPIDS-beats was resynced FROM stream
(prefetch, commit-gating, recoverable-timeout all ported across), it inherits
stream's decision shapes without inheriting even stream's partial workbook.

Start by copying the stream generator once [[TOOLING-KMAP]] has promoted the
machinery to `bin/` -- copying it BEFORE that just creates a third private copy
to keep in step.

Targets specific to RAPIDS, in priority order. The first three are OPEN
known_issues, which makes them the highest-value maps in the repo:

1. **Sink data path -- AXI timeout detection missing**
   (`known_issues/resolved/sink_data_path.md`). A map of the timeout
   qualification cone would make the missing term visible as an axis with no
   contributing expression.
2. **Sink SRAM control -- single-read limitation**
   (`known_issues/active/sink_sram_control.md`). A read-issue qualification map
   with an honest `depends_only_on` is the direct statement of what the
   limitation IS.
3. **`drain_size_gt1` source beat drop**
   (`known_issues/active/drain_size_gt1_source_beat_drop.md`). Beat-drop bugs
   are adjacency bugs; this is the archetypal K-map target.
4. **`scheduler_beats` issue qualification + commit gating.** Ported from
   stream's scheduler, so it carries the same latch/clear and timeout shapes --
   and RAPIDS has no equivalent of stream's macro coverage to catch a
   divergence.
5. **`snk_data_path_axis_beats` credit/RDA accounting.** RAPIDS' network side
   has no counterpart in stream, so nothing stream proved transfers here. This
   is the part of RAPIDS most exposed by having no workbook.
6. **`alloc_ctrl_beats` / `drain_ctrl_beats`.** Same space-accounting shapes as
   stream items 5, but independently drifted since the resync.

Note the naming-conflict history (`known_issues/scheduler_group_signal_naming_
conflicts.md`): RAPIDS has already been bitten by two signals whose names
implied a relationship they did not have. That is the same failure mode the
axis-equation requirement (criterion 3) exists to catch.

---

## Progress 2026-09-25

`projects/components/dmas/rapids/docs/gen_rapids_signal_contracts_kmaps.py`
now exists, built on the shared `bin/kmaps` package (no private copy of the
machinery). Run it with `source env_python && python3
docs/gen_rapids_signal_contracts_kmaps.py`; it writes
`rapids_signal_contracts.xlsx`.

**Item 3 (`drain_size_gt1` source beat drop) -- DONE.** Two sheets:
"Contracts src drain" (the drain interface, 5 rows) and "K-maps src drain"
(3 computed maps + a STREAM/RAPIDS comparison table). All six criteria
discharged:

1. *Computed cells* -- every grid evaluated from a python mirror; verified by
   reading the fills back out of the workbook (GREEN 17 / GREY 15 / DC 8,
   matching an independent recomputation).
2. *Defined ordering* -- Gray order, inherited from the shared writer.
3. *Axis equations + citations* -- 32 citations, all grep-verified at build
   time; a mutation test (a deliberately wrong line number) confirmed the gate
   actually fails rather than passing blind.
4. *Sufficiency argument* -- stated per map in `check`.
5. *Don't-cares marked X with citation* -- 8 unreachable cells in map 1, from
   two `relations=` predicates; a mutation test (a deliberately vacuous
   predicate) confirmed the invariant checker rejects it.
6. *Derived implicants vs RTL verdict* -- `rtl_sop=` on all three maps.

**The map found the bug.** Map 1 carries `fifo_ge_size` as an axis that does
not appear in the RTL expression at all -- the missing-term shape this task
predicted would be useful. Its single green cell at `fifo_ge_size=0` is the
defect: the grant is qualified on an availability view that double-counts beats
held in the latency bridge. Mechanism, citations, git archaeology and a
candidate one-line fix are now in
`known_issues/active/drain_size_gt1_source_beat_drop.md`. It turns out to be a
STREAM defect RAPIDS inherited in 2026-01 and STREAM fixed in 2026-07
(`e8908eebf`) without a back-port.

Also answered while here: **item 3's open question about the SINK path.**
`snk_sram_controller_unit_beats.sv:229` is the identical unfixed line, so the
sink shares the defect. That overlaps item 5's territory.

### Remaining

- **Items 1-2 CONFIRMED 2026-09-25 -- and my earlier note here was wrong.**
  I recorded that "the cited signals no longer exist" and that both needed
  re-scoping. Only their ANCHORS were stale (they named retired pre-beats
  files); both claims are true in the beats RTL. Re-filed with mechanisms.

  **Item 1 is broader than filed, and half of it is a live RAPIDS-only
  defect.** Two distinct gaps:
  - *No AXI transaction timeout in the engine* -- **BY DESIGN, not a gap.**
    Owner's decision 2026-09-25: "the monitor code takes care of timeouts."
    Detection lives in `rtl/amba/monitor/axi_monitor_timer.sv` and
    `axi_monitor_reporter_timeout.sv` (gated by `cfg_timeout_enable`), and
    RAPIDS instantiates a monitor at `scheduler_group_array_beats.sv:841` with
    `USE_AXI_MONITORS` defaulting to 1. An earlier note of mine filed this as
    an open defect; that is retracted.
  - *Bad-B-response detection exists and is discarded.* The engine already
    flags `m_axi_bresp != 2'b00` per channel, sticky (`:951`/`:955`), and
    exports it (`:144`, `assign sched_wr_error = r_wr_error;` at `:964`). On
    the sink it dies three times: `snk_data_path_beats.sv:269` connects it to
    `()`; no sink macro declares an error output, so it cannot propagate; and
    `rapids_snk_beats.sv:680` ties the scheduler input off with
    `assign sched_wr_error = '0;  // TODO: Add when write engine supports
    error reporting` -- **a TODO whose stated reason is false.**

    Consequence: `scheduler_beats.sv:978` includes `sched_wr_error` in
    `w_hard_error` and `:944` latches it sticky, so both terms are provably
    dead on the sink -- a SLVERR/DECERR can never drive `CH_ERROR` (`:380`)
    and the transfer reports success. STREAM does not have this: `stream_core
    .sv:669/1047/1409` wires it with no tie-off and surfaces it as
    `obs_flags[11]` (`:2130`). The RAPIDS *source* path is also correct
    (`src_data_path_beats.sv:79/:203`). Sink-only.

  **Item 2 is structural, not a missing feature.** `snk_sram_controller_beats
  .sv:143-160` has one `drain_read` bit and one `drain_id` index feeding a
  one-hot decode and a single data mux, so exactly one channel drains per
  cycle by construction. The fill side is the same shape (`:122-141`). That is
  why a keyword search for "single read" finds nothing -- there is no logic to
  find, only an interface. Low priority stands, per the original entry's own
  assessment.

  **Both are now MAPPED** (2026-09-25), in sheets "Contracts snk errors" and
  "K-maps snk errors": three maps plus a stage-by-stage table of where the
  sink's write error is lost.

  Map 1 (`w_hard_error` on the sink instance) is the one to read, and it
  inverts the usual reading of a K-map: **28 of its 32 cells are X**, not
  because those states are physically impossible -- the normal reason for a
  don't-care -- but because the instantiation ties inputs to constants. Two of
  those tie-offs are legitimate (`sched_rd_error` at `rapids_snk_beats.sv:513`;
  the sink has no AXI read engine) and two are the defect (`sched_wr_error` via
  the `:680` TODO, and `r_write_error_sticky` which latches only from it).
  They are carried as SEPARATE axes with separate `relations=` justifications
  precisely so legitimate and defective tie-offs are not blurred together. Of
  the 4 surviving cells, 3 are green, and the whole reachable surface is
  spanned by `descriptor_error` and `ctrl_err` alone -- so for a DATA
  descriptor `w_hard_error` reduces to `descriptor_error`.

  Map 2 (`CH_ERROR` entry) adds a consequence the prose had missed: a SLVERR
  arrives WITH a B response, so it counts as write progress and RESETS the
  timeout counter (`scheduler_beats.sv:920`). Errored traffic therefore looks
  healthy to the error path and the timeout path simultaneously.

  Map 3 states item 2 exactly: `drain_read` is one bit and `drain_id` one
  index, so at most one channel decodes per cycle -- concurrency is excluded
  by the port shape, not by any logic, which is why searching for a guard
  finds nothing.

  Item 1 gap 2 remains a one-signal wiring fix mirroring what the source path
  and STREAM already do; RTL unchanged, the owner's call.
- **Item 4 DONE 2026-09-25.** Sheet "K-maps sched commit": 3 maps + a
  STREAM/RAPIDS comparison. This is the FIRST item whose premise held up --
  `scheduler_beats.sv` really did diverge (1150 lines vs STREAM's 1390),
  unlike the alloc/drain FUBs which are byte-identical.

  **The divergence is one term.** STREAM exits `CH_XFER_DATA` on ISSUE
  (`w_transfer_complete = w_read_complete && w_write_issued`,
  `stream/.../scheduler.sv:909`) and defers the commit-wait to `CH_COMPLETE`
  for the LAST descriptor only (`:542`). RAPIDS exits on COMMIT
  (`w_transfer_complete = w_read_complete && w_write_complete`,
  `scheduler_beats.sv:776`) for EVERY descriptor, and its `CH_COMPLETE` has no
  commit gate at all. The two formal properties differ by exactly that word
  (`:1136` vs `stream:1376`). Map 1 shows it: `write_issued` is carried as an
  axis that does not appear in the RAPIDS expression.

  Costs RAPIDS chain throughput (cannot advance to the next descriptor until
  B responses land) and means a lost commit surfaces on ANY descriptor, not
  just the last. It is NOT a tolerance difference: under a lost commit neither
  design recovers -- both hang short of `CH_IDLE`. An earlier draft of the
  note in `known_issues/resolved/snk_scheduler_write_commit_stall.md` claimed
  STREAM was tolerant; that was wrong and has been retracted there, along with
  three drifted line citations in that issue (`:559`/`:601`/`:921` -> now
  `:733`/`:775`/`:1105`).

  **Second finding -- a timeout exposure, NOT filed as a bug.**
  `w_timeout_escalate = (cfg_sched_timeout_limit != 0) && (r_timeout_strikes
  >= cfg_sched_timeout_limit)` (`:970-971`) is independent of
  `cfg_sched_timeout_enable`. Strikes are cleared only by channel reset, by
  reaching `CH_IDLE`, or by real write progress (`:932-936`) -- never by the
  enable bit. So a channel holding banked strikes whose timeout is then
  disabled by software still escalates into sticky `CH_ERROR` (`:380`).
  Whether any host sequence clears enable mid-transfer is NOT established; the
  map states the exposure rather than asserting a defect.

  Also recorded: the `!w_write_complete` term in `sched_wr_valid` (`:860`) is
  logically redundant -- `beats_to_issue` already forces it, and every cell
  where it could decide the output is unreachable. Belt-and-braces, not live
  logic.
- **Item 5 DONE 2026-09-25, and RE-SCOPED: its title names machinery that
  does not exist.** There is no credit accounting and no RDA in RAPIDS RTL:
  word-boundary `RDA` occurrences are **0** (all 57 substring hits are
  `*_rdata` -- `m_axi_rdata`, `s_axil_rdata` and friends), and the only
  `credit` hits are a monbus threshold mask (`cfg_axis_credit_mask`) plus two
  `scheduler_beats.sv` comments that say "No credit management" and "Phase 2
  will add credit management". Same stale-premise failure as items 1-2.

  What the module actually decides is **AXIS ingress admission**, now mapped
  in sheets "Contracts snk ingress" and "K-maps snk ingress" (3 maps + a
  STREAM comparison table).

  **The map found a defect candidate.**
  `s_axis_tready = (fill_ready && (r_pending_alloc[ch] > 0)) || (fill_alloc_req)`
  (`snk_data_path_axis_beats.sv:204-205`). The second term carries no
  `fill_ready` conjunct, and `fill_ready` is the channel FIFO's own `wr_ready`
  (`snk_sram_controller_unit_beats.sv:184-185`) -- the only signal that says
  the beat can be stored. In the map's single green cell at `fill_ready=0`,
  an AXIS beat is accepted while the FIFO backpressures: the handshake
  completes, nothing stores the beat, and `:234` counts it as received.

  A second, related shape: `r_pending_alloc` is credited `fill_alloc_size` on
  the allocation REQUEST (`:225`), never on acceptance -- and acceptance
  (`alloc_ctrl_beats` `wr_ready`) is physically discarded at the
  instantiation (`snk_sram_controller_unit_beats.sv:126`), while the
  allocator advances its pointer only on `w_write && !r_wr_full`. So the
  datapath can credit itself space the allocator refused.

  **NOT YET ESTABLISHED -- deliberately not filed as a bug.** Reaching the
  defect cell needs `fill_ready=0` simultaneously with
  `fill_space_free >= cfg_alloc_size`, and those are two different counters
  (FIFO occupancy vs `alloc_ctrl` allocation accounting, released only when
  data leaves the latency bridge). The map states the question rather than
  assuming the answer; a directed test driving AXIS into a backpressured
  channel would settle it. Worth noting `ALLOC_SIZE` is an 8-bit rw field
  defaulting to `0x10`, so `1` is writable, and at 1 line `:222` leaves
  `r_pending_alloc` at 0 -- re-arming `fill_alloc_req` every cycle against a
  one-cycle-stale `fill_space_free` (`:236`).

  Contrast: STREAM has zero `r_pending_alloc`, and proves the contract RAPIDS
  leaves open -- `axi_rd_alloc_req |-> $past(m_axi_arvalid && m_axi_arready)`
  (`stream/rtl/fub/axi_read_engine.sv:580`, inside an `ifdef FORMAL` block).
- **Item 6 RE-SCOPED 2026-09-25: its premise is wrong.** The task says
  `alloc_ctrl_beats` / `drain_ctrl_beats` have "independently drifted since the
  resync". They have not. Diffed against their STREAM originals, both are
  byte-identical apart from two comment lines (the module name and the
  `// Subsystem:` tag):
  - `alloc_ctrl_beats.sv` vs `stream_alloc_ctrl.sv` -- 149 lines each, no
    functional difference.
  - `drain_ctrl_beats.sv` vs `stream_drain_ctrl.sv` -- identical, including
    the over-drain `$error`.

  The only line that actually drifted is `+ SCW'(bridge_occupancy)` in the
  *units* (`src_/snk_sram_controller_unit_beats.sv:229`), which item 3 already
  maps. A hypothesised mirror of that defect on the fill side was checked and
  REFUTED: `fill_space_free <= alloc_space_free` (`:236`) carries no bridge
  term, exactly as STREAM does at `sram_controller_unit.sv:314`.

  The alloc/drain event asymmetry -- space released per-beat
  (`alloc_ctrl.rd_valid = drain_valid && drain_ready`, `:129`) while data is
  reserved per-block (`drain_ctrl.rd_valid = drain_req`, `:157`) -- is real,
  but STREAM wires it the same way, so it is a design shape rather than a
  RAPIDS defect. Item 6 is therefore largely subsumed by item 3; what remains
  is contract documentation of the space-accounting shapes, not defect hunting.
