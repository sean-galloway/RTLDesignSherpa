# TASK-003: axis_monitor_lite -- a stream monitor core in the lite discipline, and the AXIS monlite wrappers

**Priority:** P2
**Status:** CLOSED 2026-09-27 -- core validated on its own (formal + yosys), eight axis4/axis5 wrappers built and tested; the observer's adoption of the core is misc TASK-003
**Owner:** tooling/monitor-lite session (Claude)

## Why

There has never been an AXIS monitor in `rtl/amba/monitor`. The `_mon` family
and its `_monlite` twin cover AXI4/AXI5/AXI-Lite4/AXI-Lite5 only, because
`axi_monitor_base` and `axi_monitor_lite` are TRANSACTION trackers (command
handshake, per-ID outstanding table, latency and timeout from command to last
data or response). AXI4-Stream has no command phase, no response and no
outstanding-transaction notion, so there was nothing to wrap. What exists for
AXIS: the `axis4/axis5` master and slave wrappers with no monitor variant,
`axis_bus_meter` (perf counters, no packets), the monbus package's AXIS
protocol code and its Credit / Channel / Stream packet classes (designed,
never given an emitter in rtl/amba), and the one emitter that does exist --
the per-port tap inside `projects/components/utility-ip/misc/rtl/axis4_intf_observer.sv`,
written in the lite discipline when the AXIS observer was built, not
reusable.

## The core: `rtl/amba/monitor/axis_monitor_lite.sv`

One stream, tapped (never gated) at TVALID/TREADY/TLAST/TID/TDEST/TSTRB, the
same 128-bit `monitor_packet_t` + side-band timestamp on the same monbus
handshake as the lite, same UNIT/AGENT ids, same 4-deep unreset output queue
with drop-and-count, same frequency-invariant microsecond tick and cfg pins
(`cfg_freq_sel`, `cfg_timeout_cnt` in microseconds, per-class enables, a
packet-type drop mask, `clear` legal only while idle). Events, taken from the
observer's board-validated tap so the observer can move onto this core later
(one implementation):

| class | code | when | data[63:0] |
|---|---|---|---|
| Error | AXIS_ERR_VALID_TIMING | TVALID withdrawn before the handshake | {stall_cycles, packets} |
| Error | AXIS_ERR_STRB_INVALID | an accepted beat with TSTRB all zero (cfg_strb_check_enable) | {beats_now, packets} |
| Timeout | AXIS_TIMEOUT_HANDSHAKE | TVALID without TREADY for cfg_timeout_cnt us; once per stall | {stall_cycles, stall_age_us, cfg} |
| Timeout | AXIS_TIMEOUT_PACKET | inside a packet, no beat for cfg_timeout_cnt us; once per gap | {beats, gap_age_us, cfg} |
| Completion | AXIS_COMPL_STREAM_END | the TLAST beat | {tid, tdest, beats} |
| Credit | AXIS_CREDIT_BACKPRESSURE | stall of cfg_stall_threshold cycles; once per stall | {stall_cycles, cfg} |
| Channel | AXIS_CHAN_ID_CHANGE / DEST_CHANGE | TID/TDEST differs from the previous beat inside a packet | {old, new, beats_now} |
| Stream | AXIS_STREAM_START / PAUSE / RESUME | first beat of a packet; TVALID low inside a packet; TVALID back | {tid, tdest, packets} / {beats, packets} |

Priority when several fire in one cycle: Error > Timeout > Completion >
Credit > Channel > Stream; TWO events are queued per cycle (see below), the
rest and anything the queue cannot take are dropped and COUNTED, reported as Error/EVENT_DROPPED -- into an EMPTY queue
only (stricter than the lite: a report must never take the slot a live event
needs while the bus is congested; the first exact-packet run showed reports
filling the queue). No Threshold class: the package has no AXIS threshold enum
and the observer never had one; the packet-length case is not built. Status:
`busy`, `in_packet`, `packet_count`, `error_count`, `dropped_count`.

`AXIS_ERR_RESERVED_E` (8'hE) became `AXIS_ERR_EVENT_DROPPED` in
monitor_amba4_pkg, monitor_pkg's name table and TBClasses/monbus, mirroring
AXI_ERR_EVENT_DROPPED at the same value.

## The wrappers

`axis4_master_monlite`, `axis4_slave_monlite`, `axis5_master_monlite`,
`axis5_slave_monlite` and their `_cg` twins: the core wrapper's ports verbatim
plus the monitor section, tap on the master-side (m_axis) port, the lite
wrappers' cfg names. Tests in `val/amba/monitor-lite/` on the framework AXIS
BFMs (never hand-rolled; the one protocol violation, TVALID withdrawn, is
driven on pins by design because a compliant BFM cannot produce it -- the
observer test set that precedent). Doc page joins `axi_monitor_lite_wrappers.md`
as a second family table plus its own core page.

## Acceptance

- Lint clean, every event class covered by a test that asserts the packet's
  class, code AND payload, checker verdicts carry counts.
- The observer's tap can be replaced by the core with the same packet stream
  (a follow-on, misc lane, once the core lands).

## Core done 2026-09-27

- `rtl/amba/monitor/axis_monitor_lite.sv` + `rtl/amba/filelists/axis_monitor_lite.f`;
  Verilator -Wall clean inside the module.
- Test: `val/amba/monitor-lite/test_axis_monitor_lite.py` on the fixture
  `tb_axis_monitor_lite.sv` (the core between the framework AXIS master and
  slave BFMs, MonbusSlave on the bus) via
  `bin/TBClasses/amba/monitor_lite/axis_monitor_lite_tb.py`: eleven phases,
  every one asserting class, code AND payload plus "nothing else". Cells GATE 1
  / FUNC 6 / FULL 12; 12/12 at FULL from `make clean-all`.
- Mutation-checked: credit firing every stall cycle -> stall phase fails (250
  BACKPRESSURE for one stall); change detector against the packet's first
  beat -> channel phase fails (2 ID_CHANGE / 0 DEST_CHANGE). RTL restored and
  cmp-identical.
- Area regression after the package enum change: val/amba/monitor-lite
  run-all-gate from clean 100/100.
- Doc: `docs/markdown/rtl-amba/monitor/axis_monitor_lite.md`; rtl-amba index
  and `rtl/amba/CLAUDE.md` no longer say "there is no AXIS monbus monitor".
- Not done: synthesis numbers; the eight wrappers and their tests; the
  observer's tap onto this core (misc lane, after the wrappers).

## Validated on its own, then the wrappers (2026-09-27, later)

Sean: "Validate the code on its own. Then write the axis4/5 versions."

**Two events a cycle.** The wrapper runs exposed what the bare-core test had
worked around: on a stream, events coincide -- the beat that ends a bubble is a
RESUME and, with TLAST, a STREAM_END; the first beat after a pause may also
change TID. The one-per-cycle pick (the observer's) dropped and counted the
loser every time, so `dropped_count` reported ordinary traffic and the earlier
"a one-beat packet's START is implied" rule was a symptom of it. The queue now
takes TWO pushes a cycle (highest two of the eleven candidates by priority;
storage becomes flops rather than LUTRAM at this depth). START is emitted on
every packet again; the drop count means what it says. Mutation: forcing the
second push off fails the suite.

**Formal** (`formal/amba/axis_monitor_lite/`, sv2v-flattened like the AXI
lite): BMC depth 24 over free stream/monbus/cfg inputs -- monbus hold, AXIS
protocol and unit/agent fields on every packet, packet_count +1 on a TLAST
handshake and unchanged otherwise, in_packet tracking the TLAST run, clear
zeroing every counter, dropped_count only ever falling to zero, busy whenever a
packet is queued or open -- PASS; cover depth 40 reaches all seven classes
(Error, Timeout, Completion, Credit, Channel, Stream, EVENT_DROPPED).

**Area, standalone** (yosys generic `synth` on the sv2v flat file, NAND-2
equivalents via bin/yosys_to_nand_equiv.py, default parameters): the AXIS core
is ~45 k NAND2 / 539 flops against the AXI lite's ~91 k / 1,209 in the same
flow -- half the AXI lite. Before the second push it was ~32 k; the second
write port and its muxes are the difference. No Vivado numbers (no fixture
build was asked for).

**The eight wrappers** `axis{4,5}_{master,slave}_monlite[_cg]` (+ filelists),
emitted by a scratch generator that reads each endpoint's own header and passes
every parameter and port through by name; tap on the EXTERNAL port (m_axis_*
on a master, s_axis_* on a slave); `_cg` = the family's own gating logic
verbatim (AXIS4 user_valid/axi_valid, AXIS5 registered wakeup incl. twakeup)
plus the monitor's activity, upstream READY and monbus_valid masked by
!cg_gating. Verilator -Wall clean, all eight.

**Tests**: the core's exact-packet TB drives every wrapper end to end (env
names the BFM prefixes, the tap side and the skid depth). Two things the
topology taught: through a wrapper a phase must wait for the endpoint's skid to
drain before judging, or its events land in the next phase; and on a SLAVE
wrapper the tap is upstream of the skid, so a single beat never stalls there --
the stall phase fills the skid first, and a mid-packet stall then also (rightly)
reports one PACKET timeout. Core 12 + 8 x 9 = 84 cells, 84/84 at FULL from
clean. The TVALID-drop phase is skipped through a wrapper (a skid's output is
always compliant); the `_cg` wrappers add a gating phase.

**Handed on**: misc TASK-003 -- the observer instantiates the core. Not done:
Vivado numbers, board run.
