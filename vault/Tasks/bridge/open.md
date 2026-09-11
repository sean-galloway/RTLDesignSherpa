<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# bridge — open

## BRIDGE-017 — Legacy backlog carried over from projects/components/bridge/TASKS.md
**Status:** open 2026-09-10 (created when the pre-migration file was folded in)
**Priority:** P3. Aspirational items from the 2025 task list that nobody has
asked for since; triage, do, or drop each with a reason.

The retired file's completed and superseded items are in the ledger at the
end of [closed](closed.md) and two are in [dropped](dropped.md). These were
still "Planned" and describe real engineering that has not happened:

- ~~**Performance characterization** (legacy TASK-005)~~ -- **done 2026-09-11.**
  `dv/tests/test_bridge_2x2_rw_perf.py` drives saturating 16-beat streams on
  `bridge_2x2_rw` (every BFM channel back-to-back) and measures over each
  phase's own window: reads 1.00 beat/cycle; one write stream 0.89-0.90 with
  ZERO cycles of the bridge holding WREADY low (the gap is the requester
  re-arming W between bursts); two masters on one slave port 1.00 total,
  shares 0.499/0.501; two parallel paths 1.78-1.80; loaded AW->B latency 23
  cycles empty, ~16k+7 with k bursts queued (the AW-ahead-of-W queue is about
  20 deep). Every figure has an asserted floor. HAS Tables 5.1a / 5.7a.
  Structural latency (2/2 propagation) was already measured by
  `test_bridge_2x2_rw_latency`. Not measured: width-converted and shim
  paths -- the HAS note on that stays.
- ~~**Synthesis and implementation guide** (TASK-010)~~ -- **done 2026-09-11.**
  `projects/components/bridge/fpga/` is a standard `fpga_flow.mk` build
  with no bitstream: `make synth BRIDGE=<fixture> PART=<part> CLK_NS=<ns>`
  takes any generated bridge out of context through synth/place/route on
  Vivado 2025.1, constrains it from its port list (one clock per `*aclk`,
  CDC ports asynchronous, resets false-pathed, 30% I/O budget) and writes
  utilization, timing, CDC and a `summary.csv` line; `bin/synth_sweep.sh`
  runs the reference set on the Nexys A7 and Genesys 2 parts, and
  `bin/summary_table.py` renders the HAS tables (HAS 6.4 flow, HAS 5.3
  numbers; the hand estimates that never reconciled are gone).
  **First run found the bridge's real critical path:** `bridge_cam` Mode 2
  computed a newcomer's ordering count with a serial max scan over 16
  entries hanging off the crossbar's arbitrated ARID -- 40 LUT levels,
  32 ns, WNS -22 ns at 10 ns on the Artix-7 -1, `bridge_2x2_rw` capped at
  31 MHz with every functional test green. The counts of one tag are always
  0..k-1, so the max is a popcount; the count-0 retire pick is one-hot.
  Restructured (`bridge_cam.sv`): same bridge meets 10 ns (+0.12 ns, 9
  levels, ~101 MHz), LUTs 5824 -> 4615. Handbook
  `design/priority-logic-depth.md` (second case), MAS 4.1.
- ~~**Async clock-domain crossing** (TASK-016)~~ -- **done 2026-09-11.** There
  was no `axi4_*_cdc` family (the note was stale); built one:
  `rtl/amba/axi4/axi4_cdc_{wr,rd}` (one `gaxi_fifo_async` per channel,
  `USE_JOHNSON` hoisted, `val/amba/test_axi4_cdc.py` at three clock ratios).
  `cdc = true` on an AXI4 slave port gives it `<slave>_aclk/_aresetn` on the
  bridge top and the crossing between its timing wrapper (aclk, with the
  monitor and the bridge-id tracking) and the port; the generated TB runs
  the port on `BRIDGE_CDC_PERIOD_NS`. Fixture `bridge_2x2_rw_cdc` (ddr on its
  own clock beside a same-clock sram); `test_bridge_2x2_rw_cdc_ratio` sweeps
  3/10/23 ns: both masters' streams complete and read back, the port's beats
  land on the slave clock, the rate follows the slower clock, the neighbour
  is unaffected. Limits (validator-enforced): slave ports, `protocol = "axi4"`
  -- AXI5 sideband and the shim protocols would each need a crossing of
  their own. HAS 4.5a / 6.8b.
- ~~**QoS with aging** (TASK-017)~~ -- **done 2026-09-11.** `[bridge]
  arbitration = "qos"` (+ `qos_aging_shift`, default 4): every slave arbiter
  computes an effective priority per requester -- AxQOS plus an 8-bit age
  counter shifted by `qos_aging_shift`, saturating at 15, cleared on grant --
  grants the maximum and round-robins among equals, lock-until-handshake
  unchanged. Fixture `bridge_2x2_rw_qos`; `test_bridge_2x2_rw_qos_arb`
  asserts per master: >= 75% share for the QoS-8 stream in both
  orientations, the QoS-0 stream's worst gap inside the aging bound (no
  starvation), and equal QoS splitting like round-robin, with the port
  saturated throughout. MAS 2.3, HAS 6.8a.
- ~~**Pipeline stages in the crossbar** (TASK-019)~~ -- **done 2026-09-11.**
  `[bridge] xbar_pipeline = true`: `CrossbarGenerator(pipeline=True)` drives
  the routing/mux logic into `xs_<slave>_axi_*` nets and
  `_generate_pipeline_stages()` joins them to the ports through 2-deep
  `gaxi_skid_buffer`s -- request stages (AW/W/AR, bridge id in the payload)
  and response stages (B/R, the adapter's `bid/rid_bridge_id` and route-open
  flag captured with the beat, the mux keyed on the staged id and valid).
  Both cones end at a register, both directions cut (the skid's ready is
  registered), full throughput. Fixture `bridge_2x2_rw_pipe` (twin of
  `bridge_2x2_rw`): `test_bridge_2x2_rw_pipe_latency` pins 3/3 propagation
  exactly against the baseline's 2/2, and `test_bridge_2x2_rw_perf` runs its
  four phases on both fixtures with the same floors. Off by default; MAS
  2.3 and HAS 6.8a / 5.7 note.

## BRIDGE-018 — A native-AXI5 fabric
**Status:** open 2026-09-11 (split out of BRIDGE-014 when its master-protocol
half closed)
**Priority:** P3. No feature anyone has asked for needs it.

The crossbar is AXI4-shaped inside, with the AXI5 sideband riding alongside
in the channel structs (BRIDGE-002 A5-2). That covers every AMBA5 feature
delivered so far -- interop sideband, native sideband, atomics of every
class, poison, the Lite and APB5 ports on both sides (BRIDGE-014). What it
cannot express is a feature whose semantics change the fabric's own rules:
read-data chunking (per-beat ordering inside a burst), MTE tags with their
own ordering, or anything that needs the crossbar to reason about AXI5
transaction attributes rather than carry them. If one of those becomes a
requirement, this is where it goes: the structs, the crossbar mux, both
adapters' tracking paths and the response mux all change together.

Not owed until a consumer appears. Related: [[BRIDGE-002]], [[BRIDGE-014]]
(both closed).
