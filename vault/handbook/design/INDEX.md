---
title: Design notes
summary: RTL rules with the failures that taught them.
---

# Design

- [[what-is-a-plane]] - purpose-sliced functional layers; repo-unifying definition, membership and edge contract
- [[plane-boundary-registered-snapshots]] - a plane's internal state never crosses to another plane combinationally; registered snapshots + handshakes, decision flags computed where the decision lives (the -35 ns mem-ctrl build, 2026-10-19)
- [[decision-stage-reads-the-snapshot]] - a capture/classify lookup over one read port: the classify reads ONLY its registered snapshot (the dirty-replay makes it exact); the live port belongs to the capture landing in the advance cycle (jet v3 false hit from the occupant's set, 2026-11-07)
- [[holds-that-wait-on-the-fabric]] - a stage's "hold, not a stall" that waits on another agent is a wait on the fabric; no grant that agent needs may wait for the hold (jet v3 snoop-safe `~r_lk_valid` deadlock, pair-rig SEED 27994, 2026-11-07)
- [[dependent-hops-forward-the-pick]] - a pipelined scheduler classifies the dependent hop (column behind an ACT, ACT behind a PRE) against the command being picked, not the registered image; fire stage = live check + bounded holds; closing decisions belong to the policy (FR-FCFS 24-cycle row vs 13 floor, pumice TASK-044, 2026-10-23)
- [[per-bank-queues-admit-from-the-pool]] - a storage backend with per-bank queues admits on the pool condition only; any per-request term in push_ready is head-of-line blocking on the single AXI address channel (granite FIFO store cap 4: 23 percent off at eight threads, mixed deadlocked, one 8-beat burst = 8 same-bank entries; same-row-behind stored at push, 2026-10-23)
- [[one-buffer-per-hop]] - count the buffers a beat passes; one per plane boundary, the rest is LUTRAM nobody asked for (granite intake FIFOs + skid 4->2: cycle-identical, AXI plane 4 958 -> 3 906 cells); a decoder shared across independent channels couples their handshakes (shared address mapper: -23 percent on mixed, knob off), 2026-10-24
- [[reduction-tree-one-array-per-level]] - a reduction tree in ONE unpacked array is UNOPTFLAT to Verilator (lint-only stays silent; the sim build fails); one array per level in its own generate scope (gaxi_age_fifo_sync, 2026-10-25)
- [[variable-part-select-is-a-shifter]] - `bus[idx*W +: W]` on a flat vector is a barrel shifter over the whole bus; index an unpacked array instead (granite pick core: 1 538 of 5 407 cells in four such selects, cycle-identical fix; Vivado never showed it), 2026-10-24; second case 2026-11-07: a shift by a quasi-static CSR (`mc_addr_mapper` `bank_lsb`) becomes CW+1 constant slices under a one-hot select, equivalence proved in formal
- [[reset-and-clocking]] - reset macros, aresetn, clock conventions; the synchronizer's one output net is the recovery path of the whole domain (REPLICATED_OUT at tops)
- [[clock-gating-activity-terms]] - wake on peer VALIDs + pending output work, never peer READY; !gating mask; emission latency vs idle count
- [[cdc]] - crossing rules, gray pointers, handshakes
- [[valid-ready-contracts]] - stability rules; who may stall whom
- [[arbitrate-at-the-acceptor]] - a pick that feeds a queue ahead of a slow slave is not round-robin: share follows outstanding (fabric benchmark W3 40%)
- [[axi-burst-splitting]] - a burst cut into pieces restarts every later piece on the size grid; test the split with an UNALIGNED start (converters BUG-011)
- [[observers-do-not-drive]] - a parallel snoop must not gate the bus it taps
- [[new-monbus-protocol]] - a new PROTOCOL_* value must reach every consumer; the group cores filter by `filter_family()` (no hard drop since 2026-10-30), but decoders, tallies and configs still name values
- [[transaction-monitor-keys]] - a monitor's slot table is keyed by what the protocol lets the other side reuse; enumerate per-opcode debts from the spec's flow tables and review before writing the TB (CHI lite review found 7 leaks)
- [[frame-per-stream]] - packet-open state must be per stream wherever streams can interleave (CXS 2.5.2, AXIS TID)
  (in-path `*_mon` wrappers own ready by design; the rule is not about them)
- [[streaming-no-fsm]] - the pipeline pattern for datapaths
- [[block-boundary-dead-cycles]] - a framed datapath is pipelined only at `beats`/block; measure the SLOPE over two block counts, then account every excess cycle to a named mechanism (RS decoder, 2026-09-30)
- [[sram-and-memories]] - no-reset SRAMs, ram_style, array syntax
- [[library-arithmetic-consumers]] - check rows against the rtl/math block's own reference model; never split a fused op without a bit-equivalence run (math BUG-009)
- [[sizing-invariants]] - shared-resource math; one source of truth
- [[priority-logic-depth]] - serialized scans vs parallel selects
- [[static-loop-bounds]] - a loop bounded by a runtime value simulates and lints clean; Vivado refuses it (arbiter_matrix, 2026-10-18)
- [[select-on-function-call]] - `f(x)[0]` is not IEEE 1800: Verilator takes it silently, Vivado stops (axi_stress_mst, 2026-10-19)
- [[typed-ports-empty-module]] - `parameter type` ports: Verilator elaborates, Vivado 2025.1 synthesizes the module EMPTY with no message and its instances die as black boxes at opt_design (CVA6 tc_sram_wrapper, 2026-11-11); ports are plain vectors
- [[area-measure-by-hierarchy]] - after every synthesis pass, the hierarchy report and the worst path pick the next edit; five passes of axi_monitor_lite
- [[always-comb-block-fusion]] - a block is one scheduling node; mixing independent signals invents dependencies and fakes combinational loops
- [[credit-tokens-count-every-event]] - a token/credit counter ADDS every increment source in the cycle; an OR between two sources is an off-by-one that silently shifts the pairing forever (pumice BUG-033: a lost release token made every command leave only when the next one arrived)
- [[global-windows-revalidate-at-issue]] - a window that is not a per-resource property (tRRD, tFAW, tZQCS) must be re-checked in the gate that lets the command FIRE, not only where it is selected, and the gate OWNS the window from the fire cycle, not from the cycle its counter loads; four bugs in one block from this (pumice BUG-021, scoria BUG-001/002, pumice BUG-033)
- [[registered-status-outputs]] - a registered readiness/status flag must sample the NEXT state; sampling `r_state == X` publishes it a cycle late and every consumer then compensates (pumice ISSUE-018); the same next-state algebra registers a compare off the ROOT of a cone, cycle-exact (MC-011)
- [[resolve-the-select-at-the-load]] - a 2:1 mux of register sets by a registered decision is a LUT and a high-fanout net at the root of every consumer; load one register set with the decision at its D (mc_bank_pick, granite 100 MHz, MC-011)
- [[naming-and-style]] - module/signal conventions, headers
- [[signal-prefixes]] - r_ = flopped, w_ = combinational; what it promises and where it lies
- [[filelists]] - every module MUST have a .f and be registered; the two silent failures
- [[generated-rtl-discipline]] - fix the generator, not the generated .sv; regen-and-diff is the audit
- [[firmware-in-rtl]] - an image in a ROM is RTL: linker relaxation rewrote a jalr base to x0; unreachable policy found by mutation becomes a fault; perf A/Bs from the same start cycle
- [[regenerating-peakrdl-blocks]] - the .rdl regen mechanics: one invocation
  emits ONE regmap, so a DV-facing copy needs a second run; establish the
  invocation empirically, then add it to the check_rdl_regen manifest
- [[minimal-fsm]] - when an FSM is right, keep it minimal
- [[signal-contracts-and-kmaps]] - contracts workbooks; computed K-maps
- [[no-assertions-in-rtl]] - SVA belongs in formal/ bindings, never in a module; the guarded blocks the RLB arc reintroduced
