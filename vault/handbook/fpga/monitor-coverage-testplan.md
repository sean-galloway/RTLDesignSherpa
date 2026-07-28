---
title: Monitor coverage testplan
summary: 12-32 board sequences that hit every protocol/type/unit with near-concurrent multi-channel traffic, monbus busy but not flooded.
---

# Monitor coverage testplan (board)

Executable companion to [[monitor-board-coverage]] (the profile-tally design) and
[[uart-harness]] (the host transport). Target board: the 4-channel Genesys 2
coverage bitstream (`make bitstream` in flows-stream-monitor; `make program`).

**Goal.** Accumulate as many hits as possible on every legal
`(protocol, pkt_type, unit)` tuple, driving **multiple channels that match near
concurrently** so several agents emit at once -- enough to keep the monbus
**busy but not flooded** (send rate ~= drain rate, no trace-overflow). Split
across ~24 sequences (12-32) so no single run enables everything (the
congestion rule: never all packet classes on all agents at once).

## Unit roster (4-channel build)

| Unit / agent | Protocol | id | Emits |
|---|---|---|---|
| Descriptor engines | CORE | 16-19 | Completion (DESCRIPTOR_LOADED), Error (DESCRIPTOR_ENGINE) |
| Schedulers | CORE | 48-51 | Completion (DESC_START/DESC_COMPLETE/IRQ), Error (STREAM_EVENT_ERROR) |
| Desc-AXI monitor | AXI | 8 | Completion / Error / Timeout / Threshold / Perf / AddrMatch |
| RD datapath | AXI | 9 | same AXI classes (source reads) |
| WR datapath | AXI | 10 | same AXI classes (dest writes) |
| Slave-side monitors | AXI | 1, 2 | Completion / Error (reference; slave tally) |

Profile tally keys on `(agent, protocol, pkt_type, event_code)` -> a dense bin;
anything out of a unit's legal profile lands in **UNEXPECTED**.

## Harness knobs each sequence uses

- **Channels + near-concurrency:** program `CHx_KICK_ADDR` for the target
  channels, then one `KICK_GO` write with a multi-bit mask fires them within one
  cycle so their AR/AW/completions interleave (concurrent agent emission).
- **Monitor classes:** per-agent enables + `pkt_mask`/`addr_mask` (drop masks) --
  enable only the classes a sequence targets.
- **Profile legal set:** load the slice of legal tuples for the sequence over
  each tally's cfg AXIL slave (`0x100200 + idx*4`; clear at `0x100100`). Reprogram
  between sequences when the target set changes.
- **Latency knobs:** `RESP_DELAY` CSR (per-beat R/B hold) provokes
  Timeout/Threshold and shapes the emission rate.
- **Snapshot:** `FREEZE_TRACE` -> sweep dense bins + UNEXPECTED over the cfg
  slave -> assert -> `clear_stats`.

## Rate control: busy, not flooded

The monbus + tally sustains ~1 packet / 2 cycles; over-driving fills the write
FIFO and sets the sticky `trace_overflow` flag. Tune each sequence so aggregate
emission stays ~50-80% of drain:
- Start at 2 concurrent channels, scale to 4; hold transfers small (256 B-4 KB).
- Watch `STATUS.trace_overflow` (must stay 0) and the always-on bus-meter
  buckets; if overflow trips, drop a channel or add `RESP_DELAY` to spread
  emission. If the meters show the monbus mostly idle, add a channel or shrink
  `RESP_DELAY`.
- The "matched" rate is where every channel runs continuously, several agents
  emit each window, and overflow never trips -- that is the target for the
  concurrency sequences (S17-S22).

## Sequence structure

Each sequence: `clear_stats` -> program mon classes + profile slice ->
`RESP_DELAY` -> kick the channel mask -> wait idle -> `FREEZE_TRACE` -> sweep ->
assert its target tuples counted (> a threshold, not just present) and
`UNEXPECTED == 0`. Sequences are independent and re-run in order.

## The sequences (~24)

**Phase A -- CORE completion volume (schedulers + desc engines, per channel).**
- S1  ch0 only: assert `(CORE,48,Compl,DESC_COMPLETE)`, `(CORE,16,Compl,DESCRIPTOR_LOADED)` counted.
- S2  ch1 only: same for agents 49 / 17.
- S3  ch2 only: agents 50 / 18.
- S4  ch3 only: agents 51 / 19.  (S1-S4 confirm every CORE agent id fires.)

**Phase B -- AXI datapath completion + AddrMatch (rd 9 / wr 10 / desc-AXI 8).**
- S5  compl: enable datapath monitors, all 4 channels; assert `(AXI,9,Compl,*)`, `(AXI,10,Compl,*)`, `(AXI,8,Compl,*)`.
- S6  rd AddrMatch: DEBUG range match-all on rd; assert `(AXI,9,AddrMatch,RANGE_MATCH)` high count.
- S7  wr AddrMatch: same on wr -> `(AXI,10,AddrMatch,RANGE_MATCH)`.
- S8  desc-AXI AddrMatch on the descriptor-fetch reads -> `(AXI,8,AddrMatch,*)`.

**Phase C -- Error coverage.**
- S9  rd allowlist-miss (ERROR-flavor range excludes the DMA addr) -> `(AXI,9,Error,AXI_ERR_ADDR_RANGE)`.
- S10 wr allowlist-miss -> `(AXI,10,Error,AXI_ERR_ADDR_RANGE)`.
- S11 CORE descriptor error (host writes a malformed descriptor) -> `(CORE,16,Error,DESCRIPTOR_ENGINE)`, `(CORE,48,Error,STREAM_EVENT_ERROR)`.

**Phase D -- Timing classes (RESP_DELAY-driven).**
- S12 rd/wr Timeout: high `RESP_DELAY` + small timeout -> `(AXI,9/10,Timeout,*)`.
- S13 rd/wr Threshold (latency): moderate `RESP_DELAY` + low latency threshold -> `(AXI,9/10,Threshold,AXI_THRESH_LATENCY)`.
- S14 rd/wr Perf: perf class on -> `(AXI,9/10,Perf,*)`  (never with compl -- congestion).
- S15 PerfWin (0xD) via the perf-window RUN edge; S16 PerfHist (0xE) histogram emit.

**Phase E -- Near-concurrent multi-channel (the busy-not-flooded core).**
- S17 2 channels (mask 0x3) matching concurrently, rate-matched; assert both channels' CORE + datapath agents counted in one window, `trace_overflow==0`.
- S18 3 channels (0x7); S19 4 channels (0xF) -- scale concurrency, hold overflow at 0.
- S20 4 channels + AddrMatch on rd/wr: several agents (16-19, 48-51, 9, 10) all emit each window -> maximal per-window agent spread.
- S21 4 channels, mixed classes (compl + addrmatch + occasional error) at the matched rate -- the sustained "keep monbus busy" run; assert high counts across the roster.
- S22 rate-ceiling probe: push transfer size / drop RESP_DELAY until `trace_overflow` trips, then back off one step -- records the drain ceiling for this build.

**Phase F -- Slave-side + gates.**
- S23 slave-side reference: assert `(AXI,1,Compl,*)` and `(AXI,2,Compl,*)` in the slave tally (agents 1/2 don't collide with STREAM's 8-55).
- S24 all-units-hit gate + UNEXPECTED: after the campaign, sweep both tallies; every roster unit shows a nonzero bin and `UNEXPECTED == 0` on both. A nonzero UNEXPECTED means a real emission outside its profile -- capture the first-offender latch and reconcile the legal set vs the RTL.

## Coverage bookkeeping

Union of S1-S24 must cover every roster row x its legal packet types. Track it as
a `(protocol, agent, pkt_type)` checklist; a row still zero after S24 gets a
dedicated follow-up sequence (extending toward the 32 cap). Sim cross-check: the
same tuples decode through `TBClasses.monbus.parse` -- the tally counts are the
silicon twin of that matrix ([[coverage]]).
