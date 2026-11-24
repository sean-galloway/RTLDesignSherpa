# TASK-005: pipelined hit path on amber's CPU port, for peregrine's MEM stage

**Priority:** P2
**Status:** closed (2026-11-24): 1-cycle hit landed; read hit 1/1, write hit 1/2
**Owner:** TBD (filed from riscv-ip/peregrine-rv32im PRD P13; the owner chose
option (b), "amber gains a pipelined hit path", on 2026-11-24)

## Why

peregrine (amber's target client, amber PRD v0.8) uses amber as its D$.
peregrine TASK-001 stage 6 measured amber's CPU-side hit timing on the pair
rig at the l1_pkg default geometry
(`projects/components/riscv-ip/peregrine-rv32im/dv/tests/test_peregrine_amber_latency.py`):

| Access | Response valid (cycles after accept) | Port ready again |
|---|---|---|
| Read or write hit | 4 | 3 |
| Write to an S line (CLEAN_UNIQUE upgrade) | 18 | 17 |
| Miss (bench memory) | 29 | 28 |

The hit path is IDLE (accept), LOOKUP (tag read), HIT_RD/HIT_WR, IDLE with
ready high, and then the response leaves the 2-deep staging FIFO
(`l1_cpu_frontend`, DECISION D-6). In a 5-stage core that waits in MEM,
that costs about 3 cycles per access over a 1-cycle hit: about 1.1 CPI at
0.36 accesses per instruction, more than the whole miss term in peregrine's
CPI model (PRD §4.8).

## What

A hit path that can take a new CPU request every cycle and return a hit's
response at a fixed, short latency, without changing the miss, snoop or
coherence behaviour.

- **Precedent in this repo:** jet-prime reached a 2-cycle hit floor with
  one hit per cycle from depth 4 (jet-prime PRD JP2/JP7;
  `jet-prime-mesi-l1/docs/delta/04_two_cycle_hit.md`). Read that before
  designing; amber stays blocking on a miss, so only the hit pipeline
  carries over.
- **Target latency: 1 cycle (owner, 2026-11-24, "1-cycle").** The
  response is valid in the cycle after the accept, so peregrine keeps a
  single MEM stage. 100 MHz on xc7a100t-1 must still close.
- A hit issued behind an older hit to the same line must see that hit's
  write (store then load, the commonest pair).

## Design (2026-11-24)

The classic synchronous-RAM split: the request's address goes to the
arrays in the accept cycle (c0), the data comes out of the RAM's output
register in c1.

- **Classify in the accept cycle.** The tag array is LUTRAM with an
  asynchronous read, so in c0 port A's set is the *arriving* request's set
  (`req_addr`, not `req_addr_q`), and the hit compare, way and state are
  computed in c0 and registered. The data array (block RAM, every way read
  at `a_addr`, `a_way` selects among the registered outputs) gets the
  arriving `{set, beat}` in c0. IDLE on an accept goes straight to
  HIT_RD / HIT_WR / MISS_VICTIM / MISS_FILL (upgrade). LOOKUP stays for the
  replay and the snoop-return paths, which classify from `req_addr_q` as
  today.
- **Respond in c1.** In HIT_RD `ctrl_rsp_valid` is the state and
  `ctrl_rsp_data` is the port-A word with `a_way = hit_way_q` (no
  `rsp_data_q` stage); HIT_WR answers with the request's own data as
  today. The FIFO stage in `l1_cpu_frontend` is bypassed when it is
  empty: a new parameter `RSP_BYPASS` (default 0, so jet and jet-prime are
  unchanged; amber's `l1_cpu_plane` sets 1). `cpu_rsp_rd_valid` = FIFO
  not empty or `ctrl_rsp_valid`; the data is the FIFO head when not empty,
  else the bypass; the response is written into the FIFO only if it is
  not taken that cycle.
- **Back-to-back reads.** `ctrl_req_ready` is high in IDLE (as today) and
  in HIT_RD when no snoop is requesting and the response FIFO is empty.
  Every term is a register, so ready never depends on the compare. A
  request accepted in HIT_RD is classified exactly as one in IDLE.
- **A write hit takes 2 cycles of occupancy.** HIT_WR writes the data and
  tag arrays at the end of c1; a read accepted in that cycle reads the same
  RAM at the same edge and would get the pre-write word, so ready stays low
  in HIT_WR. Response latency is still 1.
- **Unchanged:** the miss, upgrade, replay, drain, snoop, init and
  pending-fill paths; snoop priority over a CPU request in IDLE.
- **peregrine stage 4 consequence (recorded there).** To use the 1-cycle
  response without a MEM stall, peregrine sends loads from EX (address
  from the ALU) and gets the data in MEM. Stores go from MEM, because an
  older instruction in MEM can still trap. That puts peregrine's ALU in
  front of the LUTRAM read and the compare, which is the path to watch at
  100 MHz.

## Progress (2026-11-24)

As designed above, with two additions:

- **`HIT_RUN_MAX` (default 8).** A snoop is only granted in a snoop-safe
  state, and `CTRL_HIT_RD` is not one, so an unbroken read-hit stream would
  hold a snoop off forever. After `HIT_RUN_MAX` back-to-back accepts in
  `CTRL_HIT_RD`, ready drops for one cycle, `CTRL_IDLE` follows, and a
  waiting snoop wins there. The counter is a register, so ready stays
  registers-only. The design section's "no snoop requesting" term could not
  be used: `ctrl_snoop_req` is only raised in a snoop-safe state.
- **`l1_monlite` `tap_hit_again`.** The hit event fires on entry to a hit
  state, and a `CTRL_HIT_RD` entered from `CTRL_HIT_RD` is not an entry. A
  new tap (control's `hit_again_q`) makes it one. jet, jet-prime and the
  monlite harness tie it to 0 or to control. `l1_coh_core`'s
  `tap_hit_set` now takes the latched `req_set`, because in an accept cycle
  port A's set is the arriving request's.

RTL: `l1_control` (accept-cycle classify, `CTRL_HIT_RD` / `CTRL_HIT_WR`
respond in their own cycle, `rsp_valid_q` / `rsp_data_q` removed, run
counter); `l1_cpu_frontend` `RSP_BYPASS` (default 0, so jet and jet-prime are
unchanged; `l1_cpu_plane` sets 1); `l1_monlite` `tap_hit_again`;
`l1_coh_core` taps. The arrays are untouched.

Measured at the pins (peregrine `test_peregrine_amber_latency.py`, pair rig,
default geometry):

| Access | Before (latency / occupancy) | After |
|---|---|---|
| Read hit (S or M) | 4 / 3 | **1 / 1** |
| Write hit (M) | 4 / 3 | **1 / 2** |
| S-line write (upgrade) | 18 / 17 | 16 / 17 |
| Read miss / write miss | 29 / 28 | 27 / 27-28 |

Checks that encoded the old timing were moved to the new contract, not
loosened:

- `l1_control_tb` / `l1_snoop_resp_tb`: "LOOKUP entered" became "LOOKUP
  entered iff not an accept-cycle hit". A hit must now *skip* LOOKUP, unless
  its accept cycle also granted a snoop.
- `l1_core_tb`: "hit latency bounded 2..12" became the exact 1-cycle
  contract. The tally is checked after the MonBus drains: the last hit's
  packet is still in the observer queue when the response returns.
- `l1_cpu_frontend_tb`: "ready implies IDLE" became "IDLE or HIT_RD with the
  FIFO empty". The harness pairs real `l1_control` with the frontend, so it
  now sets `RSP_BYPASS = 1`. New `BackToBackHits` scenario: 19 read hits
  accepted one per cycle with the forced gap after every 9, each response
  one cycle after its accept with the right data, and a write hit then a
  read of the same word (2-cycle occupancy, the read returns the written
  bytes).
- `l1_monlite_tb`: the drop-count tap is sampled after the stalled phase
  settles, for the same last-packet reason.

Formal (`formal/amber/amber_control`): the flat was regenerated
(`HIT_RUN_MAX` pinned in the Makefile). Both wrappers now allow a request in
`CTRL_HIT_RD` in the previous request's response cycle. Added
`ap_hit_matches_tags` (every hit-state cycle, the tag model holds the latched
tag at the latched way in the latched valid state; owned for a write hit),
`ap_rsp_in_hit`, `ap_ready_states`, covers `cp_hit_b2b` and `cp_hit_wr_rsp`,
and on the liveness side `ap_hit_run_bounded` (a `CTRL_HIT_RD` run ends
within 9 cycles) with `cp_hit_run_max`. Cover (depth 80) PASS: 9 of 9 reached, including
`cp_hit_b2b`, `cp_hit_wr_rsp` and `cp_poisoned_lookup` (deepest step 39).
Liveness BMC (depth 126) PASS; its cover pass reached `cp_hit_run_max`
(step 28) and `cp_deep_txn` (step 49). The safety BMC (depth 48, about 4.5
h on the old flat) PASS at full depth: launched 2026-11-24 08:10,
done 09:05 (56 min wall), boolector, no trace.

Regressions (clean-all first, 0 reruns): common-ip FULL 255/255 (seed base
1269637946), amber-mesi-l1 FULL 121/121 (3842205565), jet-mesi-l1 gate 19/19
and jet-prime-mesi-l1 gate 21/21 (they share `l1_cpu_frontend` and
`l1_monlite`), peregrine `test_peregrine_amber_latency` pass. The first
common-ip FULL had 9 failures, all old-timing checks: the tally and
drop-tap checks that run before the last packet drains, and the b2b scenario
still on the FULL soak's random delays. Those checks are fixed above.

OOC (Genesys2 xc7k325t-2, `amber_top`, 10 ns): WNS +0.342 ns (the committed
`results/ooc/amber` row: +0.123), 3,579 LUT / 2,857 FF (3,709 / 2,944), 16
RAMB36, 1,169 LUTRAM. The worst path is the same family as before
(`u_control/state_q` into the monlite queue). The flow sets no I/O delays,
so the new CPU-side paths were measured separately with input and output
delay 0 on the CPU ports: worst input path slack +2.60 ns (7.46 ns, 12
levels), worst output path slack +2.27 ns (data BRAM output, way mux,
`cpu_rsp_rd_data`). The input path runs: request valid, accept, tag LUTRAM
read address, compare, `state_d`, then LOOKUP's beat-0 override of data
port A's address. That path is functionally false (no accept happens in
LOOKUP) but structurally present, and it is what is left for peregrine's
ALU in front of the cache. Breaking it would take LOOKUP's miss-gather
pre-read off `state_d`. That is open for peregrine stage 4.

## Done when

- The hit pipeline is in amber's HAS/MAS (CPU-plane contract and timing).
- peregrine's `test_peregrine_amber_latency.py` `EXPECT` table is updated to
  the new hit latency and occupancy and passes.
- amber's FULL grid stays green: the pair rig, the ACE top, the macros and
  parity.
- amber's OOC timing still closes at 100 MHz.

## Decided (were open when filed)

- The staging FIFO stays; the hit response bypasses it (`RSP_BYPASS`,
  default 0, so jet and jet-prime keep the old frontend behaviour).
- 1 cycle (owner, 2026-11-24).
- Both: `l1_control` (amber-only) classifies and responds; the shared
  `l1_cpu_frontend` gains the bypass and `l1_monlite` the `tap_hit_again`
  input (tied off in jet and jet-prime).

## Closed (2026-11-24)

Every "Done when" line holds: MAS ch02/ch03 carry the pipeline and timing,
the peregrine `EXPECT` table is (1,1)/(1,1)/(1,2) and passes, amber FULL
121/121, OOC WNS +0.342 ns at 10 ns. Open for peregrine stage 4: the
+2.60 ns input and +2.27 ns output budgets above.
