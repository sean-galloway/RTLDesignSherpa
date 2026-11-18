<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->
# jet-prime delta 03: the single-miss path (TASK-001 step 5)

**Status:** landed 2026-11-17. The third place jet-prime's architecture
differs from jet's. jet's books ([HAS](../../../jet-mesi-l1/docs/jet_has/jet_has_index.md),
[MAS](../../../jet-mesi-l1/docs/jet_mas/jet_mas_index.md)) still describe
the cache; [delta 01](01_fill_engine.md) is the fill engine, [delta 02](02_pair_fabric.md)
the pair fabric. This chapter is about one miss on its own: what a
depth-1 miss costs, cycle by cycle, and the two places the cost was
jet-prime's rather than the memory's.

## Why

Steps 2-4 took jet-prime under HPDcache from depth 4 up on every miss
configuration, as a pair. The done criterion says every depth, and depth
1 was still over: `r64k_we64` 15.39 cycles per transaction against
HPDcache's 13.73, `r64k_we255` 19.11 against 13.65, `r128k_we64` 21.02
against 18.83 (bin 3, injector 1 idle). At depth 1 nothing overlaps, so
cycles per transaction is latency plus one, and the sweep's latency
histograms split it: on `r64k_we64` the hits sit at 3 cycles, three
quarters of the misses in [16, 32) and a quarter in [32, 64) with a
maximum of 33; on `r64k_we255` -- every transaction a write, every victim
dirty -- 96 % of the misses sit in [32, 64). HPDcache's misses all sit in
[16, 32) with a maximum of 24. So two costs: a dirty-victim miss ten
cycles over a clean one, and a clean one two or three cycles over
HPDcache's.

## The anatomy, measured

The pair-rig gate cell at the default geometry with a waveform dump
(`WAVES=1`), cache 0, the depth-1 transactions of the directed scenarios
(request handshake to response handshake, no other request outstanding).
The step-4 RTL; the memory is the rig's `sdpram_slave_axi4_axi4`, four
cycles from AR to the first R beat, eight beats per line.

| cycle | clean read miss (23) | dirty-victim miss (33) |
|---|---|---|
| +0 | lookup capture | lookup capture |
| +1 | classify: alloc, launch presented, engine accepts | classify: alloc with a dirty victim, launch presented, **held** |
| +2 | engine AR register -> transport; fabric pulse and grant | capture opens: 8 port-B reads (+3..+10), the sync read's last word at +10 |
| +3 | transport AR out; fabric takes it; AC to the peer accepted | |
| +4 | fabric memory AR | |
| +6 | peer CR (idle peer: no data) | |
| +8..+15 | memory R beats, through the fabric and the transport in the same cycle | +11 engine accepts the launch, drain starts; +12..+14 as the clean miss +2..+4 |
| +9..+16 | beats at the engine (transport skid: +1) | +18..+25 memory R beats (the write-back's AW/W interleave on the memory port) |
| +10..+17 | beats presented to the array (staging queue: +1); +17 the last beat and `fill_done` | +20..+27 |
| +18 | commit snapshot (done queue head) | +28 |
| +19, +20 | `C_MERGE`: the read slot's address, then its word (sync read) and the done check | +29, +30 |
| +21 | `C_INSTALL` (tag write) | +31 |
| +22 | `C_DEPOSIT` (response into the sequencer) | +32 |
| +23 | response handshake | +33 |

Two things stand out. The dirty-victim miss is the clean miss plus the
whole capture: the launch waited for `cap_busy_o` to fall, so the
memory's round trip started ten cycles late on a miss whose data could
not have landed before the capture ended anyway (first beat at the array
+10 after the alloc; the capture's last read at +10). And the tail from
the last beat to the response was six cycles, of which three were the
commit's own bookkeeping: a snapshot cycle, a done-check cycle after the
last merge slot, and a deposit cycle after the install.

## What changed

### The launch goes out in the alloc cycle; the engine holds the beats

The MAS ch02/01 contract -- an entry's beats never land before its
victim is captured -- was enforced at the launch (delta 01's argument).
It is now enforced where the hazard is: `jet_prime_control` exports the
capture's `(set, way)` with `cap_busy_o` (`cap_set_o`, `cap_way_o`), and
`jet_prime_fill` holds a beat for that way at its staging-queue head
(`cap_hold_i`, `cap_set_i`, `cap_way_i`) until the capture completes.
The plane's launch gate (`cap_busy` low AND not a dirty-victim alloc
cycle) is gone; the launch is presented and accepted in the alloc cycle,
and the fabric's grant, the AC and the memory AR follow as for a clean
miss. The hold is head-of-line by design: a held beat holds the beats
queued behind it (any slot) for the rest of the capture, which is bounded
(FILL_BEATS port-B reads plus a snoop's CD stream pause), and on the rig
the first memory beat arrives about as the capture ends, so the hold
rarely bites. One capture streams at a time (the `wb_full_dirty_victim`
stall), and a clean-victim alloc during it claims a different `(set, way)`
by the claim-aware victim check, so the only beats a capture can hold are
its own entry's. The engine's completion follows the last consumed beat,
so a held burst completes after its capture and stays counted in flight.

### The commit tail: three cycles shorter

- **Snapshot in the done cycle.** A completion landing on an empty done
  queue with the commit idle snapshots the entry in the `fill_done` cycle
  itself (the queue is still pushed, for the bookkeeping, and popped at
  the retire). Not in a snoop grant cycle: with a non-empty queue
  `sn_safe_o` already excludes the grant (`w_any_done`); the bypass cycle
  excludes it explicitly, because a snoop's pend record must land before
  the snapshot that reads it. A merge in that cycle is held (the snapshot
  owns the merge-room probe), exactly as it was in the old snapshot cycle.
- **`C_MERGE` leaves as the last slot advances.** No separate done-check
  cycle.
- **The first deposit rides with the install.** `C_INSTALL` writes the
  tag and deposits merge slot 0 (the allocator) in the same cycle; with
  the sync data array the last read slot's word arrives in that cycle and
  is deposited straight off the port (`w_cpl_rdata`), not from the
  capture register it also lands in. `C_PEND` still follows the install;
  `C_DEPOSIT` handles slots 1.. when there are any; `C_RETIRE` closes.

A single-requester read miss now answers three cycles after its last
beat lands: `fill_done` and the snapshot, the merge read, the install
with the deposit; the response is on the port the cycle after. Expected
on the rig: a clean miss 23 -> 20, a dirty-victim miss 33 -> 20.

## What this changes for the checks

Three checks encoded the old timing and had to move with it, which is the
reason this chapter records them:

- the tops' simulation assertions "no fill accept during a capture / on a
  dirty-victim alloc cycle" became "no fill beat into the (set, way) a
  capture is reading" -- the contract at the hazard;
- the core TB's launch-time `cap_busy` check became the same beat-time
  check, and its armed-downgrade scenario waits for the retire before
  reading the slot state through the claim-aware helper (the response now
  arrives two cycles before the claim is freed);
- the control TB's commit watcher samples the cycle it starts in (the
  commit's first cycle can now be the one after `fill_done`), and the
  control formal environment accepts the launch unconditionally and holds
  beats by entry while `cap_busy_o` is high (`as_beat_not_captured`).

`jet_prime_fill` gained a `capture_hold` scenario (the hold, the
head-of-line wait behind it, the release order, a hold on another way
holding nothing); the pair-rig TB's fabric and lockstep layers needed no
change -- the fabric contract is untouched.

## Verification that carries this step

- Lint clean (`jet_prime_top` at the default and the 16x2 geometry).
- `test_jet_prime_fill`: the new `capture_hold` scenario at every level
  (the hold, the head-of-line wait behind it with the in-order responder,
  a fill to another way completing under the hold with the out-of-order
  one, the release, a hold on another way holding nothing), plus the
  existing grid.
- `test_jet_prime_control`: the commit watcher re-timed (first sample in
  its start cycle; deposits attributed by the commit's own tap) -- the
  FULL cell's four-deep merge lists are where the tag-reuse ambiguity
  showed; the engine stub already held beats while `cap_busy_o` was high.
- `test_jet_prime_core`: the capture contract checked at the beat every
  cycle (no fill beat into the (set, way) a capture is reading); the
  armed-downgrade scenario waits for the retire.
- The pair rig, unchanged: its fabric and lockstep layers score the
  same contracts (the memory AR after the AC, the per-line rule, the
  write-back content), and the per-direction request queue still holds.
- Gate 21/21; FULL 155/155 (9:17) from clean on the final RTL; ref-g2 gate 7/7.
- Control formal on the regenerated flat (two new ports; the environment
  accepts the launch unconditionally and holds beats by entry while
  `cap_busy_o` is high): covers PASS on the step-5 flat (23 of 23 control
  covers, 7 of 7 liveness-wrapper covers reached, 2026-11-18); the
  step-3 flat's liveness BMC (depth 192) PASS 2026-11-18 after 19 h; the
  step-5 safety prove (BMC depth 64, boolector) PASS 2026-11-18 after
  26:52 (the step-3 flat's took 11:57: the step-5 environment carries
  more state per step); the step-5 liveness prove (depth 192) still
  running at TASK-001's close, its verdict on the task's closed page. The
  fabric formal is step 4's; the fabric did not change.

## Board

`ref_jetpp_bringup` bin 4 (the step-5 pair): 18,126 LUT / 11,890 FF, WNS
+0.019 ns at 100 MHz under the 0.2 ns clock-uncertainty budget; the worst
path is the one bin 3 closed at +0.043 (the fill engine's staging-queue
read pointer into the data-array write address), so the spread is
placement and the budget carries it. Smoke init+smoke PASS, injector 0's
CRC the jet rig's. Two 55-run sweeps (`perf_sweep_jetpp_bin4_single_*`,
`perf_sweep_jetpp_bin4_dual_*`), err 0; every single-core CRC equals
bin 3's -- the data path is untouched, only the timing moved.

Cycles per transaction, injector 1 idle (s3 -> s5, HPDcache):

| config | d1 | d2 | d4 | d8 | d16 |
|---|---|---|---|---|---|
| `r64k_we64` | 15.39 -> **12.76** (13.73) | 9.55 -> 7.91 (9.79) | 7.05 -> 6.10 (8.22) | 5.99 -> 5.41 (7.67) | 5.78 -> 5.29 (7.64) |
| `r64k_we255` | 19.11 -> **13.17** (13.65) | 11.79 -> 9.31 (11.04) | 9.52 -> 8.65 (10.53) | 8.72 -> 8.53 (10.51) | 8.61 -> 8.51 (10.51) |
| `r128k_we64` | 21.02 -> **16.94** (18.83) | 12.13 -> 9.91 (13.11) | 9.10 -> 8.09 (11.37) | 8.32 -> 7.65 (10.91) | 8.11 -> 7.58 (10.90) |

Every depth-1 miss now sits in the [16, 32) latency bucket with a maximum
of 26 cycles (mean 20.2; HPDcache 20.5, maximum 24). With both injectors
active the pair runs at the single-core numbers (`r64k_we64` depth 1
12.78 / 12.74, depth 16 5.32 / 5.34). Hit floor 3, the 1.00 hit rows, MLP
10.6 at depth 16. jet-prime is under HPDcache at every depth on both
thrash configurations and at four times the cache: TASK-001's done
criterion. The depth-1 margin on the write-heavy row is 3.5 %, and what
remains is the resident hit -- jet's 3 cycles to HPDcache's 2, half the
transactions at depth 1 -- which is the lookup pipeline, not the miss
path; the resident rows at depths 1 and 2 stay a cycle per transaction
over for the same reason.

Cache alone, out of context at 10 ns (`ref/results/ooc/jetp5`): 6,010 LUT
/ 5,399 FF, 16 RAMB36, 1,998 LUTRAM, WNS +0.321 ns, 19 levels on the
staging-queue-to-array path; the step 2-4 cache was 6,047 / 5,394 at
+0.118. The beat hold and the shorter commit cost no area.
