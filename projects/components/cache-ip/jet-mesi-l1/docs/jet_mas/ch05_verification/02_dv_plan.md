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

# DV Plan: the Ladder and the Scoreboard

**Status:** landed through Task 9 (the pair rig). The ladder mirrors
amber's (Pattern-B cocotb GATE/FUNC/FULL grids, per amber D9):

## The ladder

1. **Unit TBs:** `jet_mshr` (alloc/match/merge/retire + oversubscription),
   `jet_wb_buffer` (capture/drain/snarf/BRESP ordering), `jet_rsp_seq`
   (release order under random completion).
2. **`jet_control` core TB** — the big one. Reuses the `L1ControlTB`
   machinery (monitor taps, LRU model, gem5-derived `oracle_step`, snoop
   driver) with one structural change: the per-transaction slice checks
   (amber assumed a blocking pipeline — one transaction's events fall in
   one window) become an **event-stream scoreboard**: per-line coherence
   stays lockstep against the oracle, while timing checks become windowed
   properties (fill starts within W cycles of alloc, responses release in
   tag order, no response crosses an earlier tag).
3. **`jet_top` / pair-rig TBs** — amber's pair rig with two jets; the
   coherence stress suite re-run (`jet_pair_rig_tb`, Task 9: two
   `jet_top`s + `jet_pair_fabric` + one shared sdpram; the per-cache
   event-stream scoreboard instantiated per side plus the fabric layer
   and the onyx-D7 ACE compliance checkers, plus the
   `pair_ships_in_the_night` WB-snarf corner and, since jet BUG-004, the
   `DeepPipelinedMisses` scenario: eight back-to-back true misses per CPU
   before any response is awaited, the posture a blocking driver can never
   reach and the one that deadlocked the fabric's safe-peer wait). Since
   jet BUG-005, a `HotSetContention` phase after the uniform soak (both
   CPUs, 70 % writes, `WAYS + 3` tags in two sets: the WB buffers stay
   full and the peer's misses snoop lines sitting in them), a
   write-back order check at the cache ports, independent of the fabric,
   and the directed `WbSameLineOrder` scenario: a TB-only valve on the
   shared memory's AW channel (`tb_aw_hold` on the rig top) holds the
   write port on a third burst so a passed-on write-back and the new
   owner's write-back of the same line wait at once, the case random
   traffic on the serial fabric never reaches. Since jet BUG-006 (the
   write port's arbiter is `arbiter_round_robin` in grant/ACK mode), a
   rig-wide check that no write-back's burst starts with an absorption of
   its line already pending, and the directed `WbGrantVsAbsorbKick` scenario:
   a second valve on the memory's B channel (`tb_b_hold`) holds a burst in
   W_B and releases it in exactly the cycle a snoop kicks an absorption of
   a line whose write-back waits, so the arbiter's re-grant lands in the
   kick cycle (the case the write-back's `abs_kick_match` request term
   exists for).

## The BUG-001/002 lesson, applied at the start

Amber's soak bugs were TB-model bugs (eviction accounting retiring a live
line through a stale {tag, I} corpse slot), fixed 2026-10-27 in the shared
base classes. jet's scoreboard inherits those fixed classes directly. The
deeper lesson is procedural: jet's TB tracks per-slot state (the slot view
is what the DUT's arrays hold) and retires lines only through guarded
eviction — the corpse-slot pattern is designed in, not patched in.

## Levels

- GATE: lookup classify smoke + one miss under one hit.
- FUNC: directed merge/drain/snoop corners (the table in ch02/05), the
  oversubscription corner, the anti-livelock window.
- FULL: 10k-transaction randomized oracle-lockstep + idle snoop soak,
  per geometry × MSHR_COUNT × VICTIM_DEPTH (ch06/02).
