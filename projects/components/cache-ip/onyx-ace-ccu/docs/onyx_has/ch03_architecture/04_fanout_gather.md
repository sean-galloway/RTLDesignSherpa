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

# Snoop Fanout and Response Gather

**Status:** architecture recorded 2026-11-21 (D4 decided 2026-11-20, PRD v0.7; N3 and N4 remain proposed invariants that the design already honors).

## Fanout: one AC queue per peer

Each attached cache has an AC queue of slot indices in grant order. A grant pushes its slot onto the queue of every port except the requester. The queue head is presented on that cache's AC channel with the slot's line and the snoop type of its class (Table 3.1); up to SNOOP_INFLIGHT ACs may be accepted by a cache and not yet answered, so a fast responder streams ACs while a slow one is served one at a time. The AC payload is held stable until accepted.

## Gather: counters, not a window

Snoops carry no ID, and each cache answers its ACs in order (the ACE rule, and the family's CD-before-CR convention on top of it). Each cache therefore has a small in-flight queue of the slots whose ACs it accepted; its next CR pairs with the head of that queue, and its CD beats land in that slot's buffer at the beat index counted since the last CR.

Per slot, onyx counts the peers yet to accept the AC and the peers yet to answer (at allocation: N_PORTS minus 1 for a cache's transaction, N_PORTS for the IO's shareable read or write, 0 for its non-shareable read; `onyx_ccu.sv:710-711`; the counters are `clog2(N_PORTS + 1)` bits and step by the cycle's handshake count, `onyx_ccu.sv:745-777`). All accepted is the memory-read trigger (DEFER_AR 0); all answered is the gather complete. The verdict is the OR of the CRs' `DataTransfer` bits and, for the supplier, its `PassDirty`. This is the tagged, per-transaction completion of D4: no response window, no presumed miss, no timeout to prove a bound for. A slow peer holds only its own slots, and only until it answers.

## Snoop data buffers

The supplier's CD line lands in the buffer of the requester's port, indexed by slot and beat: one buffer per requester (N_PORTS + 1: each cache and the IO port, `onyx_ccu.sv:937-949`), each with one write port and two read ports (the port's replay engine and the absorption), distributed RAM, payload only. The one writer per buffer per cycle is chosen round-robin among the peers that want to write it; two peers supplying two different slots of the same requester in the same cycle take turns beat by beat, and `CDREADY` to a peer is low in the cycles it loses. `CDREADY` therefore depends on `CDVALID`, which AXI permits (READY may wait for VALID; VALID never waits for READY). At N_PORTS 2 each peer is the only writer of the other port's buffer, so no turn is ever lost.

Each requester has its own replay engine. It serves the requester's lowest-indexed slot (not the oldest; `onyx_ccu.sv:901-916`) whose gather is complete and whose line is in the buffer (or which needs only the single beat of a no-data class), yields the port's R channel to a memory beat for the port when both want it, and holds a presented beat until accepted. The absorption engine reads the buffer of the slot's requester port for the memory write.

## The invariants N3 and N4

- **N3, responses from in-flight fills.** onyx does not source snoop responses; the caches do. What onyx guarantees is on its side of the contract: a slot's line is locked from grant to retire, so a peer is never asked about a line whose fill onyx is still delivering to another port, and the requester's own entry is never snooped (the fanout excludes the requester).
- **N4, CD independence.** The CD path into onyx is its own channel into its own buffers; it shares nothing with the caches' W channels or the memory write port. A write-back cannot block a snoop response. The one coupling, by design, is the other way round: a write-back to a line waits for that line's gather and absorption.

## What the harness proves

The onyx formal harness at N_PORTS 2 (TASK-001 step 4) states the fanout and gather rules as properties: an AC names a valid slot of the other port whose AC this peer has not yet accepted, with the slot's line and its class's snoop; the AC payload is stable until accepted; each cache's outstanding count is exact and bounded; CR and CD are accepted whenever a snoop is outstanding; a CD beat lands in a live slot of the other port whose gather is incomplete; the memory AR issues only for a slot with every AC accepted and no `DataTransfer` known; a forwarded memory beat belongs to a gathered slot with no supplier and carries the requester's own ID; a replayed beat belongs to a gathered slot that was supplied or needs no data. The N-generic harness at N_PORTS 3 and 4, `formal/onyx/onyx_ccu_n3` and `_n4` (one N-generic harness, commit c6273863b), adds the per-peer accept and answer shadow the counters summarize (`ap_peer_shadow`, `ap_cr_slot`, `ap_snq_count`): cover 41/41 and `prove_fast` (17 properties, BMC depth 32) PASS at both N, 19 mutants fail at both N, the N = 3 `prove` (29 properties, depth 20) PASS; the N = 4 `prove` and both `prove_book` runs: running, see onyx TASK-001.
