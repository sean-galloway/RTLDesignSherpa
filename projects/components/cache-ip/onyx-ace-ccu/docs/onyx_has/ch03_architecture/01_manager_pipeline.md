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

# Manager Pipeline

**Status:** architecture recorded 2026-11-21 (D1 and D2 decided 2026-11-20, PRD v0.7); the RTL is `rtl/top/onyx_ccu.sv`, onyx TASK-001 step 2.

## What enters and what leaves

onyx v1 is a coherency unit and nothing else (D1): N_PORTS cache-side ports (2 to 4, D11), one AXI4 master toward memory, and the snoop fanout to every attached cache. The ACE-Lite IO port that D1 keeps in scope is a later step of TASK-001 and is not in the v1 pipeline.

A cache-side port carries three things from a jet-prime cache:

- the cache's plain-AXI4 memory side (AR/R for fills, AW/W/B for write-backs), exactly as jet-prime drives it toward the pair fabric;
- the D-8 coherence sideband: one pulse per fill launch or upgrade (`ReadNotSharedDirty`, `ReadUnique`, `CleanUnique`) and per dirty write-back launch (`WriteBack`), carrying the line address and the request class; and the retire sideband, one pulse per retired MSHR entry or completed upgrade, carrying the entry's read ID;
- the ACE-shaped snoop responder port the cache already has (D7): AC in, CR and CD out.

The request class rides the sideband rather than `ARSNOOP` because that is what the house caches do; the AR itself is plain AXI4. onyx decodes the D2 subset from the sideband: `ReadNotSharedDirty`, `ReadUnique`, `CleanUnique`, `WriteBack`, `Evict`. `WriteBack` and `Evict` allocate nothing in the manager (the write-back is the write port's business; a clean eviction needs no coherence action in a broadcast CCU without a directory); the other three allocate a transaction. `MakeUnique` is decoded as a no-data class but no cache issues it yet.

## The life of a transaction

A fill or upgrade moves through the manager in these steps; every one is a field of the transaction table (Chapter 3.3), so the pipeline is the table, not a chain of stages.

1. **Pulse.** The sideband pulse enters the port's pending queue (depth 4). The head of the queue, or the live pulse when the queue is empty, is the port's grant candidate.
2. **Grant.** A candidate is granted when no valid slot holds its line (the per-line lock, D5), a slot is free, and the port has no AR still untaken from an earlier grant. One grant per cycle, rotating priority over the ports. The grant allocates the slot and arms the port's `ARREADY`.
3. **AR take.** The cache's AR for the launch is taken into the slot (its ID, cache and protection attributes). `ARREADY` comes from the armed register only, never combinationally from the AR.
4. **Fanout.** The slot is queued for an AC to every peer except the requester (D3, Chapter 3.4). Each peer's AC channel drains its queue in order, up to SNOOP_INFLIGHT accepted and unanswered.
5. **Memory read.** For a data class, the memory AR issues once every peer has accepted its AC, unless a peer has already answered with `DataTransfer` (DEFER_AR = 0); with DEFER_AR = 1 it issues only once every CR is in and none supplied the line (D6). A presented AR is held until taken.
6. **Gather and route.** CRs arrive per peer in AC order and pair with their slots; the slot's verdict is the OR of the `DataTransfer` bits and the supplier's `PassDirty`. Memory beats for the slot are forwarded to the requester once the gather is complete with no supplier, held until then, and dropped if a peer supplied the line. A supplied line is replayed from the slot buffer; a no-data class gets its single response beat the same way. A `PassDirty` line is also written to memory (the absorption).
7. **Retire and release.** The requester's retire pulse naming the slot's read ID sets the slot's retire bit. The slot frees when the gather is complete, the requester has every beat, the memory read (if issued) is drained, the absorption (if any) has its `BRESP`, and the retire bit is set. The lock on the line drops with the slot.

The write side is a pass-through: a cache's `WriteBack` AW/W/B goes to the memory write port, round-robin with the other ports' write-backs and the absorptions, and holds while a slot on its line has an incomplete gather or a pending absorption.

## Bring-up modes

Two parameters give the bring-up shapes the PRD rows name: `SERIAL_MODE` admits one transaction system-wide (the D5 fallback), and `DEFER_AR` selects the D6 mode. Both are elaboration parameters in v1; the measured configuration is SERIAL_MODE 0 with each DEFER_AR mode built as its own bitstream (reference rig selections 4 and 5).

## Where it came from

The pipeline is jet-prime's pipelined pair fabric (`jet_prime_pair_fabric`, jet-prime TASK-001 steps 3 to 5) generalized to N ports: the same table, the same lock, the same AR-alongside-the-snoop timing, the same retire-based release. At N_PORTS 2 onyx reproduces the fabric's behavior on jet-prime's pair-rig grid line for line (TASK-001 step 2), which is what makes the fabric's measured cycles the baseline onyx is judged against.
