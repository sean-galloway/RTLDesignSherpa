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

# Key Features

## N cache-side ports, 2 to 4 (D11, decided)

`N_PORTS` is an elaboration parameter; every cache-side signal is an unpacked array over it, and the transaction table, the AC queues, the snoop-data buffers and the replay engines scale with it. The measured configuration is two ports.

## The D2 subset (decided)

`ReadNotSharedDirty`, `ReadUnique`, `CleanUnique`, `WriteBack`, `Evict` -- the transactions the house caches issue, carried on the D-8 sideband. `MakeUnique` decodes as a no-data class. Barriers, DVM and the WLU/WU family are out (D8, N5, N6).

## Broadcast snoop (D3, decided)

Every allocated transaction snoops every attached cache except the requester; onyx keeps no sharer state. A directory-lite filter is a future parameter.

## Tagged gather (D4, decided)

Per transaction, counters of the peers yet to accept the AC and yet to answer; the verdict is the OR of the CRs' `DataTransfer` and the supplier's `PassDirty`. No response window, no presumed miss.

## Per-line serialization (D5, decided)

A transaction table is the point of serialization: one valid slot per line, different lines interleave, the lock held from grant to the requester's retire. `SERIAL_MODE` is the one-at-a-time bring-up shape.

## Adjudicated data source with two read modes (D6, decided)

Data is accepted from the one peer that supplies it (Exclusive or Modified under MESI); memory is read otherwise; a `PassDirty` line is absorbed into memory. `DEFER_AR` selects whether the memory read is issued alongside the snoop or only after the gather, so the bandwidth-for-latency trade is measured, not assumed.

## Fair arbitration everywhere

Rotating priority at the grant over the ports, at the write port over the write-backs and the absorption, and at each snoop-data buffer's write among the peers.

## Observation (D9, decided, not yet built)

`*_monlite` taps behind `USE_MONITOR` for transaction start, fanout, gather completion, elision hit/miss, serialization stalls and drains are a later TASK-001 step; the debug taps the pair-rig testbench reads are in place.

## Design invariants

Invariant 6 (CD before CR) is decided and relied on; N3 and N4 are honored by construction (Chapter 3.4); the others remain proposed in the PRD.
