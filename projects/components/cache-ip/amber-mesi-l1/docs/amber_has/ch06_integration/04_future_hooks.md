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

# Future Hooks

## Recorded future work, not blockers

The following items are explicitly out of scope for amber v1.0 but are recorded as hooks so the architecture does not accidentally close them off.

| Hook | Why it is future work | How amber leaves the door open |
|---|---|---|
| Lockup-free miss handling | The core research delta for `jet` (J1–J7) | `l1_core`'s module boundaries are clean; MSHRs replace the pending-fill bypass and the single-outstanding FSM without changing the array or snoop adapter interfaces. |
| MOESI O-state | Measurement for the pair rig, not a v1 requirement | The 3-bit state field in `l1_tag_array` already reserves the encoding headroom. |
| tree-PLRU cache_sim golden model | Timing-tight policy without a sim parity model today | `REPL_POLICY` is an elaboration parameter; adding a tree-PLRU model to cache_sim and the DV scoreboard is a model extension, not an RTL change. |
| STREAM attachment | First real consumer after TB masters (D10) | The CPU-side GAXI slave is the attachment point; no adapter needed. |
| Directory-lite snoop filter | Deferred from amber D4, reopened as onyx D3 | The ACE-shaped snoop port is the boundary; a filter can be inserted between `l1_snoop_resp` and the peer/onyx without touching `l1_core`. |
| ACE DVM and barriers | Out of scope per onyx D8 | The snoop adapter and `amber_ace_issue` ignore these transaction types; adding them is an adapter/issuer change. |
| Exclusive loads/stores with internal monitor | Out of scope for v1.0; needed for atomic semaphore operations | Book §6.3 describes the internal monitor, §7.9–7.10 the competing-CU livelock scenarios. Reserved as a hook: adding exclusives requires the monitor plus the temporary snoop-stall safeguard recorded in the coherence FSM. |
| Clean-victim Evict messaging | Snoop-filter accuracy when a directory-lite filter is added (deferred from D4 to onyx D3) | Book §7.4 and §10.5: clean victims should send `Evict` so the filter can reset its occupancy bits. amber's eviction path currently issues `Evict` only on the ACE write master; this hook records that a separate clean-victim `Evict` message may be needed for filter accuracy. |
| Multi-copy-atomic store invariant | Documented assumption for v1.0; simplifies protocol reasoning | Book §14.33: making stores multi-copy atomic (all copies invalidated before the store is visible) simplifies the design. amber assumes this invariant in its formal targets; if the assumption is ever relaxed, the coherence FSM and response ordering must be revisited. |

: Table 6.1: Future hooks

## Closing D3 and D11

D3 (memory-side interface) and D11 (array construction) are decided (PRD v0.6, 2026-10-07); the array-construction implementation ruling lives in the RTL completion plan (Task 9) and the MAS errata. The shapes recorded here — AXI4/ACE house wrappers and `sdpram_core`-based dual-port arrays — are the decided architecture, not candidates.
