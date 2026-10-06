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
| Lockup-free miss handling | The core research delta for `jet` (J1–J7) | `amber_core`'s module boundaries are clean; MSHRs replace the pending-fill bypass and the single-outstanding FSM without changing the array or snoop adapter interfaces. |
| MOESI O-state | Measurement for the pair rig, not a v1 requirement | The 3-bit state field in `amber_tag_array` already reserves the encoding headroom. |
| tree-PLRU cache_sim golden model | Timing-tight policy without a sim parity model today | `REPL_POLICY` is an elaboration parameter; adding a tree-PLRU model to cache_sim and the DV scoreboard is a model extension, not an RTL change. |
| STREAM attachment | First real consumer after TB masters (D10) | The CPU-side GAXI slave is the attachment point; no adapter needed. |
| Directory-lite snoop filter | Deferred from amber D4, reopened as onyx D3 | The ACE-shaped snoop port is the boundary; a filter can be inserted between `amber_snoop_resp` and the peer/onyx without touching `amber_core`. |
| ACE DVM and barriers | Out of scope per onyx D8 | The snoop adapter and `amber_ace_issue` ignore these transaction types; adding them is an adapter/issuer change. |

: Table 6.1: Future hooks

## Closing D3 and D11

D3 (memory-side interface) and D11 (array construction) remain open. Closing them will produce either a revised HAS or the MAS, depending on whether the decisions stay at architecture level or move into micro-architecture. Until then, the current directions — AXI4/ACE house wrappers and `sdpram_core`-based dual-port arrays — are the working defaults and the targets for the first RTL cut.
