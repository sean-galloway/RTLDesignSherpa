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

# Fabric ACE Master Timing

**Status:** landed (Task 9). `jet_ace_top` replaces the plain-AXI4
transports with `axi4ace_master_*` and adds `jet_ace_issue` (amber's
`amber_ace_issue` mapping, renamed for the jet top). The transaction
mapping is inherited from amber's issue-#106 reconciliation:

| Cache event | ACE transaction |
|---|---|
| Read miss | `ReadNotSharedDirty` (ARSNOOP 0x3) |
| Write miss | `ReadUnique` |
| Upgrade (write hit on S) | `CleanUnique` (AR channel, spec encoding) |
| Dirty victim drain | `WriteBack` |
| Clean victim drop | `Evict` (snoop-filter accuracy at the SI) — **not emitted by jet v1**: clean victims drop silently, so `jet_ace_issue`'s AW-only generator is present but unexercised |

All MAS ch03/02 timing rules apply; the ACE additions are amber's:
RRESP PassDirty honored on fills (live on this top's 4-bit RRESP — the
pair-rig twin `jet_top` never sees it), CR/CD conventions on the snoop
side, RACK/WACK auto-pulsed by the wrapper transports per the family
ruling (2026-10-11). Multiple outstanding coherent reads follow the same
single-ID in-order rule as the pair rig in v1; the onyx D2 subset defines
what onyx accepts.
