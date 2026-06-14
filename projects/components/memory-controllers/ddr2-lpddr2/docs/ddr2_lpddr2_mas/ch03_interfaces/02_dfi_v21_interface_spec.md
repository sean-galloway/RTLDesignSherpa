<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> &middot; <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> &middot;
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> &middot;
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# DFI v2.1 Master Protocol

**Status:** Skeleton — to be authored during MAS week


The DFI v2.1 master port drives the DRAM PHY.

## Scope

This section is the wire-level DFI v2.1 contract as implemented by this controller. The full DFI v2.1 spec covers more — training, frequency change, low-power negotiation — see HAS §2.1 for what is and isn't in scope here.

## Sub-Interfaces Supported

- Command sub-interface
- Write-data sub-interface
- Read-data sub-interface
- Status sub-interface
- Update sub-interface (controller-initiated and PHY-initiated)

## Sub-Interfaces Not Supported (v1)

- Training (not required at v2.1 for DDR2/LPDDR2)
- Frequency change
- Low-power negotiation (CKE used directly)
- CRC (not in DDR2/LPDDR2)

## Phase / Gear Topology

`N_PHASES` per MC clock; gear FUB (see §2.15) handles packing.

## TODO

- Per-signal timing diagrams (rise-to-rise)
- WRPHASE / RDPHASE selection guidelines
- ctrlupd / phyupd protocol detail (rare in v2.1 but spec-mandated)
- DDR2 ras/cas/we vs LPDDR2 CA encoding (cross-ref to §2.14)

