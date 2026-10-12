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


# NoC IP

Network-on-chip components. Created 2026-09-29 (Sean) when the component tree
was regrouped into `*-ip` families.

> **2026-10-12 reorganization.** The `delta` that lived here was never a NoC —
> it is a working **AXI4-Stream crossbar generator** and was re-homed to
> [`fabric-gen-ip/delta/`](../fabric-gen-ip/delta/) where the other
> interconnect generators live. What stayed here is the aspirational
> **DELTA mesh NoC design draft** — a chaptered spec (routers, virtual
> channels, XY routing, packet types) that has **no RTL** and exists as
> design groundwork for a future NoC.

| Directory | What | Status |
|---|---|---|
| [`delta_spec/`](delta_spec/) | DELTA mesh NoC design draft (4×4 mesh, VC, XY routing) + rendered PDF/DOCX | **Draft — not implemented** (no RTL; do not cite as existing hardware) |
| [`CLAUDE.md`](CLAUDE.md) | Agent guide for the NoC draft | — |
| `generate_pdf.sh` | Renders `delta_spec/` to DOCX/PDF | — |

A live NoC component would arrive here the way `ecc-ip/reed-solomon` did:
README, CLAUDE.md and a PRD with its decision table first, RTL when a consumer
fixes the decisions. Until then, treat this lane as reserved.
