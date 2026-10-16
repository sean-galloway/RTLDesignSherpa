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

# Observability and DFT

## Ocelus Counter Suite

> **IMPLEMENTED** — `delta_mesh_cell` exposes an eleven-entry 32-bit counter bank read through the config port. The design is per the delta mesh design spec dated 2026-10-13 (`docs/superpowers/specs/2026-10-13-delta-mesh-design.md`).

Each cell exposes saturating 32-bit counters readable through the config port. The suite is informed by NPU observability practice rather than by the sparse NoC literature. Counter indices 0..10 are defined; indices above 10 read back 0. The counter bank is selected by setting `table_index[15] = 1` on a config read.

| Index | Counter | Description |
|-------|---------|-------------|
| 0 | C_FLITS_IN | Flits received by the cell. |
| 1 | C_FLITS_OUT | Flits transmitted by the cell. |
| 2 | C_PKTS_IN | Packets received (TLAST handshakes). |
| 3 | C_PKTS_OUT | Packets transmitted (TLAST handshakes). |
| 4 | C_STALL_CYCLES | Cycles the cell saw output stall. |
| 5 | C_CREDIT_STALL | Cycles a granted output waited for downstream credit. |
| 6 | C_ERR_DROP | Malformed-destination drops (also mirrored on `o_err_drop_cnt`). |
| 7 | C_MODE_ACKS | Broadcast mode-switch acks received (also mirrored on `o_mode_acks`). |
| 8 | C_BULK_STARVE | Cycles bulk reservation was due. |
| 9 | C_SPEC_COMMITS | Speculative grants that committed. |
| 10 | C_SPEC_REVOKES | Speculative grants that were revoked. |

: Ocelus counter bank indices.

Counters are frozen when `ENABLE_COUNTERS == 0`. They clear on `aresetn`.

## DFT Test Mode

Test mode configures each cell into one of three deterministic routing patterns so the mesh wiring behaves as a concatenated bus. With three patterns, stuck-at and bridge faults are testable with approximately ⌈log₂(n)⌉ patterns. The mode is controlled through the config port using a DFT escape write (`table_index[15:12] = 4'hD`, payload bit 0 enables DFT, bits 2:1 select the pattern), and each cell drives an `o_dft_active` output.
