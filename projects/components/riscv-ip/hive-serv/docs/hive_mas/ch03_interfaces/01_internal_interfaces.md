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

# Internal Packages and Wiring

## Package Organization

One package per block plus a top-level config include; no cross-imports
from leaf packages upward:

| File | Contents |
|------|----------|
| `includes/hive_config.svh` | All `parameter` defaults (Chapter 6); single source of truth |
| `includes/hive_ctrl_net_pkg.sv` | Control-network opcodes, frame struct, urgent-flag encoding |
| `includes/hive_desc_pkg.sv` | CDA descriptor struct, field masks, `PKT_*` encodings |
| `includes/hive_cfg_pkg.sv` | Context ids, config register offsets, error codes |
| `includes/hive_obs_pkg.sv` | Observation-bus record layout (Chapter 5) |

: Package layout

Structs (not raw bit vectors) cross block boundaries for every interface
wider than a few signals — descriptor records, control frames, observation
records — so port lists stay readable and compile-time checked.

## Key Internal Interfaces

**Descriptor mailbox → `descriptor_gen`** (in `hive_c_controller`):
firmware writes a `descriptor_t` record; `descriptor_gen` pulses `done` on
handshake and raises `stall` while the injection queue is full.

**Control network frame** (§2.4): the 32-bit frame is the only
master-to-slave and slave-to-master payload; widening to 64-bit is an open
area item if the statistics payload overflows 16 bits regularly.

**Config-manager injection request**: `switch_controller` raises
`inject_req` with a completed PKT_CONFIG record; the HIVE-C injection path
(or SERV flood, Phase-2 decision) carries it into Delta.

**Observation bus** (Chapter 5): a flat, `hive_c_clk`-domain record stream
exported through `hive_top`; each block drives its slice; slices are
concatenated, not arbitrated (fixed layout in `hive_obs_pkg`).

## Wiring Conventions

- AXIS signals are named `axis_<role>_<signal>` with `role` ∈ {cda, stat,
  cfg, inj}; AXI4-Lite as `axil_<signal>`.
- Resets are `*_rst_n`, active low, synchronized per §1.3; no block
  generates its own reset from `system_rst_n` directly.
- Every inter-block interface documents its clock domain at the port; a
  port pair in different domains must name the CDC element in the block
  header comment.

---

**Last Updated:** 2026-10-12
