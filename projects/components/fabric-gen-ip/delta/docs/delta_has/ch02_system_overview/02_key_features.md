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

## Flat M×N Crossbar

Delta generates a single self-contained SystemVerilog module implementing a full M×N crossbar. Every master can reach every slave; each slave has its own round-robin arbiter.

## TDEST-Based Routing

There is no address map. The target slave is taken directly from `s_axis_tdest`. This makes request decode simpler than an address-based crossbar and removes configuration risk.

## Packet-Atomic Round-Robin Arbitration

Each slave arbiter grants one master at a time and holds that grant until the current packet's `TLAST` beat is accepted. This guarantees:

- No packet interleaving on a slave.
- Fair bandwidth allocation among contending masters.
- Streaming packet boundaries are preserved end-to-end.

## Combinational Data Mux with Registered Grant

The data path from the granted master to the selected slave is combinational. The grant decision is registered on `aclk`, giving a predictable two-cycle latency while keeping the critical path short.

## Optional Richness (Default Off)

Two command-line options add sidebands without changing the default output:

- `--strb-width N` adds `TSTRB` byte qualifiers (port-matches `rtl/amba/axis4`).
- `--amba5` adds `TWAKEUP` and the IHI 0051B chapter 5 odd-parity check signals (`TDATACHK` ... `TWAKEUPCHK`), with sticky per-port error flags. The ports match `rtl/amba/axis5`.

When neither option is used, the generated module is byte-identical to pre-2026-10-12 output.

## Optional Packet Counters

Per-master and per-slave 32-bit packet counters count completed packets (`TVALID && TREADY && TLAST`). Disable them with `--no-counters` to save area.

## Formal Assertions

When `FORMAL` is defined, the generated RTL includes assertions that check:

- One-hot (or zero-hot) grants per slave.
- `TDEST` is within range when `s_axis_tvalid` is asserted.

## Code Generation

The generator is a Python script (`bin/delta_generator.py`) that reuses the unified `Module` framework. It produces lint-clean SystemVerilog and is the single source of truth for all checked-in RTL variants.

## Mesh-Mode Features

> **IMPLEMENTED** — Mesh mode is a generator option that emits `delta_mesh_cell` and a fabric top. The design is per the delta mesh design spec dated 2026-10-13 (`docs/superpowers/specs/2026-10-13-delta-mesh-design.md`). The flat TDEST crossbar remains the default and is untouched.
>
> Still deferred: CXS migration (owner plan, parallel rapids_cxs work), MonBus observation aggregation in the tile IP (parallel session), 1 cycle/hop lookahead (issue #120), and SRAM FIFO_IMPL (issue #118).

- **3-D table-routed mesh of identical cells** — one `delta_mesh_cell` per fabric coordinate, connected to ±X/±Y/±Z neighbors, the two diagonal-axis links (P_DIA for tetrad-scale, P_DIA2 for tile-scale), and one local port.
- **Placement hierarchy** — cell → tetrad (`2×2×1` = 4 cells, fully-connected K4) → tile (`2×2×1` tetrads = 16 cells, K4 at the tetrad level). Owner-named 2026-10-15; the datapath stays one module per cell, and the tetrad/tile wrappers exist only for MonBus observation aggregation (outside delta).
- **2 VCs with escape-channel deadlock freedom** — VC0 carries the connected, acyclic escape subrelation; VC1 carries minimal-or-budgeted adaptive routes. VC1 may drain into VC0, but VC0 may never enter VC1.
- **3 QoS classes** — config, latency, and bulk traffic get separate VCs and injection buffers, with strict priority, programmable aging, and a bulk minimum reservation.
- **In-band config with broadcast mode-switch** — per-cell RAM tables load through the data path; a broadcast mode-switch message switches all cells to one of 10 standard fabric modes atomically after a fabric-wide ack barrier.
- **10 standard fabric modes** — mesh, systolic-1D, wavefront-2D, stencil-3D, broadcast, convergecast/reduce, all-to-all/transpose, pipeline+rapids-stream, tetrad all-to-all (K4 via P_DIA), and tile all-to-all (K4-of-tetrads via P_DIA2).
- **Multicast** — VC0-only, BRCP-conformed paths with source-side replication, multiple delivery VCs, and no responses.
- **Systolic/torus package** — per-dimension torus wrap (`--torus=x,y,z`), source-route mode (`--source-route`), and speculative allocation (`--speculation`). Route lookahead is the remaining latency step (issue #120).
