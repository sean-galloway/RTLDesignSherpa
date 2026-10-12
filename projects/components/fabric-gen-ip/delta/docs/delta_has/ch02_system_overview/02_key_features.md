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
- `--amba5 [--parity-width M]` adds `TWAKEUP` and `TPARITY` (port-matches `rtl/amba/axis5`).

When neither option is used, the generated module is byte-identical to pre-2026-10-12 output.

## Optional Packet Counters

Per-master and per-slave 32-bit packet counters count completed packets (`TVALID && TREADY && TLAST`). Disable them with `--no-counters` to save area.

## Formal Assertions

When `FORMAL` is defined, the generated RTL includes assertions that check:

- One-hot (or zero-hot) grants per slave.
- `TDEST` is within range when `s_axis_tvalid` is asserted.

## Code Generation

The generator is a Python script (`bin/delta_generator.py`) that reuses the unified `Module` framework. It produces lint-clean SystemVerilog and is the single source of truth for all checked-in RTL variants.
