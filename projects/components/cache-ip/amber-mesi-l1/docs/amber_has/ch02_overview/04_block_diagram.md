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

# Block Diagram

Figure 2.1 shows the shared `l1_core` (in `cache-ip/common-ip`, formerly `l1_core`) and the two rig tops that instantiate it, `amber_top` and `amber_ace_top`. The core is rig-agnostic: the CPU-side front end, control FSM, arrays, replacement engine, fill/drain engines, snoop responder, and observation wrapper are identical in both configurations. The pair-rig top adds plain AXI4 masters to memory (`axi4_master_rd/wr_monlite`); the onyx-rig top adds ACE masters (`axi4ace_master_rd/wr_monlite`) and the `amber_ace_issue` coherent-transaction issuer. Both tops merge three MonBus streams with a `monbus_arbiter`.

![amber whole unit: CPU front end, cache control, tag and data arrays, fill and drain engines, snoop responder, monitor merge](../assets/graphviz/01_block_diagram.png)

**Source:** [01_block_diagram.dot](../assets/graphviz/01_block_diagram.dot)

## Module roles

| Module | Role |
|---|---|
| `amber_top` | Pair-rig top: `l1_core` + plain AXI4 masters + snoop responder toward peer. |
| `amber_ace_top` | Onyx-rig top: `l1_core` + ACE masters + `amber_ace_issue` + snoop responder toward onyx. |
| `l1_core` | Shared rig-agnostic core instantiated by both tops. |
| `l1_cpu_frontend` | GAXI slave: request acceptance, response return, replay latch. |
| `l1_control` | Blocking pipeline FSM; owns tag-array control arbitration and the pending-fill bypass register. |
| `l1_tag_array` / `l1_data_array` | Dual-port `sdpram_core` stores; port A CPU/fill, port B snoop. |
| `l1_repl` | Pluggable replacement policy engine. |
| `l1_victim` | Dirty victim buffer + drain trigger; depth 1. |
| `l1_fill` / `l1_drain` | Read/write engines; plain AXI4 under `amber`, ACE under `amber_ace`. |
| `l1_snoop_resp` | ACE AC/CR/CD adapter; bus-agnostic inside. |
| `amber_ace_issue` | Maps cache events to the onyx D2 coherent-transaction subset. |
| `l1_monlite` | Observation wrapper; emits MonBus packets, never stalls. |

: Table 2.1: Module roles
