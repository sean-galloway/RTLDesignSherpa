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

Figure 2.1 shows the shared `amber_core` and the two rig tops that instantiate it. The core is rig-agnostic: the CPU-side front end, control FSM, arrays, replacement engine, fill/drain engines, snoop responder, and observation wrapper are identical in both configurations. The pair-rig top adds plain AXI4 masters to memory; the onyx-rig top adds ACE masters and the `amber_ace_issue` coherent-transaction issuer.

```mermaid
flowchart TB
    subgraph amber_top["amber — pair-rig top"]
        axi4m_rd["axi4_master_rd"]
        axi4m_wr["axi4_master_wr"]
    end

    subgraph amber_ace_top["amber_ace — onyx-rig top"]
        acem_rd["axi4ace_master_rd"]
        acem_wr["axi4ace_master_wr"]
        ace_issue["amber_ace_issue"]
    end

    subgraph core["amber_core — shared rig-agnostic core"]
        frontend["amber_cpu_frontend<br/>GAXI slave"]
        ctrl["amber_control<br/>blocking FSM + bypass"]
        tag["amber_tag_array<br/>sdpram_core port A/B"]
        data["amber_data_array<br/>sdpram_core port A/B"]
        repl["amber_repl"]
        victim["amber_victim<br/>depth 1"]
        fill["amber_fill"]
        drain["amber_drain"]
        snoop["amber_snoop_resp<br/>AC/CR/CD adapter"]
        mon["amber_monlite"]
    end

    cpu["CPU / STREAM GAXI master"] --> frontend
    frontend --> ctrl
    ctrl --> tag
    ctrl --> data
    ctrl --> repl
    ctrl --> victim
    ctrl --> fill
    ctrl --> drain
    fill --> data
    drain --> data
    snoop --> tag
    snoop --> data

    snoop <-->|"AC / CR / CD"| peer["peer amber cache<br/>or onyx CCU"]
    axi4m_rd <-->|"AR / R"| mem["memory"]
    axi4m_wr <-->|"AW / W / B"| mem
    acem_rd <-->|"AR / R"| onyx["onyx CCU"]
    acem_wr <-->|"AW / W / B"| onyx
    ace_issue --> acem_rd
    ace_issue --> acem_wr
    mon -->|"128-bit MonBus"| tally["monbus_tally_axil"]
    ctrl --> mon
```

**Source:** [01_block_diagram.mmd](../assets/mermaid/01_block_diagram.mmd) — the fence above mirrors it.

## Module roles

| Module | Role |
|---|---|
| `amber` | Pair-rig top: `amber_core` + plain AXI4 masters + snoop responder toward peer. |
| `amber_ace` | Onyx-rig top: `amber_core` + ACE masters + `amber_ace_issue` + snoop responder toward onyx. |
| `amber_core` | Shared rig-agnostic core instantiated by both tops. |
| `amber_cpu_frontend` | GAXI slave: request acceptance, response return, replay latch. |
| `amber_control` | Blocking pipeline FSM; owns tag-array control arbitration and the pending-fill bypass register. |
| `amber_tag_array` / `amber_data_array` | Dual-port `sdpram_core` stores; port A CPU/fill, port B snoop. |
| `amber_repl` | Pluggable replacement policy engine. |
| `amber_victim` | Dirty victim buffer + drain trigger; depth 1. |
| `amber_fill` / `amber_drain` | Read/write engines; plain AXI4 under `amber`, ACE under `amber_ace`. |
| `amber_snoop_resp` | ACE AC/CR/CD adapter; bus-agnostic inside. |
| `amber_ace_issue` | Maps cache events to the onyx D2 coherent-transaction subset. |
| `amber_monlite` | Observation wrapper; emits MonBus packets, never stalls. |

: Table 2.1: Module roles
