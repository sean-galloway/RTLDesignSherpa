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

# Architecture and Datapath

This chapter is the implementation-level architectural orientation: the macro
hierarchy, the read/write datapath flow, and the clocking topology. Per-FUB
detail is in §2.

## Macro Hierarchy

The controller is decomposed into **16 leaf FUBs grouped under 5 macros**.
The top-of-tree is `ddr2_lpddr2_core_macro` (which the SoC instantiates
alongside `axi_frontend_macro`):

```
SoC top
├── axi_frontend_macro            5 FUBs  — host AXI4 + CAMs + snarf
└── ddr2_lpddr2_core_macro
    ├── command_scheduler_macro   7 FUBs  — "what command to issue this cycle"
    ├── data_path_macro           2 FUBs  — "move bytes between AXI and DFI"
    └── dfi_v21_interface_macro   2 FUBs  — "translate to DFI v2.1 wires"
```

Per-macro FUB rosters:

| Macro                          | FUBs                                                                                                                       |
|--------------------------------|----------------------------------------------------------------------------------------------------------------------------|
| `axi_frontend_macro`           | `axi_intake`, `addr_mapper`, `wr_cmd_cam`, `rd_cmd_cam`, `wr2rd_forward`                                                   |
| `command_scheduler_macro`      | `scheduler`, `xbank_timers`, `global_timers`, `refresh_ctrl`, `powerdown_ctrl`, `mode_register`, `init_sequencer`          |
| `data_path_macro`              | `wr_beat_sequencer`, `rd_cl_aligner`                                                                                       |
| `dfi_v21_interface_macro`      | `dfi_cmd_formatter`, `dfi_signal_pack`                                                                                     |

All FUB outputs are strict-flop registered (Q of a dedicated flop). Macros
are pure structural — no behavioral logic. This adds one register stage per
macro boundary but guarantees hierarchical timing closure.

## Top-Level FUB Topology

The top-level wiring view, with macro boundaries shown:

![Top-Level FUB Topology](../assets/mermaid/01_top_fub_topology.png)

**Source:** [01_top_fub_topology.mmd](../assets/mermaid/01_top_fub_topology.mmd)

The salient property: there is exactly **one** stage where AXI-layer concepts (burst, ID, write strobe) cross into DRAM-layer concepts (rank, bank, row, column). That stage is `addr_mapper` → `{rd,wr}_cmd_cam`. Upstream of `addr_mapper` everything is AXI; downstream of the CAMs everything is DRAM.

## Read / Write Datapath: AXI → addr-hash → CAM

The user-facing entry point is `axi_intake`. From the intake, the read and write paths share `addr_mapper` (one cycle) and then split into two separate CAMs:

![AXI → addr_mapper → CAMs Datapath](../assets/mermaid/02_axi_to_cam_datapath.png)

**Source:** [02_axi_to_cam_datapath.mmd](../assets/mermaid/02_axi_to_cam_datapath.mmd)

### Why Two CAMs, Not One

The CAM split happens here, not at the scheduler, because read and write CAMs hold **different metadata** and have **different lifetimes**:

| CAM            | Key      | Data                                                       | Cleared on             |
|----------------|----------|------------------------------------------------------------|------------------------|
| `wr_cmd_cam`   | AXI ID   | (rank, bank, row, col, burst_len, **w_buf_ptr**, **strb_ptr**) | B-channel response push |
| `rd_cmd_cam`   | AXI ID   | (rank, bank, row, col, burst_len, **rid_counter**, **expected_beats**) | last R beat of the burst |

A single unified CAM would either carry both metadata sets (wasteful) or force an awkward "is_write" predicate on every lookup. Keeping the CAMs separate also means the read and write paths can be sized independently — the read path typically deeper because read latency is longer; the write path can be shallower because write completion is fire-and-forget.

The two CAMs have visibly different lifecycles — note in particular that the write side stays "alive" through the post-issue write window (waiting on `b_complete` from `xbank_timers`) while the read side just counts beats:

![CAM Slot Lifecycles (read vs. write)](../assets/mermaid/03_cam_lifecycles.png)

**Source:** [03_cam_lifecycles.mmd](../assets/mermaid/03_cam_lifecycles.mmd)

### Why the XOR Happens Before the CAM

Address XOR / hash (`addr_mapper`) **must** happen before the CAM push because the CAM stores the post-decode (rank, bank, row, col) tuple — not the raw AXI address. Two reasons:

1. **Stable CAM key data.** The CAM is queried by the scheduler in the (rank, bank) dimension — for example, "do any pending writes target rank 0 bank 3, row R?" Storing the post-decode tuple makes this a direct comparison; storing the raw AXI address would force the scheduler to re-XOR on every match.

2. **Address-mapping scheme is per-controller, not per-burst.** The `ADDR_MAP_TUNING.scheme_or` field is global to the controller. If we stored raw addresses, a runtime scheme change (which can happen at any quiet point) would force a CAM walk to re-decode every entry. Storing the decoded tuple means a scheme change only affects **new** AXI bursts — old in-flight bursts continue with their decoded address. This matches the quiet-point semantics in HAS §6.3.

The `addr_mapper` is **combinational** — no pipeline stage between AXI intake and CAM push — so the timing budget for the XOR network is one cycle minus the AXI register-slice slack. See `ch02_blocks/03_addr_mapper.md` for the timing breakdown.

### Why the AXI-side metadata stays in `axi_intake`

Some AXI fields (`awcache`, `awprot`, `awqos`, `awregion`, `bid`/`rid`) never need to cross into DRAM-layer state. These are held in small **side tables** inside `axi_intake`, indexed by the same AXI ID that keys the CAMs. The CAM holds the *DRAM* state; the side table holds the *AXI* state. On B/R completion, the CAM produces the completion signal and the side table produces the response metadata; the two are joined at the AXI return port.

This split keeps the CAM narrow (16 ID slots × ~36 bits in the default config) and pushes the AXI-specific clutter into the FUB that already owns the protocol.

## Clocking Topology

Two external clocks; one CDC.

| Clock         | Frequency Range | Drives                                                |
|---------------|-----------------|-------------------------------------------------------|
| `mc_clk`      | 100–500 MHz     | All DRAM-layer FUBs (everything in core_macro) plus `axi_frontend_macro` |
| `apb_pclk`    | 25–100 MHz      | (CSR slave — not yet implemented)                     |

A future CSR slave will own the single CDC between `apb_pclk` and `mc_clk`. CSR overrides will be handed off across this CDC into a quiet-point staging register; override-application happens at the next quiet point on `mc_clk`. Quiet-point detection lives in `powerdown_ctrl` (no commands in flight, no refresh in progress). v1 has no CSR — runtime values are driven directly from the testbench.

There is **no CDC** in the AXI4 datapath — `axi_intake` runs in the `mc_clk` domain. If the SoC's AXI master is on a different clock, an external clock converter is required upstream of the controller.

## DFI Phase / Rate Topology

The DFI v2.1 master interface is `DFI_RATE`-deep (per-phase × N widths). The
MC clock drives one frame of `DFI_RATE` DFI cycles per MC clock cycle. The
`dfi_signal_pack` FUB aggregates scheduler-issued commands and data into the
right per-phase slot. The scheduler does not see the phase dimension — its
issue rate is one command per MC clock; the pack absorbs all of the
phase-level scheduling. v1 uses phase 0 for the command; other phases drive
NOP.
