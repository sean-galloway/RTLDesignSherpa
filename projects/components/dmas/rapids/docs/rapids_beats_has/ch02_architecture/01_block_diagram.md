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

## Top-Level Architecture

![RAPIDS Beats Block Diagram](../assets/mermaid/04_block_diagram.png)

**Source:** [04_block_diagram.mmd](../assets/mermaid/04_block_diagram.mmd)

```mermaid
graph TB
    subgraph RAPIDS_CORE["rapids_core_beats"]

        subgraph SCHED_ARRAY["beats_scheduler_group_array"]
            direction TB
            SG0["Scheduler Group 0"]
            SG1["Scheduler Group 1"]
            SGN["..."]
            SG7["Scheduler Group 7"]

            subgraph SG_DETAIL["Scheduler Group (x8)"]
                SCHED["scheduler_beats"]
                DESC["descriptor_engine_beats"]
                SCHED <--> DESC
            end
        end

        subgraph SINK_PATH["sink_data_path_beats"]
            SNK_SRAM["snk_sram_controller"]
            SNK_AXI["axi_write_engine"]
            SNK_ALLOC["alloc_ctrl"]
            SNK_DRAIN["drain_ctrl"]

            SNK_SRAM --> SNK_AXI
            SNK_ALLOC --> SNK_SRAM
            SNK_DRAIN --> SNK_SRAM
        end

        subgraph SRC_PATH["source_data_path_beats"]
            SRC_AXI["axi_read_engine"]
            SRC_SRAM["src_sram_controller"]
            SRC_ALLOC["alloc_ctrl"]
            SRC_DRAIN["drain_ctrl"]

            SRC_AXI --> SRC_SRAM
            SRC_ALLOC --> SRC_SRAM
            SRC_DRAIN --> SRC_SRAM
        end

        SCHED_ARRAY -->|"Write Commands"| SINK_PATH
        SCHED_ARRAY -->|"Read Commands"| SRC_PATH
    end

    %% External Interfaces
    APB["APB Config"] --> SCHED_ARRAY
    DESC_MEM["Descriptor Memory"] <-->|"AXI4"| SCHED_ARRAY

    AXIS_IN["AXIS Slave<br/>(Network In)"] --> SNK_ALLOC
    SNK_AXI -->|"AXI4 Write"| DATA_MEM["Data Memory"]

    DATA_MEM -->|"AXI4 Read"| SRC_AXI
    SRC_DRAIN --> AXIS_OUT["AXIS Master<br/>(Network Out)"]

    RAPIDS_CORE -->|"MonBus"| MON["Monitor Aggregator"]

    style RAPIDS_CORE fill:#e3f2fd
    style SCHED_ARRAY fill:#fff9c4
    style SINK_PATH fill:#c8e6c9
    style SRC_PATH fill:#ffccbc
```

## Top-Level Integration (rapids_beats_top)

`rapids_core_beats` is wrapped by `rapids_beats_top`, which adds the software
register interface, configuration mapping, and monitoring infrastructure. A
single APB slave feeds a command/response router that splits accesses between
per-channel descriptor kick-off (`apb4todescr`, 0x000-0x03F) and the `rapids_regs`
register block (base config at 0x100-0x3FF, monitor regfile at 0x1000).
`rapids_config_block` translates the register `hwif_out` into the core/monitor
`cfg_*` signals.

When `USE_AXI_MONITORS = 1`, AXI transaction monitors observe the read and write
data masters; their packets are merged with the core descriptor-monitor packet
by a `monbus_arbiter` and delivered through a `monbus_axil_axil_group` to an
AXI-Lite error-drain slave, an AXI-Lite capture master, and a `mon_irq`
interrupt.

```mermaid
graph TB
    APB["APB4 Slave<br/>s_apb_*"] --> ROUTER["cmdrsp_router"]
    ROUTER -->|"0x000-0x03F"| KICK["apb4todescr<br/>(descriptor kick-off)"]
    ROUTER -->|"0x100+ / 0x1000"| REGS["rapids_regs<br/>(base + MON regfile)"]
    REGS --> CFG["rapids_config_block<br/>(hwif_out -> cfg_*)"]
    KICK --> CORE["rapids_core_beats"]
    CFG --> CORE

    CORE -->|"m_axi_rd"| RDMON["axi4_master_rd_mon"]
    CORE -->|"m_axi_wr"| WRMON["axi4_master_wr_mon"]
    RDMON --> MRD["m_axi_rd"]
    WRMON --> MWR["m_axi_wr"]

    CORE -->|"desc mon pkt"| ARB["monbus_arbiter (3:1)"]
    RDMON --> ARB
    WRMON --> ARB
    ARB --> GRP["monbus_axil_axil_group"]
    GRP --> ERR["s_axil_err_*<br/>(error drain)"]
    GRP --> CAP["m_axil_mon_*<br/>(capture master)"]
    GRP --> IRQ["mon_irq"]

    style CORE fill:#e3f2fd
    style REGS fill:#fff9c4
    style GRP fill:#ffccbc
```

## Component Summary

### Scheduler Group Array

The scheduler group array manages 8 independent channels:

| Component | Instance Count | Purpose |
|-----------|----------------|---------|
| `scheduler_beats` | 8 | Transfer coordination per channel |
| `descriptor_engine_beats` | 8 | Descriptor fetch and parse |
| Descriptor AXI Arbiter | 1 | Shared AXI4 for descriptor fetch |

: Scheduler Array Components

### Sink Data Path

Network-to-memory data flow:

| Component | Purpose |
|-----------|---------|
| `snk_sram_controller_beats` | Multi-channel SRAM management |
| `axi_write_engine_beats` | AXI4 burst write generation |
| `alloc_ctrl_beats` | Space allocation tracking |
| `drain_ctrl_beats` | Data availability tracking |

: Sink Path Components

### Source Data Path

Memory-to-network data flow:

| Component | Purpose |
|-----------|---------|
| `axi_read_engine_beats` | AXI4 burst read generation |
| `src_sram_controller_beats` | Multi-channel SRAM management |
| `alloc_ctrl_beats` | Space allocation tracking |
| `drain_ctrl_beats` | Data availability tracking |

: Source Path Components

## Hierarchy

```
rapids_core_beats
├── beats_scheduler_group_array
│   ├── beats_scheduler_group [0]
│   │   ├── scheduler_beats
│   │   └── descriptor_engine_beats
│   ├── beats_scheduler_group [1..6]
│   │   └── ...
│   └── beats_scheduler_group [7]
│       └── ...
├── sink_data_path_beats
│   ├── snk_sram_controller_beats
│   │   └── snk_sram_controller_unit_beats [0..7]
│   ├── axi_write_engine_beats
│   ├── alloc_ctrl_beats
│   └── drain_ctrl_beats
└── source_data_path_beats
    ├── axi_read_engine_beats
    ├── src_sram_controller_beats
    │   └── src_sram_controller_unit_beats [0..7]
    ├── alloc_ctrl_beats
    └── drain_ctrl_beats
```

## Internal Buses

| Bus | Width | Description |
|-----|-------|-------------|
| Descriptor Bus | 256-bit | Parsed descriptor to scheduler |
| Scheduler Command | Variable | Transfer parameters to data paths |
| SRAM Data | 512-bit | Data to/from SRAM buffers |
| MonBus | 64-bit | Monitor packets (aggregated) |

: Internal Bus Summary
