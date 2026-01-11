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

# Architecture Overview

**Module:** `rapids_core_beats.sv`
**Location:** `projects/components/rapids/rtl/macro_beats/`
**Status:** Implemented
**Last Updated:** 2025-01-10

---

## Overview

The RAPIDS "Beats" architecture is a Phase 1 implementation providing network-to-memory and memory-to-network data transfer capabilities. The name "beats" reflects the design decision to track all transfers at beat granularity (data-width units) for simplified flow control.

### Key Features

- **8 Independent Channels:** Each channel has its own descriptor chain and SRAM allocation
- **Separate Data Paths:** Sink (network-to-memory) and source (memory-to-network) paths
- **Beat-Level Tracking:** All flow control operates at beat granularity
- **SRAM Buffering:** Separate sink and source SRAM buffers for data staging
- **MonBus Integration:** Comprehensive monitoring for all subsystems
- **Streaming Pipelines:** No FSM in data engines - pure streaming for maximum throughput

### Block Diagram

### Figure 1.1.1: RAPIDS Beats Architecture Block Diagram

```
                              rapids_core_beats
    +-------------------------------------------------------------------------+
    |                                                                         |
    |  +-------------------------------------------------------------------+  |
    |  |              beats_scheduler_group_array (8 channels)             |  |
    |  |  +----------------+  +----------------+       +----------------+  |  |
    |  |  | scheduler_grp  |  | scheduler_grp  |  ...  | scheduler_grp  |  |  |
    |  |  |    [0]         |  |    [1]         |       |    [7]         |  |  |
    |  |  +----------------+  +----------------+       +----------------+  |  |
    |  |         |                   |                        |           |  |
    |  |         v                   v                        v           |  |
    |  |  +----------------------------------------------------------+    |  |
    |  |  |           Shared Descriptor AXI Master                   |    |  |
    |  |  |              (Round-Robin Arbitration)                   |    |  |
    |  |  +----------------------------------------------------------+    |  |
    |  +-------------------------------------------------------------------+  |
    |         |                                              |                |
    |         v                                              v                |
    |  +--------------------+                    +------------------------+   |
    |  |   SINK DATA PATH   |                    |   SOURCE DATA PATH     |   |
    |  | (Network -> Memory)|                    | (Memory -> Network)    |   |
    |  |                    |                    |                        |   |
    |  |  Fill Interface    |                    |  Drain Interface       |   |
    |  |       |            |                    |        ^               |   |
    |  |       v            |                    |        |               |   |
    |  |  snk_sram_ctrl     |                    |  src_sram_ctrl         |   |
    |  |       |            |                    |        ^               |   |
    |  |       v            |                    |        |               |   |
    |  |  axi_write_engine  |                    |  axi_read_engine       |   |
    |  |       |            |                    |        ^               |   |
    |  +-------|------------+                    +--------|---------------+   |
    |          v                                          |                   |
    +----------|------------------------------------------|-----------------+
               |                                          |
               v                                          |
        AXI Write Master                           AXI Read Master
        (to System Memory)                         (from System Memory)
```

**Source:** [01_architecture_block.mmd](../assets/mermaid/01_architecture_block.mmd)

---

## Data Flow Overview

### Sink Path (Network to Memory)

The sink path receives data from an external source (via Fill interface) and writes it to system memory:

### Figure 1.1.2: Sink Path Data Flow

```
1. External Fill Valid
        |
        v
2. beats_alloc_ctrl (Space Allocation)
        |
        v
3. snk_sram_controller_unit (SRAM Write)
        |
        v
4. beats_drain_ctrl (Data Available)
        |
        v
5. axi_write_engine (AXI Burst Write)
        |
        v
6. System Memory
```

**Source:** [01_sink_path_flow.mmd](../assets/mermaid/01_sink_path_flow.mmd)

### Source Path (Memory to Network)

The source path reads data from system memory and sends it to an external destination (via Drain interface):

### Figure 1.1.3: Source Path Data Flow

```
1. Scheduler Request
        |
        v
2. beats_alloc_ctrl (Space Allocation)
        |
        v
3. axi_read_engine (AXI Burst Read)
        |
        v
4. src_sram_controller_unit (SRAM Write)
        |
        v
5. beats_drain_ctrl (Data Available)
        |
        v
6. External Drain Ready
```

**Source:** [01_source_path_flow.mmd](../assets/mermaid/01_source_path_flow.mmd)

---

## Key Architectural Decisions

### Beat-Level Tracking

All flow control uses beat granularity:

| Operation | Granularity | Example (512-bit DW) |
|-----------|-------------|----------------------|
| Space allocation | Beats | Request 8 beats = 512 bytes |
| Data availability | Beats | 16 beats ready = 1024 bytes |
| AXI burst length | Beats | ARLEN=15 = 16 beats |
| Latency compensation | Beats | 2-beat pipeline delay |

: Table 1.1.1: Beat Granularity Examples

### Concurrent Read/Write

To prevent deadlock with large transfers:

```
Example: 100MB transfer with 2KB SRAM buffer

Sequential operation (WRONG):
1. Read 100MB -> DEADLOCK at 2KB (SRAM full, can't complete read)

Concurrent operation (CORRECT):
1. Read starts filling SRAM -> SRAM becomes full (2KB)
2. Read pauses (natural backpressure)
3. Write drains SRAM -> SRAM has free space
4. Read resumes -> Both continue until 100MB complete
```

### Virtual FIFOs (Alloc/Drain)

The alloc_ctrl and drain_ctrl modules are "virtual FIFOs" that track space/data without storing actual data:

- **beats_alloc_ctrl:** Tracks allocated space (write pointer advances on allocation, read pointer on actual write)
- **beats_drain_ctrl:** Tracks available data (write pointer advances on data arrival, read pointer on drain)

---

## Module Hierarchy

```
rapids_core_beats
├── beats_scheduler_group_array
│   ├── beats_scheduler_group [0..7]
│   │   ├── descriptor_engine
│   │   └── scheduler
│   └── Shared Descriptor AXI Master
│
├── sink_data_path
│   ├── snk_sram_controller
│   │   └── snk_sram_controller_unit [0..7]
│   │       ├── beats_alloc_ctrl
│   │       ├── simple_sram
│   │       └── beats_drain_ctrl
│   └── axi_write_engine
│       └── beats_latency_bridge
│
└── source_data_path
    ├── axi_read_engine
    │   └── beats_latency_bridge
    └── src_sram_controller
        └── src_sram_controller_unit [0..7]
            ├── beats_alloc_ctrl
            ├── simple_sram
            └── beats_drain_ctrl
```

---

## Timing Diagram: Basic Transfer

### Figure 1.1.4: Basic Sink Path Transfer Timing

```
              ____    ____    ____    ____    ____    ____    ____
    clk      |    |__|    |__|    |__|    |__|    |__|    |__|    |__
                    :       :       :       :       :       :
    fill_valid     _/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\_____
                    :       :       :       :       :       :
    fill_ready     ‾\_______/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\_______/‾‾‾‾‾
                    :  [1]  :       :       :       :  [2]  :
    fill_data      X|==D0===|==D1===|==D2===|==D3===|=====XX|XXXXX
                    :       :       :       :       :       :
    sram_wr_en     _________/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\____________
                    :       :       :       :       :       :
    data_avail     ___/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\____
                    :       :       :       :       :       :

    [1] = fill_ready deasserted (SRAM full or allocation pending)
    [2] = fill_ready deasserted (end of burst)
```

**TODO:** Replace with simulation-generated waveform showing actual signals

---

## Related Documentation

- **[Top-Level Port List](02_port_list.md)** - Complete port specification
- **[Clocks and Reset](03_clocks_and_reset.md)** - Timing requirements
- **[Beats Scheduler Group](../ch03_macro_blocks/01_beats_scheduler_group.md)** - Scheduler integration
- **[Sink Data Path](../ch03_macro_blocks/03_sink_data_path.md)** - Sink path details

---

**Last Updated:** 2025-01-10
