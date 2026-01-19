# Channel Architecture

## Multi-Channel Design

RAPIDS Beats supports 8 independent DMA channels, each with dedicated resources for concurrent operation.

## Channel Resource Allocation

![Channel Architecture](../assets/mermaid/07_channel_arch.png)

**Source:** [07_channel_arch.mmd](../assets/mermaid/07_channel_arch.mmd)

```mermaid
graph TB
    subgraph CH["Per-Channel Resources (x8)"]
        SCHED["Scheduler<br/>FSM"]
        DESC["Descriptor<br/>Engine"]
        SNK_UNIT["Sink SRAM<br/>Unit"]
        SRC_UNIT["Source SRAM<br/>Unit"]
    end

    subgraph SHARED["Shared Resources"]
        DESC_AXI["Descriptor<br/>AXI Arbiter"]
        SNK_AXI["Sink AXI<br/>Write Engine"]
        SRC_AXI["Source AXI<br/>Read Engine"]
        MONBUS_ARB["MonBus<br/>Arbiter"]
    end

    SCHED --> DESC
    DESC --> DESC_AXI

    SCHED --> SNK_UNIT
    SCHED --> SRC_UNIT

    SNK_UNIT --> SNK_AXI
    SRC_UNIT --> SRC_AXI

    CH --> MONBUS_ARB

    style CH fill:#e8f5e9
    style SHARED fill:#fff3e0
```

## Per-Channel Resources

Each channel has dedicated:

| Resource | Description | Size/Capacity |
|----------|-------------|---------------|
| **Scheduler** | Transfer coordination FSM | 1 instance |
| **Descriptor Engine** | Descriptor fetch/parse | 8-deep FIFO |
| **Sink SRAM Unit** | Sink buffer partition | SRAM_DEPTH/8 entries |
| **Source SRAM Unit** | Source buffer partition | SRAM_DEPTH/8 entries |
| **Configuration Registers** | Per-channel config | ~16 registers |

: Per-Channel Resources

## Shared Resources

Resources shared across all channels:

| Resource | Arbitration | Max Outstanding |
|----------|-------------|-----------------|
| **Descriptor AXI** | Round-robin | 8 (1 per channel) |
| **Sink AXI Write** | Round-robin | 8 configurable |
| **Source AXI Read** | Round-robin | 8 configurable |
| **MonBus Output** | Priority | 1 (serialized) |

: Shared Resources

## Channel Scheduling

### Arbitration Policy

```mermaid
graph LR
    subgraph Channels["Channel Requests"]
        CH0["CH0 req"]
        CH1["CH1 req"]
        CH2["CH2 req"]
        CHN["..."]
        CH7["CH7 req"]
    end

    ARB["Round-Robin<br/>Arbiter"]

    CH0 --> ARB
    CH1 --> ARB
    CH2 --> ARB
    CHN --> ARB
    CH7 --> ARB

    ARB --> GRANT["Grant"]
```

**Arbitration Timing:**

![Channel Arbitration](../assets/wavedrom/channel_arbitration.svg)

**Source:** [channel_arbitration.json](../assets/wavedrom/channel_arbitration.json)

```wavedrom
{
  "signal": [
    {"name": "clk", "wave": "p.........."},
    {},
    {"name": "ch0_req", "wave": "0.1........"},
    {"name": "ch1_req", "wave": "0..1......."},
    {"name": "ch2_req", "wave": "0...1......"},
    {},
    {"name": "grant", "wave": "x.0.1.2....", "data": ["CH0","CH1","CH2"]},
    {"name": "grant_valid", "wave": "0.1........"}
  ],
  "config": {"hscale": 1.5},
  "head": {"text": "Round-Robin Channel Arbitration"}
}
```

## Channel State Machine

Each channel scheduler follows this state machine:

![Channel FSM](../assets/mermaid/08_channel_fsm.png)

**Source:** [08_channel_fsm.mmd](../assets/mermaid/08_channel_fsm.mmd)

```mermaid
stateDiagram-v2
    [*] --> IDLE: Reset

    IDLE --> WAIT_DESC: apb_valid
    WAIT_DESC --> PARSE_DESC: descriptor_valid
    PARSE_DESC --> CH_XFER_DATA: Valid descriptor

    CH_XFER_DATA --> CH_XFER_DATA: Transfer in progress
    CH_XFER_DATA --> CHECK_NEXT: rd_done && wr_done

    CHECK_NEXT --> WAIT_DESC: next_ptr valid
    CHECK_NEXT --> COMPLETE: last || next_ptr=0

    COMPLETE --> IDLE: Done

    state CH_XFER_DATA {
        [*] --> CONCURRENT
        CONCURRENT: Read & Write run concurrently
        note right of CONCURRENT: Prevents deadlock when<br/>transfer > buffer size
    }
```

### Channel State Timing

![Channel State Timing](../assets/wavedrom/channel_state_timing.svg)

**Source:** [channel_state_timing.json](../assets/wavedrom/channel_state_timing.json)

```wavedrom
{
  "signal": [
    {"name": "clk", "wave": "p..............|..."},
    {},
    {"name": "apb_valid", "wave": "01.0...........|..."},
    {"name": "state", "wave": "=.=..=.=.......|=..", "data": ["IDLE","WAIT","PARSE","XFER","COMPLETE"]},
    {},
    {"name": "descriptor_valid", "wave": "0..1.0.........|..."},
    {"name": "sched_rd_valid", "wave": "0.....1........|0.."},
    {"name": "sched_wr_valid", "wave": "0.....1........|0.."},
    {},
    {"name": "sched_rd_done", "wave": "0..............|1.0"},
    {"name": "sched_wr_done", "wave": "0..............1|..0"},
    {"name": "channel_idle", "wave": "1..0...........|..1"}
  ],
  "config": {"hscale": 1},
  "head": {"text": "Single Descriptor Transfer Sequence"}
}
```

## Channel Isolation

Channels are isolated to prevent interference:

| Isolation Type | Implementation |
|----------------|----------------|
| **State Isolation** | Separate FSM per channel |
| **Buffer Isolation** | Partitioned SRAM per channel |
| **Error Isolation** | Per-channel error flags |
| **Reset Isolation** | Per-channel soft reset |

: Channel Isolation Features

### Per-Channel Error Handling

Each channel maintains independent error state:

```wavedrom
{
  "signal": [
    {"name": "clk", "wave": "p........"},
    {},
    {"name": "ch0_error", "wave": "0........"},
    {"name": "ch1_error", "wave": "0...1...."},
    {"name": "ch2_error", "wave": "0........"},
    {},
    {"name": "ch1_state", "wave": "=...=....", "data": ["XFER","ERROR"]},
    {"name": "ch0_state", "wave": "=........", "data": ["XFER"]},
    {"name": "ch2_state", "wave": "=........", "data": ["IDLE"]}
  ],
  "config": {"hscale": 1.5},
  "head": {"text": "Channel Error Isolation"}
}
```

Channel 1 error does not affect Channel 0 or Channel 2 operation.
