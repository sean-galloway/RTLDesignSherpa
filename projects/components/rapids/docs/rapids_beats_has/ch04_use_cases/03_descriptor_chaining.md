# Use Case: Descriptor Chaining

## Overview

Descriptor chaining enables multiple transfers to execute sequentially without software intervention. Each descriptor contains a pointer to the next descriptor, forming a linked list that RAPIDS processes automatically.

## Chain Structure

![Descriptor Chain](../assets/mermaid/11_descriptor_chain.png)

**Source:** [11_descriptor_chain.mmd](../assets/mermaid/11_descriptor_chain.mmd)

```mermaid
graph LR
    subgraph Memory["System Memory"]
        DESC0["Descriptor 0<br/>next_ptr → DESC1"]
        DESC1["Descriptor 1<br/>next_ptr → DESC2"]
        DESC2["Descriptor 2<br/>next_ptr → 0"]

        BUF0["Buffer 0"]
        BUF1["Buffer 1"]
        BUF2["Buffer 2"]
    end

    subgraph RAPIDS["RAPIDS Beats"]
        SCHED["Scheduler"]
        DESC_ENG["Descriptor<br/>Engine"]
    end

    DESC0 --> DESC1
    DESC1 --> DESC2

    DESC0 -.-> BUF0
    DESC1 -.-> BUF1
    DESC2 -.-> BUF2

    DESC_ENG --> DESC0

    style DESC0 fill:#e3f2fd
    style DESC1 fill:#e3f2fd
    style DESC2 fill:#e3f2fd
```

## Chain Execution Flow

```mermaid
sequenceDiagram
    participant SW as Software
    participant DESC as Descriptor Engine
    participant SCHED as Scheduler
    participant DP as Data Path
    participant MEM as Memory

    SW->>DESC: Write base pointer
    SW->>SCHED: Kick channel

    rect rgb(230, 240, 255)
    Note over DESC,MEM: Descriptor 0
    DESC->>MEM: Fetch DESC0
    MEM-->>DESC: DESC0 data
    DESC-->>SCHED: Valid, next_ptr=DESC1
    SCHED->>DP: Execute transfer 0
    DP-->>SCHED: Done
    end

    rect rgb(230, 255, 240)
    Note over DESC,MEM: Descriptor 1
    DESC->>MEM: Fetch DESC1
    MEM-->>DESC: DESC1 data
    DESC-->>SCHED: Valid, next_ptr=DESC2
    SCHED->>DP: Execute transfer 1
    DP-->>SCHED: Done
    end

    rect rgb(255, 240, 230)
    Note over DESC,MEM: Descriptor 2 (Last)
    DESC->>MEM: Fetch DESC2
    MEM-->>DESC: DESC2 data
    DESC-->>SCHED: Valid, next_ptr=0, LAST=1
    SCHED->>DP: Execute transfer 2
    DP-->>SCHED: Done
    end

    SCHED-->>SW: Chain complete (interrupt)
```

## Timing Diagram

![Chain Execution](../assets/wavedrom/chain_execution.svg)

**Source:** [chain_execution.json](../assets/wavedrom/chain_execution.json)

```wavedrom
{
  "signal": [
    {"name": "clk", "wave": "p.........|.........|.........|...."},
    {},
    ["Descriptor 0",
      {"name": "desc_fetch[0]", "wave": "01.0......|..........|..........|...."},
      {"name": "desc_valid[0]", "wave": "0..1.0....|..........|..........|...."},
      {"name": "xfer_active[0]", "wave": "0...1...0.|..........|..........|...."}
    ],
    {},
    ["Descriptor 1",
      {"name": "desc_fetch[1]", "wave": "0.........|1.0.......|..........|...."},
      {"name": "desc_valid[1]", "wave": "0.........|..1.0.....|..........|...."},
      {"name": "xfer_active[1]", "wave": "0.........|...1...0..|..........|...."}
    ],
    {},
    ["Descriptor 2",
      {"name": "desc_fetch[2]", "wave": "0.........|..........|1.0.......|...."},
      {"name": "desc_valid[2]", "wave": "0.........|..........|..1.0.....|...."},
      {"name": "xfer_active[2]", "wave": "0.........|..........|...1...0..|...."},
      {"name": "last_desc", "wave": "0.........|..........|..1.......|0..."}
    ],
    {},
    {"name": "chain_complete", "wave": "0.........|..........|........1.|0..."},
    {"name": "channel_idle", "wave": "1.0.......|..........|..........|.1.."}
  ],
  "config": {"hscale": 1},
  "head": {"text": "Three-Descriptor Chain Execution"}
}
```

## Descriptor Fields for Chaining

### Relevant Fields

| Field | Bits | Description |
|-------|------|-------------|
| `next_ptr` | [191:128] | 64-bit pointer to next descriptor |
| `last` | [255] | Last descriptor in chain flag |
| `irq_en` | [254] | Generate interrupt on completion |

: Chaining-Related Descriptor Fields

### Chain Termination

A chain terminates when ANY of these conditions is true:

1. `next_ptr == 0` (null pointer)
2. `last == 1` (explicit last flag)
3. Error during transfer

```mermaid
stateDiagram-v2
    [*] --> FETCH: Chain started

    FETCH --> PARSE: Descriptor fetched
    PARSE --> EXECUTE: Valid descriptor

    EXECUTE --> CHECK_NEXT: Transfer complete

    CHECK_NEXT --> FETCH: next_ptr != 0 && !last
    CHECK_NEXT --> COMPLETE: next_ptr == 0 || last
    CHECK_NEXT --> ERROR: Transfer error

    COMPLETE --> [*]: Chain done
    ERROR --> [*]: Chain aborted
```

## Prefetch Optimization

### Descriptor Prefetching

RAPIDS can prefetch the next descriptor while the current transfer executes:

```wavedrom
{
  "signal": [
    {"name": "clk", "wave": "p.............|.........."},
    {},
    ["Current Descriptor",
      {"name": "xfer_active", "wave": "01........0...|.........."},
      {"name": "xfer_progress", "wave": "x=.=.=.=.=.x..|..........", "data": ["0%","25%","50%","75%","100%"]}
    ],
    {},
    ["Next Descriptor (Prefetch)",
      {"name": "prefetch_en", "wave": "01.0..........|.........."},
      {"name": "prefetch_done", "wave": "0...1.........|.........."},
      {"name": "next_desc_ready", "wave": "0...1.......0.|.........."}
    ],
    {},
    ["Chain Progress",
      {"name": "desc_index", "wave": "=.........=...|..........", "data": ["N","N+1"]},
      {"name": "chain_gap", "wave": "x.........=...|..........", "data": ["0 cycles"]}
    ]
  ],
  "config": {"hscale": 1},
  "head": {"text": "Zero-Gap Descriptor Prefetch"}
}
```

**Benefit:** Zero-cycle gap between chained transfers when prefetch completes before current transfer.

## Multi-Channel Chaining

Each channel maintains independent chains:

```mermaid
graph TB
    subgraph CH0["Channel 0 Chain"]
        D0_0["DESC 0.0"] --> D0_1["DESC 0.1"] --> D0_2["DESC 0.2"]
    end

    subgraph CH1["Channel 1 Chain"]
        D1_0["DESC 1.0"] --> D1_1["DESC 1.1"]
    end

    subgraph CH2["Channel 2 Chain"]
        D2_0["DESC 2.0"] --> D2_1["DESC 2.1"] --> D2_2["DESC 2.2"] --> D2_3["DESC 2.3"]
    end

    style CH0 fill:#e3f2fd
    style CH1 fill:#e8f5e9
    style CH2 fill:#fff3e0
```

Channels execute their chains concurrently and independently.

## Error During Chain

### Error Handling

When an error occurs mid-chain:

```wavedrom
{
  "signal": [
    {"name": "clk", "wave": "p.........|....."},
    {},
    {"name": "desc_index", "wave": "=.=.=.....|.....", "data": ["0","1","2"]},
    {"name": "xfer_active", "wave": "01.01.01..|0...."},
    {},
    {"name": "axi_error", "wave": "0.....1...|0...."},
    {"name": "chain_abort", "wave": "0......1..|0...."},
    {"name": "error_desc_idx", "wave": "x......=..|x....", "data": ["2"]},
    {},
    {"name": "irq_error", "wave": "0.......1.|0...."}
  ],
  "config": {"hscale": 1.5},
  "head": {"text": "Chain Abort on AXI Error"}
}
```

**Error Response:**
1. Current transfer aborts
2. Chain processing stops
3. Error status captures failing descriptor index
4. MonBus reports error event
5. Interrupt generated (if enabled)

### Recovery

Software must:
1. Read error status to identify failing descriptor
2. Fix the issue (descriptor content, memory mapping, etc.)
3. Restart chain from failing descriptor or beginning

