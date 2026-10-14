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

# Use Case: Descriptor Chaining

## Overview

Descriptor chaining enables multiple transfers to execute sequentially without software intervention. Each descriptor contains a pointer to the next descriptor, forming a linked list that RAPIDS processes automatically.

## Chain Structure

### Figure 4.3.1: Descriptor Chain Structure

![Descriptor Chain Structure](../assets/graphviz/ch04_chain_structure.png)

**Source:** [ch04_chain_structure.dot](../assets/graphviz/ch04_chain_structure.dot)

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

Prefetch depth is controlled by `DESCENG_CONFIG.PREFETCH_EN` and
`DESCENG_CONFIG.FIFO_THRESH` (register block, offset 0x220). With prefetch
disabled the descriptor engine fetches on demand (roughly one descriptor ahead
of the scheduler); with prefetch enabled it buffers up to `FIFO_THRESH`
descriptors ahead. A chain fetch that is throttled (output FIFO at the threshold)
is deferred and reissued automatically once the FIFO drains, so no chain link is
lost.

## Multi-Channel Chaining

Each channel maintains independent chains:

### Figure 4.3.2: Independent Per-Channel Chains

![Independent Per-Channel Chains](../assets/graphviz/ch04_multichannel_chains.png)

**Source:** [ch04_multichannel_chains.dot](../assets/graphviz/ch04_multichannel_chains.dot)

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
