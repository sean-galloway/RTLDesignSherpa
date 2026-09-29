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

## Feature Summary

| Feature | Specification |
|---------|---------------|
| **Channels** | 8 independent channels |
| **Descriptor Size** | 256 bits (32 bytes) |
| **Data Width** | Parameterizable (default 512 bits) |
| **Address Width** | 64 bits |
| **Maximum Burst** | 256 beats (AXI4) |
| **Chaining** | Unlimited descriptor chain depth |
| **Arbitration** | Priority-based with round-robin |

---

## Descriptor-Based Operation

### Single-Write Kick-off

A single APB write to a channel's control register initiates an entire transfer sequence:

1. Write descriptor address to `CHn_CTRL` register
2. STREAM automatically fetches and processes descriptor
3. Chained descriptors processed without software intervention
4. Completion indicated via status register and optional interrupt

### Autonomous Chaining

STREAM follows `next_descriptor_ptr` automatically:

- **Non-zero pointer**: Fetch next descriptor, continue processing
- **Zero pointer**: Chain complete, transition to idle
- **Last flag**: Explicit chain termination regardless of pointer

---

## Multi-Channel Architecture

### Channel Independence

Each channel maintains:

- Independent FSM state
- Separate descriptor chain pointer
- Individual error status
- Private completion interrupt

### Resource Sharing

All channels share:

- Descriptor fetch AXI master
- Data read AXI master
- Data write AXI master
- Internal SRAM buffer
- MonBus reporter

### Priority-Based Arbitration

- 8-bit priority field in each descriptor
- Higher priority descriptors serviced first
- Round-robin within same priority level
- Anti-starvation timeout mechanism

---

## Data Path Features

### Parameterizable Data Width

Compile-time configurable data width:

| Parameter | Description | Typical Values |
|-----------|-------------|----------------|
| `DATA_WIDTH` | AXI data bus width | 128, 256, 512 bits |
| `SRAM_DEPTH` | Internal buffer depth | 1024, 2048, 4096 entries |

### Aligned Address Requirement

**[CONST-1]** All source and destination addresses must be aligned to data width.

| Data Width | Alignment Requirement |
|------------|----------------------|
| 128 bits | 16-byte aligned |
| 256 bits | 32-byte aligned |
| 512 bits | 64-byte aligned |

This simplification eliminates complex alignment fixup logic for tutorial clarity.

---

## Monitoring and Debug

### MonBus Integration

64-bit monitor packets for:

- Transfer initiation events
- Descriptor fetch events
- Transfer completion events
- Error condition reporting
- Performance metrics

### Status Visibility

APB-readable status registers provide:

- Channel state (idle, active, error)
- Descriptor count per channel
- Error codes and flags
- Performance counters (optional)

---

## Error Handling

### Error Detection

| Error Type | Detection | Response |
|------------|-----------|----------|
| AXI read error | RRESP != OKAY | Stop chain, set error flag |
| AXI write error | BRESP != OKAY | Stop chain, set error flag |
| Invalid descriptor | Validation failure | Stop chain, set error flag |
| Address out of range | Limit check | Stop chain, set error flag |

### Error Isolation

Errors in one channel do not affect other channels. Each channel has independent error status and recovery.

---

**Last Updated:** 2026-01-03
