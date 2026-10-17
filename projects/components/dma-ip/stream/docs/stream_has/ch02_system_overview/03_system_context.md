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

# System Context

## System Integration Overview

STREAM integrates into a typical SoC as a peripheral subsystem with the following connections:

### Figure 2.3.1: System Context

![System Context](../assets/graphviz/ch02_system_context.png)

**Source:** [ch02_system_context.dot](../assets/graphviz/ch02_system_context.dot)

---

## External Connections

### Configuration Path

| Connection | Protocol | Description |
|------------|----------|-------------|
| APB Slave | APB3/APB4 | Configuration and control interface |

**Functions:**
- Channel kick-off (write descriptor address)
- Status monitoring
- Interrupt control
- Error handling

### Data Paths

| Connection | Protocol | Width | Description |
|------------|----------|-------|-------------|
| Descriptor Master | AXI4 | 256-bit | Fetch descriptors from memory |
| Read Data Master | AXI4 | Param | Read source data from memory |
| Write Data Master | AXI4 | Param | Write destination data to memory |

### Monitoring Path

| Connection | Protocol | Width | Description |
|------------|----------|-------|-------------|
| MonBus Master | MonBus | 64-bit | Debug/trace packet output |

---

## Clock and Reset

### Clock Domain

STREAM operates in a single clock domain:

| Signal | Description |
|--------|-------------|
| `aclk` | Primary system clock, all interfaces synchronous |
| `aresetn` | Active-low asynchronous reset |

**[INTEG-1]** All external interfaces must be synchronous to `aclk`.

### Reset Requirements

- Asynchronous assertion, synchronous de-assertion
- Minimum reset pulse width: 2 clock cycles
- All state machines return to idle on reset
- SRAM contents undefined after reset

---

## Memory Map Requirements

### Descriptor Memory

Descriptors must be placed in memory accessible via the descriptor fetch AXI master:

- **Alignment:** 32-byte aligned (256-bit descriptor size)
- **Accessibility:** Read access required
- **Coherency:** Software must ensure descriptors are coherent before kick-off

### Data Memory

Source and destination regions must be accessible via the appropriate AXI master:

- **Source:** Read access via read data master
- **Destination:** Write access via write data master
- **Alignment:** Per data width (see Key Features)

---

## Interrupt Integration

### Interrupt Signals

| Signal | Description |
|--------|-------------|
| `stream_irq` | The single interrupt output: the error/interrupt FIFO of `monbus_axil4_axil4_group` is not empty. Tied to 0 when `USE_AXI_MONITORS = 0` |

: Interrupt Signals

There is no per-channel interrupt vector, at 8 or at 16 channels.

### Interrupt Conditions

- A MonBus packet the group classifies as an error or interrupt (for example a
  descriptor completion with the descriptor's `interrupt` flag, or a channel
  error) is pushed into the error FIFO, which raises `stream_irq`
- Software reads the FIFO through `s_axil_err` to find the channel and cause,
  and the interrupt drops when the FIFO is empty
- Per-channel completion is also visible by polling `AXI_RD_COMPLETE`,
  `AXI_WR_COMPLETE` and `CHANNEL_IDLE`

---

## Power Considerations

### Clock Gating

STREAM supports clock gating when all channels are idle:

- Monitor `all_channels_idle` status bit
- External clock gate can disable `aclk` when idle
- Re-enable clock before writing kick-off register

### Power States

| State | Channels | Clock | Power |
|-------|----------|-------|-------|
| Active | >= 1 busy | Running | Full |
| Idle | All idle | Running | Reduced (no switching) |
| Gated | All idle | Stopped | Minimal (leakage only) |

---

**Last Updated:** 2026-01-03
