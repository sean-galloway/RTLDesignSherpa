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

# Clock and Reset

## Clock Interface

### Signal Definition

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `pclk` | 1 | Input | APB clock |

: Clock Signal

### Clock Requirements

**Single Clock Domain:**
- All crossbar logic operates on pclk rising edge
- All APB signals sampled/driven synchronous to pclk
- No internal clock generation or division

**Frequency:**
- No minimum frequency requirement
- Maximum frequency determined by critical path
- Typical: 100-250 MHz (depends on target technology)

**Duty Cycle:**
- No specific duty cycle requirement
- Standard 50% duty cycle recommended

## Reset Interface

### Signal Definition

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `presetn` | 1 | Input | Active-low asynchronous reset |

: Reset Signal

### Reset Behavior

**Assertion (presetn goes low):**
- All internal state cleared immediately
- All output signals driven to safe values
- Master ports: PREADY=1, PRDATA=0, PSLVERR=0
- Slave ports: PSEL=0, PENABLE=0, PADDR=0, etc.

**Deassertion (presetn goes high):**
- Internal state begins normal operation
- Reset release synchronized to pclk internally
- Ready to accept transactions immediately

### Reset Safe Values

| Signal Group | Reset Value | Rationale |
|--------------|-------------|-----------|
| Master PREADY | 1 | No false wait states |
| Master PRDATA | 0 | No false data |
| Master PSLVERR | 0 | No false errors |
| Slave PSEL | 0 | No false transactions |
| Slave PENABLE | 0 | No false enables |
| Arbiter grants | 0 | No master selected |

: Reset Safe Values

## Clock-Reset Relationship

### Reset Assertion

Reset can be asserted at any time:
- Asynchronous assertion (immediate effect)
- Synchronous or asynchronous deassertion
- All in-flight transactions aborted

### Reset Deassertion

For clean operation:
1. Assert reset for minimum 2 pclk cycles
2. Deassert reset synchronous to pclk rising edge
3. Wait 1 cycle before first transaction

### Reset Sequence Diagram

```
pclk      _|~|_|~|_|~|_|~|_|~|_|~|_|~|_

presetn   ________|~~~~~~~~~~~~~~~~

Internal  xxxxxxxx|--- Valid State --
State

Ready for ________|--- Transactions --
Traffic
```

## Integration Notes

### Clock Domain Crossing

If masters or slaves are in different clock domains:
- Insert appropriate CDC logic external to crossbar
- Crossbar assumes single clock domain
- Consider APB clock bridge if needed

### Clock Gating

The crossbar supports clock gating:
- No internal activity when idle
- Safe to gate pclk when no transactions pending
- All registers use standard flip-flops (no clock gating cells)

---

**Next:** [Chapter 5: Performance](../ch05_performance/01_throughput.md)
