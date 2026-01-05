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

# Slave-Side APB Interfaces

## Interface Overview

Each slave port provides a complete APB master interface to drive transactions to an external APB slave (peripheral).

## Signal Definition

For each slave index `j` (0 to N-1):

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `s<j>_apb_PSEL` | 1 | Output | Peripheral select |
| `s<j>_apb_PENABLE` | 1 | Output | Transfer enable |
| `s<j>_apb_PADDR` | ADDR_WIDTH | Output | Address bus |
| `s<j>_apb_PWRITE` | 1 | Output | Write/read direction |
| `s<j>_apb_PWDATA` | DATA_WIDTH | Output | Write data bus |
| `s<j>_apb_PSTRB` | STRB_WIDTH | Output | Write strobes |
| `s<j>_apb_PPROT` | 3 | Output | Protection attributes |
| `s<j>_apb_PRDATA` | DATA_WIDTH | Input | Read data bus |
| `s<j>_apb_PSLVERR` | 1 | Input | Slave error response |
| `s<j>_apb_PREADY` | 1 | Input | Transfer ready |

: Slave Port Signal Definition

## Signal Behavior

### Output Signals (Crossbar to Slave)

**PSEL:** Asserted when a transaction targets this slave. Remains high throughout the transaction.

**PENABLE:** Follows standard APB timing:
- Low during setup phase
- High during access phase

**PADDR:** Contains the full address from the master. The local address within the 64KB region is in bits [15:0].

**PWRITE, PWDATA, PSTRB, PPROT:** Passed through from the winning master without modification.

### Input Signals (Slave to Crossbar)

**PRDATA:** Captured by crossbar when both PREADY and PENABLE are high. Routed to originating master.

**PSLVERR:** Captured with PRDATA. Propagated to originating master as error indication.

**PREADY:** Controls transaction completion:
- PREADY=1: Transaction completes this cycle
- PREADY=0: Insert wait states

## Slave Response Handling

### Wait States

Slaves can insert wait states by holding PREADY low:

```
       Cycle 1    Cycle 2    Cycle 3    Cycle 4
PSEL   __|-------------------------------|____
PENABLE__|____________|------------------|____
PREADY _____________________|-----------|____
                      ^ Wait states
```

The crossbar:
- Holds master PREADY low while waiting
- Does not timeout (assumes slaves always respond)
- Passes through all wait states to master

### Error Response

When slave asserts PSLVERR:

1. Crossbar captures PSLVERR with PRDATA
2. Routes PSLVERR to originating master
3. Master sees PSLVERR=1 when its PREADY goes high

No error handling or recovery - error indication only.

## Multi-Slave Considerations

### Address Overlap Prevention

Each slave port is mutually exclusive:
- Only one slave receives PSEL for any given address
- No overlapping address regions
- Address decode is deterministic

### Independent Operation

Each slave operates independently:
- Own PREADY timing
- No synchronization between slaves
- Concurrent transactions to different slaves allowed (different masters)

---

**Next:** [Clock and Reset](03_clock_reset.md)
