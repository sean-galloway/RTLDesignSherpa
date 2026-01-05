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

# Master-Side APB Interfaces

## Interface Overview

Each master port provides a complete APB slave interface to accept transactions from an external APB master (CPU, DMA, etc.).

## Signal Definition

For each master index `i` (0 to M-1):

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `m<i>_apb_PSEL` | 1 | Input | Peripheral select |
| `m<i>_apb_PENABLE` | 1 | Input | Transfer enable |
| `m<i>_apb_PADDR` | ADDR_WIDTH | Input | Address bus |
| `m<i>_apb_PWRITE` | 1 | Input | Write/read direction |
| `m<i>_apb_PWDATA` | DATA_WIDTH | Input | Write data bus |
| `m<i>_apb_PSTRB` | STRB_WIDTH | Input | Write strobes |
| `m<i>_apb_PPROT` | 3 | Input | Protection attributes |
| `m<i>_apb_PRDATA` | DATA_WIDTH | Output | Read data bus |
| `m<i>_apb_PSLVERR` | 1 | Output | Slave error response |
| `m<i>_apb_PREADY` | 1 | Output | Transfer ready |

: Master Port Signal Definition

## Signal Descriptions

### PSEL (Input)

Peripheral select signal. When asserted:
- Indicates master wants to access the crossbar
- Must remain asserted throughout the transaction
- Combined with PADDR determines target slave

### PENABLE (Input)

Transfer enable signal. APB state machine:
- PSEL=1, PENABLE=0: Setup phase
- PSEL=1, PENABLE=1: Access phase (data transfer)

### PADDR (Input)

Address bus. Used for:
- Target slave selection (upper bits)
- Local address within slave (lower bits)
- Must be stable while PSEL asserted

### PWRITE (Input)

Transfer direction:
- PWRITE=1: Write transaction (data from master)
- PWRITE=0: Read transaction (data to master)

### PWDATA (Input)

Write data bus:
- Valid during write transactions
- Sampled when PREADY and PENABLE both high
- Width set by DATA_WIDTH parameter

### PSTRB (Input)

Write byte strobes:
- One bit per byte of DATA_WIDTH
- Indicates which bytes are valid in PWDATA
- Ignored during read transactions

### PPROT (Input)

Protection attributes (3 bits):
- Bit 0: Privileged/normal access
- Bit 1: Secure/non-secure access
- Bit 2: Instruction/data access

### PRDATA (Output)

Read data bus:
- Valid during read transactions when PREADY high
- Undefined during write transactions
- Width matches DATA_WIDTH parameter

### PSLVERR (Output)

Slave error response:
- Sampled when PREADY and PENABLE both high
- PSLVERR=1 indicates error condition
- Propagated from downstream slave

### PREADY (Output)

Transfer ready signal:
- PREADY=1 allows transaction to complete
- PREADY=0 inserts wait states
- Reflects downstream slave PREADY (or arbitration wait)

## Transaction Timing

### Uncontended Write (No Arbitration Wait)

```
       Cycle 1    Cycle 2    Cycle 3
PSEL   __|-----------|----------|____
PENABLE__|________---|----------|____
PADDR  --<  Address  >--
PWRITE --<  1        >--
PWDATA --<  Data     >--
PREADY _________|----------|____
```

### Contended Transaction (Arbitration Wait)

When another master holds the target slave:

```
       Cycle 1    Cycle 2    Cycle 3    Cycle 4
PSEL   __|--------------------------|____
PENABLE__|_____________|--------------|____
PADDR  --<  Address                   >--
PREADY _______________________|------|____
                     ^ Wait for grant
```

---

**Next:** [Slave-Side Interfaces](02_slave_side.md)
