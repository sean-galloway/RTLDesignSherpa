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

# Definitions and Acronyms

## Acronyms

| Acronym | Definition |
|---------|------------|
| AMBA | Advanced Microcontroller Bus Architecture |
| APB | Advanced Peripheral Bus |
| AR | AXI4 Read Address channel |
| AW | AXI4 Write Address channel |
| AXI | Advanced eXtensible Interface |
| AXI4 | AXI Protocol Version 4 |
| B | AXI4 Write Response channel |
| BID | Bridge ID (internal master identifier) |
| CAM | Content-Addressable Memory |
| CDC | Clock Domain Crossing |
| CSV | Comma-Separated Values |
| DECERR | Decode Error (AXI response) |
| DMA | Direct Memory Access |
| FIFO | First-In First-Out buffer |
| FSM | Finite State Machine |
| HAS | Hardware Architecture Specification |
| ID | Transaction Identifier |
| MAS | Micro-Architecture Specification |
| MUX | Multiplexer |
| NxM | N masters by M slaves (topology notation) |
| OOO | Out-of-Order |
| OOR | Out-of-Range |
| QoS | Quality of Service |
| R | AXI4 Read Data channel |
| RTL | Register-Transfer Level |
| SLVERR | Slave Error (AXI response) |
| SoC | System-on-Chip |
| TOML | Tom's Obvious Minimal Language |
| W | AXI4 Write Data channel |

: Acronyms and Abbreviations

## Definitions

**Address Decode:**
Determining which slave receives a transaction, from its address.

**Arbitration:**
Selecting which master gets a slave when several masters contend for it.

**Bridge ID (BID):**
The issuing master's index, width clog2(NUM_MASTERS). With more than one master it is both prepended to the AXI ID inside the fabric (slave-side IDs are `{BRIDGE_ID, id}`, wider than master-side ones) and carried as a sideband into the slave adapter's response tracker (a `bridge_cam` or an in-order FIFO), which routes B and R back to the master.

**Channel-Specific Master:**
A master that uses only a subset of AXI4 channels (write-only or read-only).

**Crossbar:**
An NxM interconnect allowing any master to communicate with any connected slave.

**Grant Locking:**
Mechanism that holds arbitration grant until transaction completes.

**Out-of-Order Response:** (defined for completeness; NOT supported by this bridge)
Responses returned in different order than requests were issued.

**Protocol Conversion:**
Transformation between different bus protocols (e.g., AXI4 to APB).

**Response Routing:**
Directing B/R channel responses back to the originating master.

**Round-Robin Arbitration:**
Fair arbitration where priority rotates among requesters.

**Width Conversion:**
Transformation between different data bus widths (upsize or downsize).
