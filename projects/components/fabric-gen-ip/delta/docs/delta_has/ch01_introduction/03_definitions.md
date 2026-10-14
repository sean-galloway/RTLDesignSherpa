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
| AXIS | AXI4-Stream (ARM AMBA streaming protocol) |
| AMBA5 | ARM AMBA 5 protocol extensions, including TWAKEUP and the T*CHK interface check signals |
| TDEST | Transaction destination (slave ID in AXI4-Stream) |
| TID | Transaction ID (master identifier in AXI4-Stream) |
| TUSER | User-defined sideband in AXI4-Stream |
| TSTRB | Byte strobe / byte qualifier in AXI4-Stream |
| TWAKEUP | AMBA 5 wakeup hint signal |
| T*CHK | AXI5-Stream interface check signals (`TDATACHK`, `TVALIDCHK`, ...), odd parity, IHI 0051B chapter 5 |
| RR | Round-robin arbitration |
| LUT | Look-up table (FPGA logic resource) |
| FF | Flip-flop (FPGA register resource) |

: Acronyms and Definitions

## Key Terms

**Base flavor**
: The default generated crossbar with the seven-signal set: `tdata`, `tvalid`, `tready`, `tlast`, `tdest`, `tid`, `tuser`.

**Rich flavor**
: A generated crossbar with optional additional signals enabled: `tstrb` and/or AMBA 5 `twakeup` with the `t*chk` check signals.

**Packet atomicity**
: The property that once a master is granted access to a slave, it retains that grant until the current packet's `TLAST` beat has been transferred. No other master may interleave beats on that slave during the packet.

**Request matrix**
: A per-slave collection of master request bits. `request_matrix[s][m]` is true when master `m` has a valid transaction targeting slave `s`.

**Grant matrix**
: A per-slave one-hot (or zero-hot) collection of master grant bits. `grant_matrix[s][m]` is true when master `m` currently owns slave `s`.

**TDEST decode**
: The combinational translation of `s_axis_tdest[m]` into a slave index in the request matrix. Delta does not use an address map.

**TWAKEUP steering**
: The AMBA 5 sideband path that forwards a master's `s_axis_twakeup` hint to the slave selected by `s_axis_tdest`. It is an OR-per-slave and may assert before `TVALID`.
