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

# Wishbone B4 Interface

## Overview

Wishbone B4 is the open bus of the FPGA world -- the fabric OpenCores cores
speak and the one most soft CPUs ship with. Since BRIDGE-019 a bridge port
can be Wishbone on either side: a **slave port** with `protocol = "wb4"`
makes the bridge the Wishbone requester toward an external completer; a
**master port** with `protocol = "wb4"` makes the bridge the completer for an
external Wishbone requester. The fabric between stays AXI4.

The mode is **B4 pipelined** -- a new `STB` every clock while `STALL` is
low, in-order termination -- which is what `rtl/amba/wb4` and the converters
implement. B4 standard ("classic") mode exists in the converters as a
parameter but is not selectable from the TOML; the two modes do not mix on
one bus, so a classic peer needs a classic bridge build.

## Ports

### Signal Definition

| Signal | Width | Slave port (bridge requests) | Master port (bridge completes) | Description |
|--------|-------|------|------|-------------|
| CYC | 1 | Output | Input | Bus cycle in progress |
| STB | 1 | Output | Input | Transfer request |
| WE | 1 | Output | Input | 1 = write, 0 = read |
| ADR | ADDR_WIDTH | Output | Input | Byte address (the fabric address, unwindowed) |
| DAT_W | DATA_WIDTH | Output | Input | Write data (the spec's DAT_O from the requester) |
| SEL | DATA_WIDTH/8 | Output | Input | Byte lane select = AXI WSTRB |
| CTI | 3 | Output | Input | Burst hint (carried, not acted on; CLASSIC when the bridge drives it) |
| BTE | 2 | Output | Input | Burst type extension (LINEAR when the bridge drives it) |
| STALL | 1 | Input | Output | Pipelined back-pressure |
| ACK | 1 | Input | Output | Normal termination |
| ERR | 1 | Input | Output | Error termination |
| RTY | 1 | Input | Output | Retry termination (never driven by the bridge) |
| DAT_R | DATA_WIDTH | Input | Output | Read data (the spec's DAT_I at the requester) |

: Table 4.7: Wishbone B4 Signal Definitions

### Signal Naming

Wishbone ports use the TOML prefix followed by the uppercase B4 name, the
convention `rtl/amba/wb4` and the RDS-DV BFMs share:

```systemverilog
// Slave port, prefix "wbp_wb_" -- the bridge drives the bus
output logic        wbp_wb_CYC,
output logic        wbp_wb_STB,
output logic        wbp_wb_WE,
output logic [31:0] wbp_wb_ADR,
output logic [31:0] wbp_wb_DAT_W,
output logic [3:0]  wbp_wb_SEL,
output logic [2:0]  wbp_wb_CTI,
output logic [1:0]  wbp_wb_BTE,
input  logic        wbp_wb_STALL,
input  logic        wbp_wb_ACK,
input  logic        wbp_wb_ERR,
input  logic        wbp_wb_RTY,
input  logic [31:0] wbp_wb_DAT_R
```

A master port has the same thirteen with the directions reversed.

## Functional Description

### Slave port: AXI4 to Wishbone

`axi4_to_wb4` (converters MAS, chapter 3) sits in the slave adapter: the
AXI4-Lite decomposers turn each AXI4 burst into one single-beat transfer per
beat, and `axil4_to_wb4` turns those into Wishbone transfers, in order.
`WSTRB` becomes `SEL`. Termination maps back as:

| Wishbone | AXI4 response |
|---|---|
| ACK | OKAY |
| ERR | SLVERR |
| RTY | SLVERR (`RTY_RESP`; AXI has no retry) |

: Table 4.8: Wishbone termination to AXI4 response

The monitored (`mon`) variant places the `axi4_master_*_mon` wrappers
between the crossbar and the converter, exactly as for APB slave ports.

### Master port: Wishbone to AXI4

`wb4_to_axi4` sits in the master adapter in front of the ordinary AXI4
timing wrapper: `wb4_to_axil4` merges AXI's two response channels back into
Wishbone's single in-order termination stream, and the wrapper promotes the
AXI4-Lite face to AXI4 (`AxLEN = 0`, full-width `AxSIZE`, INCR, `WLAST = 1`,
a constant ID -- the fabric prepends the master index, BRIDGE-016). From the
wrapper on, the port is an AXI4-Lite-shaped single-beat requester: decode,
the width converters, the wide-slave aligner toward wider slaves and the
response mux are the ones every other master uses. `SLVERR` and `DECERR`
both terminate `ERR` -- an unmapped address (the subtractive slave) is
indistinguishable from a failing completer on this bus. `RTY` is never
generated.

### Rules the validator enforces

- `channels = "rw"` (one bus carries both directions), `id_width = 0`.
- `data_width` is 8, 16, 32 or 64.
- A master port has `addr_width = 32`: `ADR` is the full fabric address,
  where an APB or Wishbone *slave* port's address is whatever the fabric
  forwards for its window.

## Design Notes

- **In-order by construction.** Wishbone terminates in issue order and the
  bridge's slave-side tracking is in-order for shim-converted slaves, so a
  Wishbone completer never needs the CAM. Two masters sharing a Wishbone
  completer are serialised by the crossbar's arbitration and answered in
  that order.
- **One transfer per beat.** A 16-beat AXI4 burst is sixteen Wishbone
  transfers; the pipelined bus takes one per clock when the completer does
  not stall, so the cost is latency, not bandwidth.
- **Burst hints are not generated.** `CTI`/`BTE` are CLASSIC/LINEAR on a
  slave port; a Wishbone completer that needs registered-feedback bursts to
  perform will not see them from the bridge.

Verified by `dv/tests/test_bridge_2x2_wb4_paths.py` on `bridge_2x2_wb4`
(error folding both ways, SEL lanes at both a Wishbone and a 64-bit AXI4
completer, burst decomposition, both requesters in flight at the Wishbone
completer) plus the generated tests of that fixture.
