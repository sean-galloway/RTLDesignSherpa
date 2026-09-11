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

# Wishbone B4 Modules

**Location:** `rtl/amba/wb4/`
**Test Location:** `val/amba/`
**Status:** New (2026-09-09); master, slave, monitor, retry, clock-gated and
CDC variants with sim and formal collateral. Family FULL sweep on one pinned
seed base (`RDS_SEED_BASE=20260910`): 379 cells across the nine wb4 suites in
`val/amba/`, plus the two AXI4-Lite bridge suites in
`projects/components/converters/dv/tests/`, all passing. The cell count grew
on 2026-09-11 when `USE_BURST_HINTS` became a dimension of the master and
monitor suites.

---

## Overview

A Wishbone B4 master and slave pair (and a monitor for either), both in the **pipelined** mode the B4
revision added, behind the same FUB-side contract the APB4 pair uses: a
command queue and a response queue, each a valid/ready handshake through a
`gaxi_skid_buffer`. A FUB that already talks to `apb4_master` through
`cmd_*`/`rsp_*` talks to `wb4_master` the same way; the differences are the
field names and a 2-bit status in place of `pslverr`.

There is no Wishbone B5. B4 (2010) is the current revision of the
specification and is what the `wb4` name records, the way `apb4` records
AMBA 4 APB.

### Protocol scope

| Signal set | Master (`m_wb_*`) | Slave (`s_wb_*`) |
|---|---|---|
| `CYC`, `STB`, `WE`, `ADR`, `DAT_W` (DAT_O), `SEL` | drives | receives |
| `STALL` | receives | drives (combinational from state, never from `STB`) |
| `ACK`, `ERR`, `RTY`, `DAT_R` (DAT_I) | receives | drives (registered) |

- **Pipelined by default, classic by parameter.** With `CLASSIC=0` a new
  `STB` every clock while `STALL` is low, and in-order termination. With
  `CLASSIC=1` the blocks speak B4 standard ("classic") mode: the master holds
  the request on `STB`/`CYC` until the termination and ignores `STALL`; the
  slave never drives `STALL`, accepts a presentation once, and refuses an
  accept in the clock its termination is on the wire (the held `STB` is
  still there, and would otherwise be taken twice).
- **Match the mode to the peer.** The two modes do not mix, in either
  direction: a pipelined master drops `STB` after one clock, which a classic
  slave never accepts, and a classic master's held `STB` is accepted again
  every clock by a pipelined slave (B4 chapter 5). Both tests and both
  formal harnesses run each mode against a peer of the same mode.
- **RTY is a status, not a retry.** Every termination is returned to the FUB
  as `rsp_status` = ACK (0), ERR (1) or RTY (2). The master does not re-issue
  on RTY; the FUB decides, or `wb4_retry` decides for it. The encoding is `wb4_pkg`.
- **Burst hints are carried, not acted on.** `CTI` and `BTE` are advisory in
  B4. With `USE_BURST_HINTS = 1` the master puts the FUB's hint on the wires
  with the transfer it belongs to and the slave hands the received hint to
  its FUB; neither changes behaviour, because deciding what a burst means is
  the peripheral's job. With the parameter at 0 the ports still exist and the
  bus reads CLASSIC/LINEAR, a legal non-burst cycle, which is what every
  consumer had before the hints landed.
- **Still not implemented, deliberately:** `LOCK` and the `TGA`/`TGC`/`TGD`
  tag signals.

### Modules

- **[wb4_master](wb4_master.md)** - command/response queues in, pipelined
  Wishbone out; issue is credit-gated by the response queue so a termination
  can always be enqueued
- **[wb4_slave](wb4_slave.md)** - pipelined Wishbone in, command/response
  queues out; in-order registered termination with an orphan-response guard
- **[wb4_monitor](wb4_monitor.md)** - watches either block's queues and
  reports completions, errors, timeouts, latency and address-range hits as
  monitor bus packets tagged `PROTOCOL_WB`; in-order tracking queue, since
  B4 terminates in issue order
- **[wb4_retry](wb4_retry.md)** - RTY retry on the FUB side of the master:
  in-order completion buffer, re-issue up to a budget with a delay, the FUB
  sees RTY only once the budget is spent; **[wb4_master_retry](wb4_master_retry.md)**
  is the block and the master together
- **[wb4_master_cg](wb4_master_cg.md)**, **[wb4_slave_cg](wb4_slave_cg.md)** -
  the clock-gated variants (`amba_clock_gate_ctrl`, runtime enable and idle
  count, output valids masked for the wake overlap)
- **[wb4_slave_cdc](wb4_slave_cdc.md)** - the slave with its queues carried
  to another clock domain over two `gaxi_fifo_async` instances;
  **[wb4_slave_cdc_cg](wb4_slave_cdc_cg.md)** adds the gated bus clock
- **[wb4_master_stub](wb4_master_stub.md)** / **[wb4_slave_stub](wb4_slave_stub.md)** -
  the pair with packed cmd/rsp vectors, for shim-style converters
- **[wb4_pkg](wb4_pkg.md)** - the response-status encoding shared by the family and the DV

### Reset and clock naming

The ports are `clk` and `aresetn` (active-low), the repository convention,
rather than Wishbone's `CLK_I`/`RST_I` (active-high). An integrator bridging
to a Wishbone fabric that carries `RST_I` inverts it at the boundary; the
reset macros inside the blocks are polarity-agnostic.

### Test

Nine test files in `val/amba/`, all through the RDS-DV framework's Wishbone B4
BFMs (`CocoTBFramework.components.wb4`: `WB4Master`, `WB4Slave`,
`WB4Monitor`) and the GAXI BFMs on the FUB-side queues:

- `test_wb4_master.py` - the master alone: the framework slave answers on
  the bus from a memory model with ERR and RTY address windows, the monitor
  checks the wires, and every response on `rsp_*` is paired in order with
  the termination the slave produced.
- `test_wb4_slave.py` - the slave alone: the framework master drives the bus
  and the test is the FUB. Includes the abort case (CYC dropped with requests
  outstanding), which a master-slave loop can never produce, and proves the
  slave discards the late responses instead of pairing them with the next
  cycle.
- `test_wb4_master_slave_loop.py` - both back to back
  (`rtl/amba/testcode/wb4_master_slave_loop.sv`); the framework monitor and
  the wrapper's own protocol checks must agree.
- `test_wb4_master_cg.py`, `test_wb4_slave_cg.py` - the clock-gated wrappers:
  the gate must not swallow a transfer, and the wake must be bounded.
- `test_wb4_slave_cdc.py` - the clock-domain-crossing slave, and the gated
  variant built on it.
- `test_wb4_master_retry.py` - the RTY retry wrapper: re-issue budget, delay,
  and that a retried transfer carries its own payload and burst hint.
- `test_wb4_monitor.py` - the monitor, decoded through the shared monbus path.
- `test_wb4_stubs.py` - the packed-vector stubs.

The three single-block tests above each assert the peak in-flight count
exceeds one, so the pipelined mode is proven exercised rather than assumed.
Formal covers nine blocks: seven under `formal/amba/wb4_*` and the two
converter cores under `formal/converters/`.
