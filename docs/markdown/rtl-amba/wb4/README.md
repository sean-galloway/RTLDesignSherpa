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
**Status:** New (2026-09-09); sim and formal collateral in place

---

## Overview

A Wishbone B4 master and slave pair, both in the **pipelined** mode the B4
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

- **Pipelined mode only.** A new `STB` every clock while `STALL` is low, and
  in-order termination. Classic (one-outstanding) masters and slaves
  interoperate with these blocks by construction: a classic slave simply
  never accepts more than one, and a classic master never issues more.
- **RTY is a status, not a retry.** Every termination is returned to the FUB
  as `rsp_status` = ACK (0), ERR (1) or RTY (2). The master does not re-issue
  on RTY; the FUB decides. The encoding is `wb4_pkg`.
- **Not implemented, deliberately:** `CTI`/`BTE` burst hints (advisory in
  B4; the pipelined queues already give the throughput they recover),
  `LOCK`, `TGA`/`TGC`/`TGD` tags.

### Modules

- **[wb4_master](wb4_master.md)** - command/response queues in, pipelined
  Wishbone out; issue is credit-gated by the response queue so a termination
  can always be enqueued
- **[wb4_slave](wb4_slave.md)** - pipelined Wishbone in, command/response
  queues out; in-order registered termination with an orphan-response guard
- `wb4_pkg` - the response-status encoding shared by both and the DV

### Reset and clock naming

The ports are `clk` and `aresetn` (active-low), the repository convention,
rather than Wishbone's `CLK_I`/`RST_I` (active-high). An integrator bridging
to a Wishbone fabric that carries `RST_I` inverts it at the boundary; the
reset macros inside the blocks are polarity-agnostic.

### Test

Three tests in `val/amba/`, all through the RDS-DV framework's Wishbone B4
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

Each asserts the peak in-flight count exceeds one, so the pipelined mode is
proven exercised rather than assumed. Formal: `formal/amba/wb4_master/` and
`formal/amba/wb4_slave/`.
