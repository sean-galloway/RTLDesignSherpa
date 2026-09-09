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

`val/amba/test_wb4_master_slave_loop.py` wires a master to a slave
(`rtl/amba/testcode/wb4_master_slave_loop.sv`) and drives both entirely
through the four FUB-side queues with the GAXI BFMs under independent timing
profiles. The wrapper carries the pipelined-protocol checks a Wishbone BFM
monitor would perform: `STB` implies `CYC`, a stalled request is held
unchanged, at most one termination per clock, none outside a cycle, never
more terminations than accepted requests. It also records the peak
in-flight count, which the test asserts is above one so the pipelined mode
is proven exercised rather than assumed.
