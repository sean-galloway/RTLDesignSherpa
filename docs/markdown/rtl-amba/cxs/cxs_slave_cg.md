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

# CXS Slave with Clock Gating

**Module:** `cxs_slave_cg.sv`
**Location:** `rtl/amba/cxs/`
**Status:** New (2026-10-15)

---

## Overview

`cxs_slave_cg` puts [cxs_slave](cxs_slave.md) behind one `amba_clock_gate_ctrl`. It has the same parameters and ports as the core, minus `busy`, plus `CG_IDLE_COUNT_WIDTH`, `cfg_cg_enable`, `cfg_cg_idle_count`, `cg_gating` and `cg_idle`.

IHI 0079D 5.5 anticipates this block: "It is common for the clock in the Receiver to stop during the STOP state ... The assertion of the CXSACTIVEREQ signal might be used to restart that clock."

## When It Gates

The core's `busy` covers every state in which a flit or credit return can still arrive: ACK or the synchronized ACTIVEREQ high, any credit outstanding, or a flit waiting on the FUB side.

| CXS_LINK_CTRL | Gates? | Why |
|---|---|---|
| 1 | Only in STOP, every credit home, FIFO empty | The transmitter "must not send flits or credit returns" in STOP (5.2); a rising `CXSACTIVEREQ` wakes the block |
| 0 | Never | Credits stay outstanding indefinitely, so a flit can arrive on any cycle |

## Activity Terms

| Term | Expression | Reason |
|---|---|---|
| user_valid | `busy` | Includes `fub_cxs_valid`, the pending output |
| axi_valid | `s_cxs_valid \| s_cxs_crdrtn \| ACTIVEREQ (synchronized)` | Peer VALIDs and the wake request |

`CXSACTIVEREQ` is asynchronous, so the wake term passes through its own `glitch_free_n_dff_arn` on the **free-running** `aclk`. A wake term must be in the gate's own clock domain, and the core's synchronizer sits on the gated clock and is frozen in STOP. `CXSCRDGNT` (and its check bit) and `fub_cxs_valid` are masked with `!cg_gating`.

## Testing

`val/amba/test_cxs_slave_cg.py` streams flits, takes the link to STOP, idles, and requires the block to have gated during that window. It then sends a wake phase that must be delivered intact, which proves `CXSACTIVEREQ` restarted the clock. Without link control it must never gate.

## Navigation

- **[Back to CXS Index](README.md)**
- **[CXS Slave](cxs_slave.md)**
