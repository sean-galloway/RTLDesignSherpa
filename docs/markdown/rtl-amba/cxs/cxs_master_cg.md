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

# CXS Master with Clock Gating

**Module:** `cxs_master_cg.sv`
**Location:** `rtl/amba/cxs/`
**Status:** New (2026-10-15)

---

## Overview

`cxs_master_cg` puts [cxs_master](cxs_master.md) behind one `amba_clock_gate_ctrl`. It has the same parameters and ports as the core, minus `busy`, plus the clock-gating set: `CG_IDLE_COUNT_WIDTH`, `cfg_cg_enable`, `cfg_cg_idle_count`, `cg_gating` and `cg_idle`.

## When It Gates

A credited link changes state with no handshake the gated side could stall. A `CXSCRDGNT` that arrives while the clock is stopped is a credit lost for good. The core's `busy` therefore covers every state in which the receiver may still grant: `CXSACTIVEREQ` or the sampled `CXSACTIVEACK` high, or any credit held. As a result:

| CXS_LINK_CTRL | Gates? | Why |
|---|---|---|
| 1 | Only in STOP with zero credits | The receiver "must not send credit" in STOP (IHI 0079D 5.2). A FUB flit wakes the block, which then raises `CXSACTIVEREQ` |
| 0 | Never | The receiver grants whenever it has room, so the core holds credits indefinitely and `busy` never falls |

The second row is a property of the protocol, not a shortcoming of this wrapper. To save clock power, use link control.

## Activity Terms

The terms follow `vault/handbook/design/clock-gating-activity-terms.md`:

| Term | Expression | Reason |
|---|---|---|
| user_valid | `fub_cxs_valid \| busy` | FUB VALID plus all pending work |
| axi_valid | `m_cxs_crdgnt \| m_cxs_activeack` | The peer's VALID-like inputs, synchronous to `aclk` (5.5) |

No READY appears in either term; CXS has none. The event outputs `CXSVALID` and `CXSCRDRTN` are masked with `!cg_gating` for the wake-latency overlap, and their check bits follow the masked value (a masked 0 carries check 1). `fub_cxs_ready` is forced low while gated.

## Testing

`val/amba/test_cxs_master_cg.py` runs the master traffic with `cfg_cg_enable = 1` and checks every flit. It then makes two gating claims: with link control the block **must** gate during an idle window in STOP, and without link control it must **never** gate.

## Navigation

- **[Back to CXS Index](README.md)**
- **[CXS Master](cxs_master.md)**
