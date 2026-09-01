<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> &middot; <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> &middot;
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> &middot;
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# AXI5-Lite (AXIL5) Modules

**Location:** `rtl/amba/axil5/`
**Sibling family:** [AXI4-Lite](../axil4/README.md)

---

## Overview

Sixteen modules mirroring the AXI4-Lite family one for one, with the AXI5-Lite
optional signal groups threaded through. Same channel set, same handshakes,
same single-beat semantics; what AXI5-Lite adds is sideband.

## Scope of This Implementation

These modules **transport** AXI5-Lite signals. They do not execute AXI5-Lite
semantics:

- MPAM, MECID, NSAID, LOOP and TRACE are carried end to end unmodified. Nothing
  here interprets a partition ID or an encryption context.
- POISON is carried. It is never generated and never checked.
- LOCK is carried with no exclusive-access monitor behind it. A completer
  returning EXOKAY is not validated against anything.

Those behaviours belong to the endpoints on either side. Read this before
treating the family as a full AXI5-Lite protocol stack -- it is not one.

## Module Categories

### Transport (4)

| Module | Channels |
|---|---|
| [axil5_master_rd](axil5_master_rd.md) | AR, R |
| [axil5_master_wr](axil5_master_wr.md) | AW, W, B |
| [axil5_slave_rd](axil5_slave_rd.md) | AR, R |
| [axil5_slave_wr](axil5_slave_wr.md) | AW, W, B |

### Clock-gated (4)

| Module | Adds |
|---|---|
| [axil5_master_rd_cg](axil5_master_rd_cg.md) | One `amba_clock_gate_ctrl` over the whole inner module |
| [axil5_master_wr_cg](axil5_master_wr_cg.md) | ditto |
| [axil5_slave_rd_cg](axil5_slave_rd_cg.md) | ditto |
| [axil5_slave_wr_cg](axil5_slave_wr_cg.md) | ditto |

### Monitored (4)

| Module | Adds |
|---|---|
| [axil5_master_rd_mon](axil5_master_rd_mon.md) | `axi_monitor_filtered`, monbus packet output |
| [axil5_master_wr_mon](axil5_master_wr_mon.md) | ditto |
| [axil5_slave_rd_mon](axil5_slave_rd_mon.md) | ditto |
| [axil5_slave_wr_mon](axil5_slave_wr_mon.md) | ditto |

### Monitored and clock-gated (4)

| Module | Adds |
|---|---|
| [axil5_master_rd_mon_cg](axil5_master_rd_mon_cg.md) | Both, with ready held low while gated |
| [axil5_master_wr_mon_cg](axil5_master_wr_mon_cg.md) | ditto |
| [axil5_slave_rd_mon_cg](axil5_slave_rd_mon_cg.md) | ditto |
| [axil5_slave_wr_mon_cg](axil5_slave_wr_mon_cg.md) | ditto |

---

## AXI4-Lite vs AXI5-Lite in This Library

| Feature | AXI4-Lite | AXI5-Lite |
|---|---|---|
| Channels | AW, W, B, AR, R | same |
| Burst support | none | none |
| Transaction ID | none | none |
| User sideband | not present | `AxUSER`/`WUSER`/`BUSER`/`RUSER`, gated by `ENABLE_USER` |
| Trace | not present | `AxTRACE`/`BTRACE`/`RTRACE`, gated by `ENABLE_TRACE` |
| Loopback ID | not present | `AxLOOP`/`BLOOP`/`RLOOP`, gated by `ENABLE_LOOP` |
| MPAM / MECID / NSAID | not present | on the address channels, each independently gated |
| Poison | not present | `WPOISON`/`RPOISON`, one bit per 64 data bits |
| Exclusive access | not present | `AxLOCK`, gated by `ENABLE_LOCK` |

**With every group disabled the two are the same interface.** The packed
payload widths match channel for channel, which is what lets one testbench
bind to either family.

---

## Quick Start

```systemverilog
// AXI4-Lite-equivalent: every group off, payload widths identical to axil4
axil5_master_rd #(
    .AXIL_ADDR_WIDTH (32),
    .AXIL_DATA_WIDTH (32),
    .ENABLE_USER (0), .ENABLE_TRACE (0), .ENABLE_LOOP  (0), .ENABLE_MPAM (0),
    .ENABLE_MECID(0), .ENABLE_NSAID(0), .ENABLE_POISON(0), .ENABLE_LOCK (0)
) u_plain ( /* ... */ );

// With the security qualifiers, which is what AXI5-Lite is usually for
axil5_master_rd #(
    .AXIL_ADDR_WIDTH (32),
    .AXIL_DATA_WIDTH (32),
    .NSAID_WIDTH (4), .MPAM_WIDTH (11), .MECID_WIDTH (16),
    .ENABLE_NSAID(1), .ENABLE_MPAM(1), .ENABLE_MECID(1),
    .ENABLE_USER (0), .ENABLE_TRACE(0), .ENABLE_LOOP (0),
    .ENABLE_POISON(0), .ENABLE_LOCK(0)
) u_secure ( /* ... */ );
```

---

## Testing

`val/amba/test_axil5_*.py` -- sixteen runners, 42 parameterised cases, all
passing. They drive the modules with **every optional group enabled**, which
makes them the only tests in the repo that exercise the AXI5-Lite sideband
against real transport RTL rather than a behavioural model.

The testbench classes in `bin/TBClasses/axil5/` are the AXI4-Lite ones with
the component factories swapped and the group widths set in
`COMPONENT_KWARGS`. One definition of the traffic and its checks.

Also here: `test_axil5_opt_signals.py` drives `axil5_opt_slave`, a behavioural
slave under `rtl/amba/axil5/test-modules/` built purely so the BFMs had a DUT
carrying every optional port. It is test collateral -- do not instantiate it in
a design.

---

## Known Limitations

- No protocol checking of the optional groups. The monitored variants observe
  handshakes, addresses, responses and timing; `axi_monitor_filtered` has no
  ports for MPAM, MECID, NSAID, TRACE, LOOP or POISON.
- No exclusive-access monitor. `AxLOCK` is transported; nothing tracks
  exclusive state or validates EXOKAY.
- No poison generation or checking.
- Timing diagrams are not yet drawn for this family.

---

## Navigation

[AMBA overview](../overview.md) | [AXI4-Lite](../axil4/README.md) | [AXI5](../axi5/README.md)
