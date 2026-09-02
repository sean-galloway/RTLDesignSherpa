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

# AXIL5 Slave Read

**Module:** `axil5_slave_rd.sv`
**Location:** `rtl/amba/axil5/`
**AXI4-Lite counterpart:** [`axil4_slave_rd`](../axil4/axil4_slave_rd.md)

---

## Overview

The AXIL5 Slave Read provides a buffered AXI5-Lite read interface for slave devices.

AXI5-Lite is AXI4-Lite plus optional signal groups. It changes no channel's handshake, ordering or response semantics, so this module is structurally `axil4_slave_rd` with those groups threaded through the packed SKID payload.

- AXI5-Lite read path (AR and R channels)
- Single-beat transactions: AXI-Lite has no burst support
- Configurable skid buffers on every channel for timing closure
- Eight optional signal groups, each independently enabled
- Bit-identical to the AXI4-Lite module of the same name with all groups disabled

---

## Parameters

| Parameter | Type | Default | Description |
|---|---|---|---|
| `AXIL_ADDR_WIDTH` | int | `32` |  |
| `AXIL_DATA_WIDTH` | int | `32` |  |
| `USER_WIDTH` | int | `4` |  |
| `LOOP_WIDTH` | int | `3` |  |
| `MPAM_WIDTH` | int | `11` |  |
| `MECID_WIDTH` | int | `16` |  |
| `NSAID_WIDTH` | int | `4` |  |
| `ENABLE_USER` | bit | `1` |  |
| `ENABLE_TRACE` | bit | `1` |  |
| `ENABLE_LOOP` | bit | `1` |  |
| `ENABLE_MPAM` | bit | `1` |  |
| `ENABLE_MECID` | bit | `1` |  |
| `ENABLE_NSAID` | bit | `1` |  |
| `ENABLE_POISON` | bit | `1` |  |
| `ENABLE_LOCK` | bit | `1` |  |
| `SKID_DEPTH_AR` | int | `2` |  |
| `SKID_DEPTH_R` | int | `4` |  |
| `AW` | int | `AXIL_ADDR_WIDTH` |  |
| `DW` | int | `AXIL_DATA_WIDTH` |  |
| `UW` | int | `USER_WIDTH` |  |
| `LW` | int | `LOOP_WIDTH` |  |
| `MW` | int | `MPAM_WIDTH` |  |
| `EW` | int | `MECID_WIDTH` |  |
| `NW` | int | `NSAID_WIDTH` |  |
| `PW` | int | `(DW / 64) > 0 ? (DW / 64) : 1` |  |
| `ARSize` | int | `AW + 3 +` |  |
| `RSize` | int | `DW + 2 +` |  |

The derived parameters (`AW`, `DW`, `UW`, ... and the `*Size` payload widths) are computed from the ones above. **Do not override them.** Forcing a `*Size` to a value the RTL did not derive makes every optional-group field a part-select past the end of the vector -- which is exactly how `test_axil5_master_wr` failed until `d6266344` removed those overrides.

---

## Ports

The `s_axil_*` side faces the bus; your backend drives the `fub_*` side.

| Port | Direction | Width | Description |
|---|---|---|---|
| `aclk` | Input | 1 |  |
| `aresetn` | Input | 1 |  |
| `s_axil_araddr` | Input | `[AW-1:0]` |  |
| `s_axil_arprot` | Input | `[2:0]` |  |
| `s_axil_arlock` | Input | 1 |  |
| `s_axil_aruser` | Input | `[UW-1:0]` |  |
| `s_axil_artrace` | Input | 1 |  |
| `s_axil_arloop` | Input | `[LW-1:0]` |  |
| `s_axil_armpam` | Input | `[MW-1:0]` |  |
| `s_axil_armecid` | Input | `[EW-1:0]` |  |
| `s_axil_arnsaid` | Input | `[NW-1:0]` |  |
| `s_axil_arvalid` | Input | 1 |  |
| `s_axil_arready` | Output | 1 |  |
| `fub_araddr` | Output | `[AW-1:0]` |  |
| `fub_arprot` | Output | `[2:0]` |  |
| `fub_arlock` | Output | 1 |  |
| `fub_aruser` | Output | `[UW-1:0]` |  |
| `fub_artrace` | Output | 1 |  |
| `fub_arloop` | Output | `[LW-1:0]` |  |
| `fub_armpam` | Output | `[MW-1:0]` |  |
| `fub_armecid` | Output | `[EW-1:0]` |  |
| `fub_arnsaid` | Output | `[NW-1:0]` |  |
| `fub_arvalid` | Output | 1 |  |
| `fub_arready` | Input | 1 |  |
| `fub_rdata` | Input | `[DW-1:0]` |  |
| `fub_rresp` | Input | `[1:0]` |  |
| `fub_ruser` | Input | `[UW-1:0]` |  |
| `fub_rtrace` | Input | 1 |  |
| `fub_rloop` | Input | `[LW-1:0]` |  |
| `fub_rpoison` | Input | `[PW-1:0]` |  |
| `fub_rvalid` | Input | 1 |  |
| `fub_rready` | Output | 1 |  |
| `s_axil_rdata` | Output | `[DW-1:0]` |  |
| `s_axil_rresp` | Output | `[1:0]` |  |
| `s_axil_ruser` | Output | `[UW-1:0]` |  |
| `s_axil_rtrace` | Output | 1 |  |
| `s_axil_rloop` | Output | `[LW-1:0]` |  |
| `s_axil_rpoison` | Output | `[PW-1:0]` |  |
| `s_axil_rvalid` | Output | 1 |  |
| `s_axil_rready` | Input | 1 |  |
| `busy` | Output | 1 |  |

---

## Functional Description

### Optional signal groups

Eight groups, each gated by its own `ENABLE_*` parameter. A group contributes to the packed SKID payload only when enabled.

| Group | Parameter | Signals on this module | Width |
|---|---|---|---|
| USER | `ENABLE_USER` | `AxUSER`, `WUSER`, `BUSER`, `RUSER` | `USER_WIDTH` |
| TRACE | `ENABLE_TRACE` | `AxTRACE`, `BTRACE`, `RTRACE` | 1 |
| LOOP | `ENABLE_LOOP` | `AxLOOP`, `BLOOP`, `RLOOP` | `LOOP_WIDTH` |
| MPAM | `ENABLE_MPAM` | `AxMPAM` | `MPAM_WIDTH` |
| MECID | `ENABLE_MECID` | `AxMECID` | `MECID_WIDTH` |
| NSAID | `ENABLE_NSAID` | `AxNSAID` | `NSAID_WIDTH` |
| POISON | `ENABLE_POISON` | `WPOISON`, `RPOISON` | one bit per 64 data bits |
| LOCK | `ENABLE_LOCK` | `AxLOCK` | 1 |

(Only the channels this module carries are present; a read module has no W or B channel, so it has no WPOISON or BUSER.)

### With every group disabled, this IS the AXI4-Lite module

The packed payload width of a fully-disabled build equals its AXI4-Lite counterpart's, channel for channel:

| Payload | AXI4-Lite | AXI5-Lite, groups off | AXI5-Lite, groups on |
|---|---|---|---|
| `ARSize` | 35 | 35 | 75 |
| `RSize` | 34 | 34 | 43 |
| `AWSize` | 35 | 35 | 75 |
| `WSize` | 36 | 36 | 41 |
| `BSize` | 2 | 2 | 10 |

(at `AXIL_ADDR_WIDTH = AXIL_DATA_WIDTH = 32` and the default group widths.)

That equivalence is what `val/amba/test_axil5_master_rd.py` relies on when it drives AXI4-Lite RTL with AXI5-Lite BFMs: with no groups enabled an AXI5-Lite interface *is* an AXI4-Lite interface, so the same testbench binds to either.

### It transports; it does not interpret

MPAM, MECID, NSAID, LOOP and TRACE are carried end to end unmodified. POISON is carried -- never generated, never checked. LOCK is carried with no exclusive-access monitor behind it. Those behaviours belong to the endpoints on either side, and nothing in this module implements them.

A disabled group's output is driven to zero rather than left dangling, so an integrator who disables a group downstream of one that enables it sees a defined value instead of X.

---

## Related Modules

- [axil5_master_rd](axil5_master_rd.md)
- [axil5_master_rd_cg](axil5_master_rd_cg.md)
- [axil5_master_rd_mon](axil5_master_rd_mon.md)
- [axil5_master_rd_mon_cg](axil5_master_rd_mon_cg.md)
- [axil5_master_wr](axil5_master_wr.md)
- [axil5_master_wr_cg](axil5_master_wr_cg.md)
- [`axil4_slave_rd`](../axil4/axil4_slave_rd.md) -- the AXI4-Lite counterpart
- [AXI4-Lite modules](../axil4/README.md)

---

## Testing

`val/amba/test_axil5_slave_rd.py` drives this module with the AXI5-Lite BFMs and **every optional group enabled** -- `TBClasses/axil5` sets the group widths in `COMPONENT_KWARGS` to mirror the RTL defaults. A BFM configured differently from its DUT is a bind failure, which is the loud version of the mistake.

The testbench class is the AXI4-Lite one with the component factories swapped, so every phase, check and randomizer sweep has a single definition, and a fix to the AXI4-Lite flow reaches this module automatically.

---

## Navigation

[AXI5-Lite index](README.md) | [AMBA overview](../overview.md)
