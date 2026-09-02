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

# AXIL5 Master Read

**Module:** `axil5_master_rd.sv`
**Location:** `rtl/amba/axil5/`
**AXI4-Lite counterpart:** [`axil4_master_rd`](../axil4/axil4_master_rd.md)

---

## Overview

The AXIL5 Master Read provides a buffered AXI5-Lite read interface for master devices.

AXI5-Lite is AXI4-Lite plus optional signal groups. It changes no channel's handshake, ordering or response semantics, so this module is structurally `axil4_master_rd` with those groups threaded through the packed SKID payload.

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

Your logic drives the `fub_*` side; the `m_axil_*` side faces the bus.

| Port | Direction | Width | Description |
|---|---|---|---|
| `aclk` | Input | 1 |  |
| `aresetn` | Input | 1 |  |
| `fub_araddr` | Input | `[AW-1:0]` |  |
| `fub_arprot` | Input | `[2:0]` |  |
| `fub_arlock` | Input | 1 |  |
| `fub_aruser` | Input | `[UW-1:0]` |  |
| `fub_artrace` | Input | 1 |  |
| `fub_arloop` | Input | `[LW-1:0]` |  |
| `fub_armpam` | Input | `[MW-1:0]` |  |
| `fub_armecid` | Input | `[EW-1:0]` |  |
| `fub_arnsaid` | Input | `[NW-1:0]` |  |
| `fub_arvalid` | Input | 1 |  |
| `fub_arready` | Output | 1 |  |
| `m_axil_araddr` | Output | `[AW-1:0]` |  |
| `m_axil_arprot` | Output | `[2:0]` |  |
| `m_axil_arlock` | Output | 1 |  |
| `m_axil_aruser` | Output | `[UW-1:0]` |  |
| `m_axil_artrace` | Output | 1 |  |
| `m_axil_arloop` | Output | `[LW-1:0]` |  |
| `m_axil_armpam` | Output | `[MW-1:0]` |  |
| `m_axil_armecid` | Output | `[EW-1:0]` |  |
| `m_axil_arnsaid` | Output | `[NW-1:0]` |  |
| `m_axil_arvalid` | Output | 1 |  |
| `m_axil_arready` | Input | 1 |  |
| `m_axil_rdata` | Input | `[DW-1:0]` |  |
| `m_axil_rresp` | Input | `[1:0]` |  |
| `m_axil_ruser` | Input | `[UW-1:0]` |  |
| `m_axil_rtrace` | Input | 1 |  |
| `m_axil_rloop` | Input | `[LW-1:0]` |  |
| `m_axil_rpoison` | Input | `[PW-1:0]` |  |
| `m_axil_rvalid` | Input | 1 |  |
| `m_axil_rready` | Output | 1 |  |
| `fub_rdata` | Output | `[DW-1:0]` |  |
| `fub_rresp` | Output | `[1:0]` |  |
| `fub_ruser` | Output | `[UW-1:0]` |  |
| `fub_rtrace` | Output | 1 |  |
| `fub_rloop` | Output | `[LW-1:0]` |  |
| `fub_rpoison` | Output | `[PW-1:0]` |  |
| `fub_rvalid` | Output | 1 |  |
| `fub_rready` | Input | 1 |  |
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

## Timing Characteristics

### Buffer Depths and Latency

| Parameter | Default | Channel |
|-----------|---------|---------|
| `SKID_DEPTH_AR` | 2 entries | Skid depth on the AR channel |
| `SKID_DEPTH_R` | 4 entries | Skid depth on the R channel |

Each channel traverses one `gaxi_skid_buffer`. That module registers both
`rd_valid` and the storage array, so the **1-cycle input-to-output latency
applies on every transfer, including the unstalled case** -- there is no
combinational bypass from the upstream payload to the downstream one. Full
throughput (one transfer per cycle) is still sustained once the pipeline is
primed; the depth sets how much backpressure can be absorbed before it
propagates upstream, not the steady-state rate.

Legal depth range is 2..8 inclusive, odd values included.

### Optional-group effect

The AXI5-Lite optional groups widen the packed skid payload but do not add a
pipeline stage: `ARSize`, `AWSize`, `WSize`, `RSize` and `BSize` are
conditional sums over the `ENABLE_*` parameters, so disabling a group narrows
the storage without changing latency.

---


## Usage Examples

Every parameter and port below is taken from the module declaration; the
elisions name the remaining members of each group, all of which appear in the
Ports table above. Override only what your integration needs, and never
override a derived parameter -- see the note under Parameters.

```systemverilog
axil5_master_rd #(
    .AXIL_ADDR_WIDTH     (32),
    .AXIL_DATA_WIDTH     (32),
    .USER_WIDTH          (4),
    .LOOP_WIDTH          (3),
    .MPAM_WIDTH          (11),
    .MECID_WIDTH         (16),
    .NSAID_WIDTH         (4),
    .ENABLE_USER         (1),
    .ENABLE_TRACE        (1),
    .ENABLE_LOOP         (1),
    .ENABLE_MPAM         (1),
    .ENABLE_MECID        (1),
    .ENABLE_NSAID        (1),
    .ENABLE_POISON       (1),
    .ENABLE_LOCK         (1),
    .SKID_DEPTH_AR       (2),
    .SKID_DEPTH_R        (4)
) u_axil5_master_rd (
    // clock/reset
    .aclk                (aclk),
    .aresetn             (aresetn),
    // fub_ar
    .fub_araddr          (fub_araddr),
    // ... `fub_arprot`, `fub_arlock`, `fub_aruser`, +7 more
    // m_axil_ar
    .m_axil_araddr       (m_axil_araddr),
    // ... `m_axil_arprot`, `m_axil_arlock`, `m_axil_aruser`, +7 more
    // m_axil_r
    .m_axil_rdata        (m_axil_rdata),
    // ... `m_axil_rresp`, `m_axil_ruser`, `m_axil_rtrace`, +4 more
    // fub_r
    .fub_rdata           (fub_rdata),
    // ... `fub_rresp`, `fub_ruser`, `fub_rtrace`, +4 more
    // status
    .busy                (busy)
);
```

---

## Design Notes

**All optional groups off is AXI4-Lite.** `ARSize`/`AWSize`/`WSize`/`RSize`/
`BSize` are conditional sums over the `ENABLE_*` parameters. Disable every
group and they collapse to the AXI4-Lite payload widths exactly, which is what
`val/amba/test_axil5_axil4_equivalence.py` asserts by running AXI5-Lite BFMs
against the AXI4-Lite RTL. If that test ever fails, AXI5-Lite has drifted from
the protocol it extends.

**Do not override a derived parameter.** The `*Size` parameters and the `AW`/
`DW` aliases are declared as `parameter` so the elaborator can compute them,
not so callers can set them. Forcing one to the AXI4-Lite value while a group
is enabled part-selects past the end of the vector -- the failure reads
"Extracting 4 bits from only 2 bit number", and it is how this family's test
port broke.

**No transaction IDs.** AXI4-Lite and AXI5-Lite have none, so anything
ID-shaped in the shared monitor core is inert here and the wrappers tie the ID
inputs to zero.

**The skid buffer is not a bypass.** `gaxi_skid_buffer` registers both
`rd_valid` and its storage, so every transfer costs one cycle even unstalled.
Depth buys backpressure absorption, not throughput.

---

## Related Modules

- [axil5_master_rd_cg](axil5_master_rd_cg.md)
- [axil5_master_rd_mon](axil5_master_rd_mon.md)
- [axil5_master_rd_mon_cg](axil5_master_rd_mon_cg.md)
- [axil5_master_wr](axil5_master_wr.md)
- [axil5_master_wr_cg](axil5_master_wr_cg.md)
- [axil5_master_wr_mon](axil5_master_wr_mon.md)
- [`axil4_master_rd`](../axil4/axil4_master_rd.md) -- the AXI4-Lite counterpart
- [AXI4-Lite modules](../axil4/README.md)

---

## Testing

`val/amba/test_axil5_master_rd.py` drives this module with the AXI5-Lite BFMs and **every optional group enabled** -- `TBClasses/axil5` sets the group widths in `COMPONENT_KWARGS` to mirror the RTL defaults. A BFM configured differently from its DUT is a bind failure, which is the loud version of the mistake.

The testbench class is the AXI4-Lite one with the component factories swapped, so every phase, check and randomizer sweep has a single definition, and a fix to the AXI4-Lite flow reaches this module automatically.

---

## Navigation

[AXI5-Lite index](README.md) | [AMBA overview](../overview.md)
