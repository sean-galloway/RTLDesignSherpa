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

# AXIL5 Slave Read Monitor

**Module:** `axil5_slave_rd_mon.sv`
**Location:** `rtl/amba/axil5/`
**AXI4-Lite counterpart:** [`axil4_slave_rd_mon`](../axil4/axil4_slave_rd_mon.md)

---

## Overview

The AXIL5 Slave Read Monitor provides a buffered AXI5-Lite read interface for slave devices.

AXI5-Lite is AXI4-Lite plus optional signal groups. It changes no channel's handshake, ordering or response semantics, so this module is structurally `axil4_slave_rd_mon` with those groups threaded through the packed SKID payload.

### Key Features

- AXI5-Lite read path (AR and R channels)
- Single-beat transactions: AXI-Lite has no burst support
- Configurable skid buffers on every channel for timing closure
- Eight optional signal groups, each independently enabled
- Bit-identical to the AXI4-Lite module of the same name with all groups disabled
- Integrated transaction monitor emitting monbus packets

---

## Parameters

| Parameter | Type | Default | Description |
|---|---|---|---|
| `SKID_DEPTH_AR` | int | `2` |  |
| `SKID_DEPTH_R` | int | `4` |  |
| `AXIL_ADDR_WIDTH` | int | `32` |  |
| `AXIL_DATA_WIDTH` | int | `32` |  |
| `ACLK_MHZ` | int | `100` |  |
| `CFI_MIN_FREQ_MHZ` | int | `ACLK_MHZ` |  |
| `CFI_MAX_FREQ_MHZ` | int | `ACLK_MHZ` |  |
| `USE_MONITOR` | bit | `1'b1` | 0 = omit monitor, tie outputs |
| `N_ADDR_RANGES` | int | `0` | 0 = address-range checker disabled |
| `MAX_TRANSACTIONS` | int | `8` | Maximum outstanding transactions (reduced for AXIL) |
| `USE_WDATA_ORDER_Q` | bit | `1'b0` |  |
| `NUM_BANKS` | int | `1` |  |
| `ID_FILTER_ENABLE` | bit | `1'b0` | Per-instance ID-slice filter, inherited from the shared monitor core. **Leave at 0 on AXI4-Lite.** The wrapper hardwires `cmd_id`/`data_id`/`resp_id` to `1'b0`, so enabling this with `ID_MATCH_BASE` above 0 makes `id_owned(0)` false for every transaction and drops ALL monitoring. |
| `ADDR_FILTER_ENABLE` | bit | `1'b0` |  |
| `ID_MATCH_BASE` | int | `0` | First ID this instance owns when `ID_FILTER_ENABLE=1`. Must stay 0 on AXI4-Lite -- every transaction reports ID 0. |
| `ID_MATCH_COUNT` | int | `0` | Number of IDs owned from `ID_MATCH_BASE`. 0 = all IDs (the filter passes everything). |
| `ACTIVE_TRANS_THRESHOLD` | int | `MAX_TRANSACTIONS / 2` |  |
| `ENABLE_FILTERING` | bit | `1` | Enable packet filtering |
| `ADD_PIPELINE_STAGE` | bit | `0` | Add register stage for timing closure |
| `ENABLE_ERROR_LOGIC` | bit | `1'b1` |  |
| `ENABLE_TIMEOUT_LOGIC` | bit | `1'b1` |  |
| `ENABLE_COMPL_LOGIC` | bit | `1'b1` |  |
| `ENABLE_THRESHOLD_LOGIC` | bit | `1'b1` |  |
| `ENABLE_PERF_LOGIC` | bit | `1'b1` |  |
| `ENABLE_DEBUG_LOGIC` | bit | `1'b0` |  |
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
| `AW` | int | `AXIL_ADDR_WIDTH` |  |
| `DW` | int | `AXIL_DATA_WIDTH` |  |
| `UW` | int | `USER_WIDTH` |  |
| `LW` | int | `LOOP_WIDTH` |  |
| `MW` | int | `MPAM_WIDTH` |  |
| `EW` | int | `MECID_WIDTH` |  |
| `NW` | int | `NSAID_WIDTH` |  |
| `PW` | int | `(DW / 64) > 0 ? (DW / 64) : 1` |  |

The derived parameters (`AW`, `DW`, `UW`, ... and the `*Size` payload widths) are computed from the ones above. **Do not override them.** Forcing a `*Size` to a value the RTL did not derive makes every optional-group field a part-select past the end of the vector -- which is exactly how `test_axil5_master_wr` failed until `d6266344` removed those overrides.

---

## Ports

| Port | Direction | Width | Description |
|---|---|---|---|
| `aclk` | Input | 1 |  |
| `aresetn` | Input | 1 |  |
| `cam_clear` | Input | 1 | sync clear of the monitor trans CAM |
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
| `s_axil_rdata` | Output | `[DW-1:0]` |  |
| `s_axil_rresp` | Output | `[1:0]` |  |
| `s_axil_ruser` | Output | `[UW-1:0]` |  |
| `s_axil_rtrace` | Output | 1 |  |
| `s_axil_rloop` | Output | `[LW-1:0]` |  |
| `s_axil_rpoison` | Output | `[PW-1:0]` |  |
| `s_axil_rvalid` | Output | 1 |  |
| `s_axil_rready` | Input | 1 |  |
| `fub_axil_araddr` | Output | `[AW-1:0]` |  |
| `fub_axil_arprot` | Output | `[2:0]` |  |
| `fub_axil_arlock` | Output | 1 |  |
| `fub_axil_aruser` | Output | `[UW-1:0]` |  |
| `fub_axil_artrace` | Output | 1 |  |
| `fub_axil_arloop` | Output | `[LW-1:0]` |  |
| `fub_axil_armpam` | Output | `[MW-1:0]` |  |
| `fub_axil_armecid` | Output | `[EW-1:0]` |  |
| `fub_axil_arnsaid` | Output | `[NW-1:0]` |  |
| `fub_axil_arvalid` | Output | 1 |  |
| `fub_axil_arready` | Input | 1 |  |
| `fub_axil_rdata` | Input | `[DW-1:0]` |  |
| `fub_axil_rresp` | Input | `[1:0]` |  |
| `fub_axil_ruser` | Input | `[UW-1:0]` |  |
| `fub_axil_rtrace` | Input | 1 |  |
| `fub_axil_rloop` | Input | `[LW-1:0]` |  |
| `fub_axil_rpoison` | Input | `[PW-1:0]` |  |
| `fub_axil_rvalid` | Input | 1 |  |
| `fub_axil_rready` | Output | 1 |  |
| `cfg_monitor_enable` | Input | 1 | Enable monitoring |
| `cfg_error_enable` | Input | 1 | Enable error detection |
| `cfg_timeout_enable` | Input | 1 | Enable timeout detection |
| `cfg_perf_enable` | Input | 1 | Enable performance monitoring |
| `cfg_compl_enable` | Input | 1 | Enable completion packets |
| `cfg_threshold_enable` | Input | 1 | Enable threshold packets |
| `cfg_debug_enable` | Input | 1 | Enable debug packets |
| `cfg_timeout_cycles` | Input | `[15:0]` | Timeout threshold in MICROSECONDS (1 us tick), despite the name |
| `cfg_freq_sel` | Input | `[3:0]` | counter_freq_invariant LUT index |
| `cfg_latency_threshold` | Input | `[31:0]` | Latency threshold for alerts |
| `cfg_axi_pkt_mask` | Input | `[15:0]` | Drop mask for packet types |
| `cfg_axi_err_select` | Input | `[15:0]` | Error select for packet types |
| `cfg_axi_error_mask` | Input | `[15:0]` | Individual error event mask |
| `cfg_axi_timeout_mask` | Input | `[15:0]` | Individual timeout event mask |
| `cfg_axi_compl_mask` | Input | `[15:0]` | Individual completion event mask |
| `cfg_axi_thresh_mask` | Input | `[15:0]` | Individual threshold event mask |
| `cfg_axi_perf_mask` | Input | `[15:0]` | Individual performance event mask |
| `cfg_axi_addr_mask` | Input | `[15:0]` | Individual address match event mask |
| `cfg_axi_debug_mask` | Input | `[15:0]` | Individual debug event mask |
| `cfg_addr_check_enable` | Input | 1 |  |
| `cfg_addr_range_enable` | Input | `[(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0]` |  |
| `cfg_addr_filter_enable` | Input | 1 |  |
| `cfg_addr_filter_low` | Input | `[AW-1:0]` |  |
| `cfg_addr_filter_high` | Input | `[AW-1:0]` |  |
| `monbus_valid` | Output | 1 | Monitor bus valid |
| `monbus_ready` | Input | 1 | Monitor bus ready |
| `busy` | Output | 1 |  |
| `active_transactions` | Output | `[7:0]` | Number of active transactions |
| `error_count` | Output | `[15:0]` | Total error count |
| `transaction_count` | Output | `[31:0]` | Total transaction count |
| `debug_block_ready` | Output | 1 |  |
| `cfg_conflict_error` | Output | 1 | Configuration conflict detected |
| `cfg_start_event_sel` | Input | `[2:0]` |  |
| `cfg_end_event_sel` | Input | `[2:0]` |  |
| `cfg_start_trigger` | Input | 1 |  |
| `cfg_end_trigger` | Input | 1 |  |
| `cfg_window_force_close` | Input | 1 |  |
| `window_active` | Output | 1 |  |
| `window_cycles` | Output | `[31:0]` |  |
| `perf_prod_cycles` | Output | `[31:0]` |  |
| `perf_bp_cycles` | Output | `[31:0]` |  |
| `perf_starv_cycles` | Output | `[31:0]` |  |
| `perf_idle_cycles` | Output | `[31:0]` |  |
| `perf_beat_count` | Output | `[31:0]` |  |
| `perf_byte_count` | Output | `[63:0]` |  |
| `perf_burst_count` | Output | `[31:0]` |  |

---

## AXI5-Lite Optional Signal Groups

Eight groups, each gated by its own `ENABLE_*` parameter. A group contributes
to the packed SKID payload only when enabled.

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

(Only the channels this module carries are present; a read module has no W or
B channel, so it has no WPOISON or BUSER.)

### With every group disabled, this IS the AXI4-Lite module

The packed payload width of a fully-disabled build equals its AXI4-Lite
counterpart's, channel for channel:

| Payload | AXI4-Lite | AXI5-Lite, groups off | AXI5-Lite, groups on |
|---|---|---|---|
| `ARSize` | 35 | 35 | 75 |
| `RSize` | 34 | 34 | 43 |
| `AWSize` | 35 | 35 | 75 |
| `WSize` | 36 | 36 | 41 |
| `BSize` | 2 | 2 | 10 |

(at `AXIL_ADDR_WIDTH = AXIL_DATA_WIDTH = 32` and the default group widths.)

That equivalence is what `val/amba/test_axil5_master_rd.py` relies on when it
drives AXI4-Lite RTL with AXI5-Lite BFMs: with no groups enabled an AXI5-Lite
interface *is* an AXI4-Lite interface, so the same testbench binds to either.

### It transports; it does not interpret

MPAM, MECID, NSAID, LOOP and TRACE are carried end to end unmodified. POISON is
carried, never generated and never checked. LOCK is carried with no
exclusive-access monitor behind it. Those behaviours belong to the endpoints on
either side, and nothing in this module implements them.

A disabled group's OUTPUT is driven to zero rather than left dangling, so an
integrator who disables a group downstream of one that enables it sees a
defined value instead of X.

---

## Notes for the monitored variants

**The monitor does not observe the optional groups.** `axi_monitor_filtered`
has no ports for MPAM, MECID, NSAID, TRACE, LOOP or POISON, so it sees exactly
what it sees on AXI4-Lite: handshakes, addresses, responses and timing. It does
not check MPAM/MECID/NSAID consistency and does not validate POISON.

**`ACLK_MHZ` is not decoration.** It builds the microsecond tick LUT in
`counter_freq_invariant`. Leave it at the 100 MHz default on a 90 MHz part and
every microsecond-denominated timeout is wrong, silently.

**`NUM_BANKS` > 1 on a WRITE monitor requires `USE_WDATA_ORDER_Q = 1`.**
`axi_monitor_trans_mgr` fails elaboration otherwise; the error names the
combination.

**A filter parameter only decides whether the logic is SYNTHESISED.** A build
that sets `ADDR_FILTER_ENABLE` but leaves `cfg_addr_filter_enable` low filters
nothing and looks broken. The parameter and the runtime port are both required.

---

## Verification

`val/amba/test_axil5_slave_rd_mon.py` drives this module with the AXI5-Lite BFMs and **every optional group enabled** -- `TBClasses/axil5` sets the group widths in `COMPONENT_KWARGS` to mirror the RTL defaults. A BFM configured differently from its DUT is a bind failure, which is the loud version of the mistake.

The testbench class is the AXI4-Lite one with the component factories swapped, so every phase, check and randomizer sweep has a single definition and a fix to the AXI4-Lite flow reaches this module automatically.

---

## Related Modules

- [axil5_master_rd](axil5_master_rd.md)
- [axil5_master_rd_cg](axil5_master_rd_cg.md)
- [axil5_master_rd_mon](axil5_master_rd_mon.md)
- [axil5_master_rd_mon_cg](axil5_master_rd_mon_cg.md)
- [axil5_master_wr](axil5_master_wr.md)
- [axil5_master_wr_cg](axil5_master_wr_cg.md)
- [`axil4_slave_rd_mon`](../axil4/axil4_slave_rd_mon.md) -- the AXI4-Lite counterpart
- [AXI4-Lite modules](../axil4/README.md)

---

## Navigation

[AXI5-Lite index](README.md) | [AMBA overview](../overview.md)
