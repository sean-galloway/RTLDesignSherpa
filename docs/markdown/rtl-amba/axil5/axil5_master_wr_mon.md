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

# AXIL5 Master Write Monitor

**Module:** `axil5_master_wr_mon.sv`
**Location:** `rtl/amba/axil5/`
**AXI4-Lite counterpart:** [`axil4_master_wr_mon`](../axil4/axil4_master_wr_mon.md)

---

## Overview

The AXIL5 Master Write Monitor provides a buffered AXI5-Lite write interface for master devices.

AXI5-Lite is AXI4-Lite plus the transaction ID and a few optional signal groups. It changes no channel's handshake, ordering or response semantics, so this module is structurally `axil4_master_wr_mon` with the ID and those groups threaded through the packed SKID payload.

- AXI5-Lite write path (AW, W and B channels)
- Single-beat transactions: AXI-Lite has no burst support
- Configurable skid buffers on every channel for timing closure
- Elaboration fails on an illegal `AXIL_DATA_WIDTH` or `ID_WIDTH`
- Transaction ID (`AWID`/`BID`, `ARID`/`RID`; `ID_WIDTH`) plus three optional signal groups (USER, TRACE, POISON), each independently enabled
- Bit-identical to the AXI4-Lite module of the same name with `ID_WIDTH=0` and all groups disabled
- Integrated transaction monitor emitting monbus packets

---

## Parameters

> A lite-monitor version of this wrapper exists as [`axil5_master_wr_monlite`](../monitor/axi_monitor_lite_wrappers.md): the same core and taps with `axi_monitor_lite` instead of `axi_monitor_filtered`, about a fifth of the monitor gates, error/timeout/completion/threshold packets only. Selected in generated bridges by `mon_preset = "lite"`.

| Parameter | Type | Default | Description |
|---|---|---|---|
| `SKID_DEPTH_AW` | int | `2` |  |
| `SKID_DEPTH_W` | int | `2` |  |
| `SKID_DEPTH_B` | int | `2` |  |
| `AXIL_ADDR_WIDTH` | int | `32` |  |
| `AXIL_DATA_WIDTH` | int | `32` | Any AXI data width, 8..1024 and a power of two (IHI 0022L Table A3.19; Table B2.4 adds no AXI5-Lite limit). Checked at elaboration. |
| `ACLK_MHZ` | int | `100` |  |
| `CFI_MIN_FREQ_MHZ` | int | `ACLK_MHZ` |  |
| `CFI_MAX_FREQ_MHZ` | int | `ACLK_MHZ` |  |
| `USE_MONITOR` | bit | `1'b1` | 0 = omit monitor, tie outputs |
| `N_ADDR_RANGES` | int | `0` | 0 = address-range checker disabled |
| `MAX_TRANSACTIONS` | int | `8` | Maximum outstanding transactions (reduced for AXIL) |
| `USE_WDATA_ORDER_Q` | bit | `1'b0` |  |
| `NUM_BANKS` | int | `1` |  |
| `ID_FILTER_ENABLE` | bit | `1'b0` | Per-instance ID-slice filter, inherited from the shared monitor core. Since amba #104 the wrapper feeds the AXI5-Lite ID, so the slice selects on AxID as on the AXI4 wrappers. |
| `ADDR_FILTER_ENABLE` | bit | `1'b0` |  |
| `ID_MATCH_BASE` | int | `0` | First ID this instance owns when `ID_FILTER_ENABLE=1`. Compared against the AXI5-Lite AxID. |
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
| `ID_WIDTH` | int | `4` | AWID/BID and ARID/RID width, 0..32; 0 = no ID (Manager side, Table B2.2 code YS). IHI 0022L Table A5.2. |
| `USER_WIDTH` | int | `4` |  |
| `ENABLE_USER` | bit | `1` |  |
| `ENABLE_TRACE` | bit | `1` |  |
| `ENABLE_POISON` | bit | `1` |  |
| `AW` | int | `AXIL_ADDR_WIDTH` |  |
| `DW` | int | `AXIL_DATA_WIDTH` |  |
| `IW` | int | `(ID_WIDTH > 0) ? ID_WIDTH : 1` | ID port width; a 1-bit placeholder when `ID_WIDTH = 0` |
| `UW` | int | `USER_WIDTH` |  |
| `PW` | int | `(DW / 64) > 0 ? (DW / 64) : 1` |  |
| `AGENT_ID` |  | `16'h000B` | Agent identifier emitted in the `agent_id` field of every monitor packet. Pairs with `UNIT_ID` to identify the packet source. (16-bit Agent ID for monitor packets) |
| `UNIT_ID` |  | `8'h01` | Unit identifier emitted in the `unit_id` field of every monitor packet. Give each monitored interface a distinct value or the packets cannot be told apart at the collector. (8-bit Unit ID for monitor packets) |

The derived parameters (`AW`, `DW`, `UW`, ... and the `*Size` payload widths) are computed from the ones above. **Do not override them.** Forcing a `*Size` to a value the RTL did not derive makes every optional-group field a part-select past the end of the vector -- which is exactly how `test_axil5_master_wr` failed until `d6266344` removed those overrides.

---

## Ports

Your logic drives the `fub_axil_*` side; the `m_axil_*` side faces the bus. The `cfg_*` and `monbus_*` ports belong to the monitor.

| Port | Direction | Width | Description |
|---|---|---|---|
| `aclk` | Input | 1 |  |
| `aresetn` | Input | 1 |  |
| `cam_clear` | Input | 1 | sync clear of the monitor trans CAM |
| `fub_axil_awid` | Input | `[IW-1:0]` |  |
| `fub_axil_awaddr` | Input | `[AW-1:0]` |  |
| `fub_axil_awprot` | Input | `[2:0]` |  |
| `fub_axil_awuser` | Input | `[UW-1:0]` |  |
| `fub_axil_awtrace` | Input | 1 |  |
| `fub_axil_awvalid` | Input | 1 |  |
| `fub_axil_awready` | Output | 1 |  |
| `fub_axil_wdata` | Input | `[DW-1:0]` |  |
| `fub_axil_wstrb` | Input | `[DW/8-1:0]` |  |
| `fub_axil_wuser` | Input | `[UW-1:0]` |  |
| `fub_axil_wpoison` | Input | `[PW-1:0]` |  |
| `fub_axil_wvalid` | Input | 1 |  |
| `fub_axil_wready` | Output | 1 |  |
| `fub_axil_bid` | Output | `[IW-1:0]` |  |
| `fub_axil_bresp` | Output | `[1:0]` |  |
| `fub_axil_buser` | Output | `[UW-1:0]` |  |
| `fub_axil_btrace` | Output | 1 |  |
| `fub_axil_bvalid` | Output | 1 |  |
| `fub_axil_bready` | Input | 1 |  |
| `m_axil_awid` | Output | `[IW-1:0]` |  |
| `m_axil_awaddr` | Output | `[AW-1:0]` |  |
| `m_axil_awprot` | Output | `[2:0]` |  |
| `m_axil_awuser` | Output | `[UW-1:0]` |  |
| `m_axil_awtrace` | Output | 1 |  |
| `m_axil_awvalid` | Output | 1 |  |
| `m_axil_awready` | Input | 1 |  |
| `m_axil_wdata` | Output | `[DW-1:0]` |  |
| `m_axil_wstrb` | Output | `[DW/8-1:0]` |  |
| `m_axil_wuser` | Output | `[UW-1:0]` |  |
| `m_axil_wpoison` | Output | `[PW-1:0]` |  |
| `m_axil_wvalid` | Output | 1 |  |
| `m_axil_wready` | Input | 1 |  |
| `m_axil_bid` | Input | `[IW-1:0]` |  |
| `m_axil_bresp` | Input | `[1:0]` |  |
| `m_axil_buser` | Input | `[UW-1:0]` |  |
| `m_axil_btrace` | Input | 1 |  |
| `m_axil_bvalid` | Input | 1 |  |
| `m_axil_bready` | Output | 1 |  |
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
| `monbus_packet` | Output | `monitor_packet_t` (128) | The monitor packet itself -- the module's primary output. Valid when `monbus_valid` is high. |
| `monbus_timestamp` | Output | `monbus_timestamp_t` | Side-band sampled time for the packet on `monbus_packet`. |
| `i_mon_time` | Input | `monbus_timestamp_t` | Shared free-running timestamp, driven from the group/aggregator so every monitor stamps against one clock. |
| `cfg_addr_range_low` | Input | `[AW-1:0]` x `N_ADDR_RANGES` | Low bound of each address-range comparator; only present when `N_ADDR_RANGES > 0`. |
| `cfg_addr_range_high` | Input | `[AW-1:0]` x `N_ADDR_RANGES` | High bound of each address-range comparator; pairs with `cfg_addr_range_low`. |
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

## Functional Description

### Optional signal groups

The ID plus three optional groups -- the ones IHI 0022L Table B2.2 allows on AXI5-Lite. The ID has no enable (it is sized by `ID_WIDTH`); each group is gated by its own `ENABLE_*` parameter and contributes to the packed SKID payload only when enabled.

| Group | Parameter | Signals on this module | Width |
|---|---|---|---|
| ID | `ID_WIDTH` (no enable) | `AxID`, `BID`, `RID` | `ID_WIDTH` (0..32; >= 1 on slave-side modules) |
| USER | `ENABLE_USER` | `AxUSER`, `WUSER`, `BUSER`, `RUSER` | `USER_WIDTH` |
| TRACE | `ENABLE_TRACE` | `AxTRACE`, `BTRACE`, `RTRACE` | 1 |
| POISON | `ENABLE_POISON` | `WPOISON`, `RPOISON` | one bit per 64 data bits |

(Only the channels this module carries are present; a read module has no W or B channel, so it has no WPOISON or BUSER.)

### With no ID and every group disabled, this IS the AXI4-Lite module

The packed payload width of a no-ID, fully-disabled build equals its AXI4-Lite counterpart's, channel for channel:

| Payload | AXI4-Lite | AXI5-Lite, `ID_WIDTH=0`, groups off | AXI5-Lite defaults (`ID_WIDTH=4`, groups on) |
|---|---|---|---|
| `ARSize` | 35 | 35 | 44 |
| `RSize` | 34 | 34 | 44 |
| `AWSize` | 35 | 35 | 44 |
| `WSize` | 36 | 36 | 41 |
| `BSize` | 2 | 2 | 11 |

(at `AXIL_ADDR_WIDTH = AXIL_DATA_WIDTH = 32` and the default widths. `ID_WIDTH = 0` is legal only on the Manager-side `axil5_master_*` modules; a Subordinate must carry the ID, so the `axil5_slave_*` modules require `ID_WIDTH >= 1` and their minimum payload is the AXI4-Lite one plus the ID on AR/R or AW/B.)

That equivalence is what `val/amba/test_axil5_axil4_equivalence.py` pins: it runs the same AXI5-Lite BFMs, built with no ID and no groups, against both `axil4_master_rd` and `axil5_master_rd` elaborated with `ID_WIDTH=0` and every `ENABLE_*` = 0.

### It transports; it does not interpret

The ID is carried in both directions like every other field: AxID crosses with the request, and BID/RID cross back with the response unchanged. Reflecting AxID onto BID/RID is the Subordinate's job (IHI 0022L A5.1.1); this module only guarantees that whatever ID it is given leaves on the other side. With `ID_WIDTH = 0` (Manager-side modules only) the ID outputs are driven 0 -- the "tied LOW" of A5.1.1 -- and the ID inputs are ignored.

TRACE and USER are carried end to end unmodified. POISON is carried -- never generated, never checked. Those behaviours belong to the endpoints on either side, and nothing in this module implements them.

AxLOCK, AxMPAM, AxMECID, AxNSAID and xLOOP are not carried. Table B2.2 of IHI 0022L marks them "not present" on AXI5-Lite and B2.1.5 states exclusive accesses are not supported; earlier versions of this module carried them behind `ENABLE_*` parameters (removed by issue #102).

A disabled group's output is driven to zero rather than left dangling, so an integrator who disables a group downstream of one that enables it sees a defined value instead of X.

---

## Design Notes

Four things worth knowing before you trust what comes out of the monitor:

**The monitor observes the ID, not the optional groups.** Since amba #104 the wrapper feeds AxID and BID/RID to `axi_monitor_filtered`, so a Subordinate that reorders responses across IDs (permitted on AXI5-Lite, IHI 0022L B2.1.5) has each response paired with its own transaction, and a completion packet carries the ID as its channel. W carries no ID and is attributed in AW order (A5.5), including W that arrives ahead of its AW (A2.6). The full monitor keys on at most 8 ID bits, so `ID_WIDTH` > 8 is refused at elaboration here (the `_monlite` wrappers take any width). There are no ports for TRACE, USER or POISON, and POISON is not validated.

**`ACLK_MHZ` is not decoration.** It builds the microsecond tick LUT in `counter_freq_invariant`. Leave it at the 100 MHz default on a 90 MHz part and every microsecond-denominated timeout is wrong, silently.

**`NUM_BANKS` > 1 on a WRITE monitor requires `USE_WDATA_ORDER_Q = 1`.** `axi_monitor_trans_mgr` fails elaboration otherwise; the error names the combination.

**A filter parameter only decides whether the logic is SYNTHESISED.** A build that sets `ADDR_FILTER_ENABLE` but leaves `cfg_addr_filter_enable` low filters nothing and looks broken. The parameter and the runtime port are both required.

---

## Timing Characteristics

### Buffer Depths and Latency

| Parameter | Default | Channel |
|-----------|---------|---------|
| `SKID_DEPTH_AW` | 2 entries | Skid depth on the AW channel |
| `SKID_DEPTH_W` | 2 entries | Skid depth on the W channel |
| `SKID_DEPTH_B` | 2 entries | Skid depth on the B channel |

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
axil5_master_wr_mon #(
    .SKID_DEPTH_AW       (2),
    .SKID_DEPTH_W        (2),
    .SKID_DEPTH_B        (2),
    .AXIL_ADDR_WIDTH     (32),
    .AXIL_DATA_WIDTH     (32),
    .ACLK_MHZ            (100),
    .USE_MONITOR         (1'b1),
    .N_ADDR_RANGES       (0),
    .UNIT_ID             (8'h01),
    .AGENT_ID            (16'h000B),
    .MAX_TRANSACTIONS    (8),
    .USE_WDATA_ORDER_Q   (1'b0),
    .NUM_BANKS           (1),
    .ID_FILTER_ENABLE    (1'b0),
    .ADDR_FILTER_ENABLE  (1'b0),
    .ID_MATCH_BASE       (0),
    .ID_MATCH_COUNT      (0),
    .ENABLE_FILTERING    (1),
    .ADD_PIPELINE_STAGE  (0),
    .ENABLE_ERROR_LOGIC  (1'b1),
    .ENABLE_TIMEOUT_LOGIC(1'b1),
    .ENABLE_COMPL_LOGIC  (1'b1),
    .ENABLE_THRESHOLD_LOGIC(1'b1),
    .ENABLE_PERF_LOGIC   (1'b1),
    .ENABLE_DEBUG_LOGIC  (1'b0),
    .ID_WIDTH            (4),
    .USER_WIDTH          (4),
    .ENABLE_USER         (1),
    .ENABLE_TRACE        (1),
    .ENABLE_POISON       (1)
) u_axil5_master_wr_mon (
    // clock/reset
    .aclk                (aclk),
    .aresetn             (aresetn),
    // status
    .cam_clear           (cam_clear),
    // ... `fub_axil_awaddr`, `fub_axil_awprot`, `fub_axil_awlock`, +35 more
    // m_axil_aw
    .m_axil_awid         (m_axil_awid),
    // ... `m_axil_awaddr`, `m_axil_awprot`, `m_axil_awuser`, +3 more
    // m_axil_w
    .m_axil_wdata        (m_axil_wdata),
    // ... `m_axil_wstrb`, `m_axil_wuser`, `m_axil_wpoison`, +2 more
    // m_axil_b
    .m_axil_bid          (m_axil_bid),
    // ... `m_axil_bresp`, `m_axil_buser`, `m_axil_btrace`, +2 more
    // configuration
    .cfg_monitor_enable  (cfg_monitor_enable),
    // ... `cfg_error_enable`, `cfg_timeout_enable`, `cfg_perf_enable`, +28 more
    // monitor bus
    .monbus_valid        (monbus_valid)
    // ... `monbus_ready`, `monbus_packet`, `monbus_timestamp`
);
```

---

## Related Modules

- [axil5_master_rd](axil5_master_rd.md)
- [axil5_master_rd_cg](axil5_master_rd_cg.md)
- [axil5_master_rd_mon](axil5_master_rd_mon.md)
- [axil5_master_rd_mon_cg](axil5_master_rd_mon_cg.md)
- [axil5_master_wr](axil5_master_wr.md)
- [axil5_master_wr_cg](axil5_master_wr_cg.md)
- [`axil4_master_wr_mon`](../axil4/axil4_master_wr_mon.md) -- the AXI4-Lite counterpart
- [AXI4-Lite modules](../axil4/README.md)

---

## Testing

`val/amba/test_axil5_master_wr_mon.py` drives this module with the AXI5-Lite BFMs and **the ID and every optional group enabled** -- `TBClasses/axil5` sets the group widths in `COMPONENT_KWARGS` to mirror the RTL defaults. A BFM configured differently from its DUT is a bind failure, which is the loud version of the mistake.

Every transaction the Manager-side BFM issues carries a rotating non-zero ID and must come back with the same BID/RID (`bin/TBClasses/axil5/axil5_id_check.py`); the inherited AXI4-Lite phases alone would only ever send ID 0, which a module that dropped the ID would pass.

The testbench class is the AXI4-Lite one with the component factories swapped, so every phase, check and randomizer sweep has a single definition, and a fix to the AXI4-Lite flow reaches this module automatically.

## References

- Arm. *AMBA AXI Protocol Specification*, ARM IHI 0022, Issue L, Aug. 2025. [developer.arm.com/documentation/ihi0022/l](https://developer.arm.com/documentation/ihi0022/l) -- §B2.1.5 "AXI5-Lite" and Table B2.2 signal matrix; carried groups per §A12.5 User defined signaling, §A12.3 Trace signals, §A5.1.1 transaction ID signals, §A16.1 Poison; handshake on the AW, W and B channels per §A2.3.1/§A2.3.2; register stages per §A2.5. Table B2.2 marks AxLOCK, AxMPAM, AxMECID, AxNSAID and xLOOP not present on AXI5-Lite and AxID/BID/RID mandatory on a Subordinate (YS): this module carries the ID (`ID_WIDTH`) and none of the not-present signals (issue #102). Data width per Table A3.19 (any AXI DATA_WIDTH; Table B2.4 adds no AXI5-Lite constraint).
- Arm. *AMBA AXI and ACE Protocol Specification*, ARM IHI 0022, Issue H, 2020. [developer.arm.com/documentation/ihi0022/h](https://developer.arm.com/documentation/ihi0022/h) -- Part C ch. C2 "AMBA AXI5-Lite", §C2.2 comparison with AXI4-Lite and §C2.5/§C2.6 upgrading an AXI4-Lite master/slave: the `ID_WIDTH=0`, every-group-disabled Manager-side build is the AXI4-Lite-equivalent port.
- Cortadella, J., Kishinevsky, M., Grundmann, B. "Synthesis of Synchronous Elastic Architectures." *Proc. 43rd Design Automation Conf. (DAC '06)*, pp. 657-662, 2006. DOI: [10.1145/1146909.1147077](https://doi.org/10.1145/1146909.1147077) -- the elastic buffer; its Property 3.1 (capacity C >= 2 for full throughput) is the depth-2 floor of each channel's `gaxi_skid_buffer`.
- The monitor itself (`axi_monitor_filtered`) is referenced in the [monitor pages](../monitor/axi_monitor_base.md); on this port it sees single-beat transactions carrying the AXI5-Lite ID (IHI 0022L B2.1.5; W in AW order, A5.5).
- Chipressian. *Crack the Hardware Interview -- from RTL Designers' Perspective: Architecture and Micro-architecture Design*, ch. 2 "Handshake Protocols", Q8 valid-ready protocol and Q9 valid-ready slices -- textbook treatment of register slices (secondary source).
- Indexed in `rtl/amba/references/README.md` (local PDF: `ElasticBuffer__Cortadella2006.pdf`)

---

## Navigation

[AXI5-Lite index](README.md) | [AMBA overview](../overview.md)
