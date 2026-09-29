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

# AXI4-Stream Interface Observer

**Module:** `axis4_intf_observer.sv`
**Location:** `projects/components/utility-ip/misc/rtl/`
**Status:** Verified in simulation (2026-09-27); not yet on a board

---

## Overview

The AXI4-Stream interface observer is the AXIS sibling of
`axi4_intf_master_observer` and `axi4_intf_slave_observer`. It sits beside any
AXI4-Stream link -- a DMA's sink ingress, a source egress, a switch port -- and
watches it without driving anything: every `obs_axis_*` pin is an input, the
handshake's `tready` included, so attaching the block cannot change the stream
it measures (`vault/handbook/design/observers-do-not-drive.md`).

It shares everything an integrator or a host tool touches with the AXI
observers: the same `obs_regs` register map behind the same APB window, the
same `OBS_STAT_SEL` / `OBS_STAT_DATA` telemetry readback, the same monbus egress
(AXIL slave-read drain plus `irq_out`, and a bulk-dump master in either AXI4 or
AXIL flavour). One host decoder and one generated regmap serve all three.

### Key Features

- Per port, an `axis_bus_meter`: productive / backpressure / starvation / idle
  cycle buckets, per-`tid` channel buckets, and exact bytes (from `tstrb`),
  beats and packets. The meter lives outside the tap gate and counts in every
  build.
- Per port, an AXIS event tap emitting `PROTOCOL_AXIS` monbus packets in the
  six classes the packet vocabulary defines for a stream: Error, Timeout,
  Completion, Credit, Channel and Stream. There is no Threshold class for AXIS,
  which is why `MON_LATENCY` drives a Credit/BACKPRESSURE event here.
- Written in the monitor-lite discipline: no transaction CAM, no timer pool,
  microsecond stamps instead of per-transaction counters, and an event the
  monbus cannot take is dropped and counted (`OBS_STICKY.TAP_BLOCKED`,
  `METRIC 15`) rather than stalling anything.
- `MON_CTRL` bit-for-bit with the AXI observers, `OBS_CAPS0` reporting the
  same bit for the cone each enable gates, so host code that already walks an
  AXI observer needs only the class names changed.

No AXIS monitor exists in `rtl/amba/monitor` -- the AXI observers wrap
`axi4_*_monlite`, but there was never an `axis4_*` counterpart -- so the tap is
written in this module rather than wrapped.

---

## Parameters

| Parameter | Type | Default | Description |
|---|---|---|---|
| `NUM_PORTS` | int | 1 | Observed AXIS links. Each gets a meter and a tap. |
| `DATA_WIDTH` | int | 512 | `tdata` width; `SW = DATA_WIDTH/8` is the `tstrb` width. |
| `AXIS_ID_WIDTH` | int | 8 | `tid` width. Its low `$clog2(NUM_CHANNELS)` bits pick the meter's channel bucket. |
| `AXIS_DEST_WIDTH` | int | 4 | `tdest` width. |
| `AXIS_USER_WIDTH` | int | 1 | `tuser` width (observed, not interpreted). |
| `ADDR_WIDTH` | int | 32 | Address width of the egress masters and the AXIL drain. |
| `OBS_AXI_ID_WIDTH` | int | 4 | ID width of the AXI4 bulk-dump master. |
| `MAX_BURST_BEATS` | int | 64 | Bulk-dump burst length, 1..256. |
| `FIFO_DEPTH_ERR` / `FIFO_DEPTH_WRITE` | int | 64 / 96 | Monbus group err FIFO entries / write FIFO beats. |
| `FLUSH_TIMEOUT_CYCLES` | int | 1024 | Group bulk-write flush timeout. |
| `USE_COMPRESSION` | int | 0 | Monbus record compression in the group. |
| `EGRESS_AXIL` | bit | 0 | 0 = AXI4 burst dump on `m_axi_*`; 1 = AXIL dump on `m_axil_*`. Both port sets always exist; the unused one is driven to zero. |
| `ACLK_MHZ` | int | 100 | Clock the block is built for. Must land on the CFI LUT grid (`60 + 5i`), or elaboration fails: `MON_TIMEOUT` is in microseconds and the tick would otherwise be inexact. |
| `CFI_MIN_FREQ_MHZ` / `CFI_MAX_FREQ_MHZ` | int | 60 / 135 | CFI LUT bounds, 16 linear entries. |
| `ENABLE_MON_TAPS` | bit | 1 | Build-time arm for the taps. `MON_CTRL.MONITOR_EN` is ANDed with it. Meters are not gated. |
| `UNIT_ID` | logic [7:0] | 8'h11 | `unit_id` in every packet. The AXI observers use 8'h10. |
| `TAP_ENABLE_ERROR_LOGIC` | bit | 0 | Build the Error cone. |
| `TAP_ENABLE_TIMEOUT_LOGIC` | bit | 0 | Build the Timeout cone. |
| `TAP_ENABLE_COMPL_LOGIC` | bit | 0 | Build the Completion cone. |
| `TAP_ENABLE_CREDIT_LOGIC` | bit | 0 | Build the Credit cone. |
| `TAP_ENABLE_STREAM_LOGIC` | bit | 0 | Build the Stream cone. |
| `TAP_ENABLE_CHANNEL_LOGIC` | bit | 0 | Build the Channel cone. |
| `APB_ADDR_WIDTH` | int | 12 | APB window width. Must cover the regblock's derived cpuif width, checked at elaboration. |
| `ENABLE_BUS_METER` | bit | 1 | 0 omits the meters; every meter metric reads 0. |
| `NUM_CHANNELS` | int | 1 | Per-`tid` meter buckets per port. 1 = aggregate only. |

A cone that is not built is constant-pruned; its runtime enable does nothing
and `OBS_CAPS0` reports it absent.

---

## Ports

All `obs_axis_*` ports are packed `[NUM_PORTS-1:0]` arrays and are inputs.

| Group | Ports | Notes |
|---|---|---|
| Clock / reset | `aclk`, `aresetn` | One domain for the observed stream, the APB and the egress. |
| APB slave | `s_apb_psel`, `s_apb_penable`, `s_apb_pready`, `s_apb_paddr[APB_ADDR_WIDTH-1:0]`, `s_apb_pwrite`, `s_apb_pwdata[31:0]`, `s_apb_pstrb[3:0]`, `s_apb_prdata[31:0]`, `s_apb_pslverr` | The `obs_regs` window. |
| `cam_clear` | in | Clears the group's compressor CAM and every tap's drop counter. |
| Observed stream | `obs_axis_tdata[DATA_WIDTH-1:0]`, `obs_axis_tstrb[SW-1:0]`, `obs_axis_tlast`, `obs_axis_tid[AXIS_ID_WIDTH-1:0]`, `obs_axis_tdest[AXIS_DEST_WIDTH-1:0]`, `obs_axis_tuser[AXIS_USER_WIDTH-1:0]`, `obs_axis_tvalid`, `obs_axis_tready` | Inputs only. `tready` is observed, never produced. |
| AXIL drain | `s_axil_arvalid`, `s_axil_arready`, `s_axil_araddr[ADDR_WIDTH-1:0]`, `s_axil_arprot[2:0]`, `s_axil_rvalid`, `s_axil_rready`, `s_axil_rdata[63:0]`, `s_axil_rresp[1:0]` | Host reads the err FIFO, three beats per record. |
| AXI4 dump master | `m_axi_aw*`, `m_axi_w*`, `m_axi_b*` (64-bit data) | Live when `EGRESS_AXIL=0`; zero otherwise. |
| AXIL dump master | `m_axil_aw*`, `m_axil_w*`, `m_axil_b*` (64-bit data) | Live when `EGRESS_AXIL=1`; zero otherwise. |
| `irq_out` | out | Asserted while the err FIFO holds any record. |
| Meter window | `i_meter_clear[NUM_PORTS-1:0]`, `i_meter_freeze[NUM_PORTS-1:0]` | PER PORT: bit i clears / freezes port i's meter (same contract as `axi_bus_meter`). Per port because one observer's ports usually belong to different transfers (a sink's ingress streams before its write side is busy); the rapids harness drives its sink-ingress window on port 0 and its main window on port 1. |

---

## What the tap emits

Every packet is `PROTOCOL_AXIS`, `channel_id` = `tid` (low 9 bits),
`agent_id` = `{8'h00, 4'h2, port[3:0]}`, `unit_id` = `UNIT_ID`. Event codes
are `monitor_amba4_pkg`'s `axis_*_code_t` values.

| Class | Code | Fires when | `event_data[63:0]` |
|---|---|---|---|
| Error | `AXIS_ERR_VALID_TIMING` (2) | `tvalid` was high and unaccepted, then dropped | `{stall cycles[31:0], packets done[31:0]}` |
| Error | `AXIS_ERR_STRB_INVALID` (5) | a beat handshook with `tstrb == 0` | `{beats in packet, packets done}` |
| Timeout | `AXIS_TIMEOUT_HANDSHAKE` (0) | a stall reached `MON_TIMEOUT` microseconds (once per stall) | `{stall cycles, age us[15:0], limit us[15:0]}` |
| Timeout | `AXIS_TIMEOUT_PACKET` (2) | an open packet saw no beat for `MON_TIMEOUT` microseconds (once per gap) | `{beats in packet, age us, limit us}` |
| Completion | `AXIS_COMPL_STREAM_END` (0) | `tlast` handshook | `{tid[15:0], tdest[15:0], beats in packet[31:0]}` |
| Credit | `AXIS_CREDIT_BACKPRESSURE` (5) | a stall reached `MON_LATENCY` cycles (once per stall) | `{stall cycles, MON_LATENCY}` |
| Channel | `AXIS_CHAN_ID_CHANGE` (5) | `tid` differs from the previous beat of the packet (once per change) | `{previous tid[15:0], this tid[15:0], beats}` |
| Channel | `AXIS_CHAN_DEST_CHANGE` (6) | `tdest` differs from the previous beat of the packet | `{previous tdest, this tdest, beats}` |
| Stream | `AXIS_STREAM_START` (0) | first beat of a packet handshook | `{tid, tdest, packets done}` |
| Stream | `AXIS_STREAM_PAUSE` (2) | `tvalid` dropped inside a packet (a source bubble) | `{beats in packet, packets done}` |
| Stream | `AXIS_STREAM_RESUME` (3) | `tvalid` returned after a pause | `{beats in packet, packets done}` |

When several classes fire in one cycle the priority is Error, Timeout,
Completion, Credit, Channel, Stream; every loser is counted in the port's drop
counter, as is a winner that arrives while the port's one-deep holding
register is still waiting on the arbiter. A non-zero drop count means the
packet stream undercounts, which is what `OBS_STICKY.TAP_BLOCKED` says.

Not checked: `tdata` stability across a stall. That costs `DATA_WIDTH` flops
and a `DATA_WIDTH` compare per port (512 each at the rapids width) for a
violation no DMA in the tree can commit.

---

## Registers

The map is `projects/components/utility-ip/misc/rtl/obs_regs.rdl`, shared with the AXI
observers and regenerated through `bin/peakrdl_generate.py`. What differs is
meaning, not layout.

**`MON_CTRL`** gates the cones. The bit positions are the AXI observers'; the
class each gates here:

| Bit | Field | AXIS class |
|---|---|---|
| 0 | `ERROR_EN` | Error |
| 1 | `TIMEOUT_EN` | Timeout |
| 2 | `COMPL_EN` | Completion |
| 3 | `THRESHOLD_EN` | Credit |
| 4 | `PERF_EN` | Stream |
| 5 | `DEBUG_EN` | Channel |
| 6 | `ADDR_CHECK_EN` | inert (a stream has no address) |
| 7 | `MONITOR_EN` | all of the above, ANDed with `ENABLE_MON_TAPS` |

**`MON_TIMEOUT`** is in microseconds (0 means 0xFFFF). **`MON_LATENCY`** is
the stall length in cycles above which Credit/BACKPRESSURE fires. The
`ADDR_RANGE*` registers exist and do nothing.

**`OBS_CAPS0`** bits [5:0] pair with `MON_CTRL` [5:0] and report the cones
that were built: `[5] CHANNEL [4] STREAM [3] CREDIT [2] COMPL [1] TIMEOUT
[0] ERROR`, then `[6] MON_TAPS_ARMED [7] BUS_METER [8] COMPRESSION
[9] EGRESS_AXIL`. `[10] ID_SLICE` and `[15:12] N_ADDR_RANGES` read 0.
**`OBS_CAPS1`** = `{8'h00, NUM_CHANNELS, 8'h00, NUM_PORTS}` -- the port count
sits in the `NUM_RD_PORTS` byte and the write byte is 0. **`OBS_CAPS2`** =
`{ADDR_WIDTH, AXIS_ID_WIDTH, DATA_WIDTH[15:0]}`.

**`OBS_STAT_SEL` / `OBS_STAT_DATA`**: `TAP` selects the port, `IS_WRITE` must
be 0 (a stream has one direction; 1 reads 0), and `METRIC` is:

| METRIC | Reads | Source |
|---|---|---|
| 0 / 1 / 2 / 3 | productive / backpressure / starvation / idle cycles, aggregate | `axis_bus_meter` |
| 4 / 5 / 6 / 7 | the same for channel `CHANNEL` (by `tid`) | `axis_bus_meter` |
| 8 | channel `CHANNEL` overflow stickies `{prod, bp, starv, idle}` | `axis_bus_meter` |
| 9 / 10 | 0 -- no latency histogram on a stream | -- |
| 11 / 12 | bytes low / high word (productive beats, `tstrb` popcount) | `axis_bus_meter` |
| 13 | beats | `axis_bus_meter` |
| 14 | packets (`tlast` beats) | `axis_bus_meter` |
| 15 | events the monbus did not take | tap |
| 16 | packets the tap closed (compare with 14) | tap |

The group filter for this block's packets is `AXIS_PKT_MASK` (drop by class,
route to the err FIFO by `ERR_SELECT`) and `AXIS_MASK1..3` (drop by event code
within Error/Timeout, Completion/Channel, Credit/Stream).

---

## Instantiation

Wrapping a DMA's two stream ports -- sink ingress on port 0, source egress on
port 1 -- with the AXIL egress a harness tally consumes:

```systemverilog
axis4_intf_observer #(
    .NUM_PORTS               (2),
    .DATA_WIDTH              (512),
    .AXIS_ID_WIDTH           (8),
    .AXIS_DEST_WIDTH         (4),
    .NUM_CHANNELS            (8),
    .EGRESS_AXIL             (1'b1),
    .ACLK_MHZ                (100),
    .TAP_ENABLE_ERROR_LOGIC  (1'b1),
    .TAP_ENABLE_TIMEOUT_LOGIC(1'b1),
    .TAP_ENABLE_COMPL_LOGIC  (1'b1)
) u_axis_obs (
    .aclk            (aclk),
    .aresetn         (aresetn),
    .s_apb_psel      (obs_psel),
    .s_apb_penable   (obs_penable),
    .s_apb_pready    (obs_pready),
    .s_apb_paddr     (obs_paddr),
    .s_apb_pwrite    (obs_pwrite),
    .s_apb_pwdata    (obs_pwdata),
    .s_apb_pstrb     (obs_pstrb),
    .s_apb_prdata    (obs_prdata),
    .s_apb_pslverr   (obs_pslverr),
    .cam_clear       (1'b0),
    .obs_axis_tdata  ({m_axis_tdata,  s_axis_tdata}),
    .obs_axis_tstrb  ({m_axis_tstrb,  s_axis_tstrb}),
    .obs_axis_tlast  ({m_axis_tlast,  s_axis_tlast}),
    .obs_axis_tid    ({m_axis_tid,    s_axis_tid}),
    .obs_axis_tdest  ({m_axis_tdest,  s_axis_tdest}),
    .obs_axis_tuser  ({m_axis_tuser,  s_axis_tuser}),
    .obs_axis_tvalid ({m_axis_tvalid, s_axis_tvalid}),
    .obs_axis_tready ({m_axis_tready, s_axis_tready}),
    .s_axil_arvalid  (1'b0),
    .s_axil_arready  (),
    .s_axil_araddr   ('0),
    .s_axil_arprot   ('0),
    .s_axil_rvalid   (),
    .s_axil_rready   (1'b0),
    .s_axil_rdata    (),
    .s_axil_rresp    (),
    .m_axi_awid      (), .m_axi_awaddr (), .m_axi_awlen  (), .m_axi_awsize  (),
    .m_axi_awburst   (), .m_axi_awlock (), .m_axi_awcache(), .m_axi_awprot  (),
    .m_axi_awqos     (), .m_axi_awregion(), .m_axi_awuser(), .m_axi_awvalid (),
    .m_axi_awready   (1'b0),
    .m_axi_wdata     (), .m_axi_wstrb  (), .m_axi_wlast  (), .m_axi_wuser   (),
    .m_axi_wvalid    (), .m_axi_wready (1'b0),
    .m_axi_bid       ('0), .m_axi_bresp ('0), .m_axi_buser (1'b0),
    .m_axi_bvalid    (1'b0), .m_axi_bready (),
    .m_axil_awvalid  (tally_awvalid),
    .m_axil_awready  (tally_awready),
    .m_axil_awaddr   (tally_awaddr),
    .m_axil_awprot   (),
    .m_axil_wvalid   (tally_wvalid),
    .m_axil_wready   (tally_wready),
    .m_axil_wdata    (tally_wdata),
    .m_axil_wstrb    (),
    .m_axil_bvalid   (tally_bvalid),
    .m_axil_bready   (tally_bready),
    .m_axil_bresp    (tally_bresp),
    .irq_out         (obs_irq),
    .i_meter_clear   ({perf_clear,  sin_clear}),    // port 1 = m_axis, port 0 = s_axis
    .i_meter_freeze  ({perf_freeze, sin_freeze})
);
```

Filelist: `projects/components/utility-ip/misc/rtl/filelists/axis4_intf_observer.f`.

---

## Verification

`projects/components/utility-ip/misc/dv/tests/fub/test_axis4_intf_observer.py` over
`dv/tbclasses/axis4_intf_observer_tb.py`, which extends the AXI observer TB
(same APB, same egress sink, same shared monbus decoder) and drives the stream
through the AXIS master BFM against a TB-owned `tready`.

| Test | Proves |
|---|---|
| `test_axis4_intf_observer` | `OBS_CAPS0/1/2` report the build, `MON_CTRL` resets match the shared map, config round-trips, caps are read-only. |
| `..._traffic` | Beats, packets, bytes and productive cycles equal the stimulus exactly; per-`tid` buckets split it; the tap's packet count equals the meter's; `IS_WRITE=1` reads 0. |
| `..._packets` | One Completion/STREAM_END per packet; a zero-strobe beat and a withdrawn `tvalid` produce their two Error codes; record framing holds. |
| `..._all_classes` | All six classes and all eleven event codes on an every-cone build, every packet `PROTOCOL_AXIS`. |

The withdrawn-`tvalid` error is the one stimulus driven on the pins rather
than through the BFM: a compliant master cannot produce it.

---

## Related

- `axi4_intf_master_observer.sv`, `axi4_intf_slave_observer.sv` -- the AXI
  siblings, same map and egress.
- `rtl/amba/shared/axis_bus_meter.sv` -- the meter this wraps.
- `rtl/amba/includes/monitor_amba4_pkg.sv` -- the AXIS event vocabulary.
- `docs/markdown/rtl-amba/monitor/axi_monitor_lite.md` -- the discipline the
  tap follows.
- `vault/handbook/design/observers-do-not-drive.md`.
