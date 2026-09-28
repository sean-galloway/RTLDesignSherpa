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
# AXIS Monitor Lite

**Module:** `axis_monitor_lite.sv`
**Location:** `rtl/amba/monitor/axis_monitor_lite.sv`
**Category:** Monitor Infrastructure
**Status:** Built, formally checked and verified in simulation, with the eight `axis{4,5}_{master,slave}_monlite[_cg]` wrappers (amba/monitor-lite TASK-003, closed 2026-09-27). Standalone area from yosys only; no Vivado fixture build yet.

---

## Overview

The first AXI4-Stream monitor in `rtl/amba/monitor`. The `_mon` family and
its `_monlite` twin cover AXI4, AXI5 and both AXI-Lite generations because
`axi_monitor_base` and `axi_monitor_lite` are transaction trackers: a command
handshake opens a table entry, data beats and a response close it. A stream
has no command, no response and no outstanding-transaction notion, so there was
nothing for those cores to track and nothing for a wrapper to wrap. Until this
block the only stream-side measurement was `axis_bus_meter` (counters, no
packets), and the only AXIS monbus emitter anywhere was the per-port tap inside
`axis4_intf_observer`, written for that block and not reusable.

What a stream does have is packets (TLAST-delimited runs of beats), stalls
(TVALID held without TREADY), bubbles (TVALID withdrawn inside a packet), and a
per-beat TID and TDEST that may change under a packet. This block watches
those and emits them as the AXIS packet classes the monbus package has always
defined -- Credit, Channel and Stream -- plus the shared Error, Timeout and
Completion classes. Same 128-bit `monitor_packet_t`, same side-band
timestamp, same monbus handshake, same UNIT/AGENT ids: the arbiter, group,
tally and host tooling see one more producer and nothing new.

The event set and payload layouts are the observer's tap, lifted unchanged so
that the observer can later instantiate this core instead of carrying its own
copy. What the block adds over the tap is the lite's delivery contract: a
4-deep output queue that takes two events a cycle instead of a one-packet hold
register, drop-and-count with the count reported as `Error/EVENT_DROPPED`, the
frequency-invariant microsecond tick for the timeouts, the lite's cfg pin set,
and `clear`.

This is a tap. Nothing here drives or gates the stream; `axis_tready` is an
input like `axis_tvalid`, and a packet the monbus will not take is dropped and
counted.

## Parameters

| Parameter | Default | Meaning |
|---|---|---|
| `UNIT_ID` | `8'h09` | unit field of every packet |
| `AGENT_ID` | `16'h0064` | agent field of every packet |
| `DATA_WIDTH` | 32 | sizes `axis_tstrb` only; the monitor never sees TDATA |
| `ID_WIDTH` | 8 | TID width; 0 is legal (a 1-bit tie-off) |
| `DEST_WIDTH` | 4 | TDEST width; 0 is legal |
| `AGE_WIDTH` | 16 | microsecond age counter (cfg_timeout_cnt is 16 bits) |
| `OUT_DEPTH` | 4 | output queue depth, a power of two |
| `CFI_MIN_FREQ_MHZ`, `CFI_MAX_FREQ_MHZ`, `CFI_NUM_FREQ_ENTRIES`, `CFI_FREQ_STRATEGY` | 5, 220, 16, 0 | the `counter_freq_invariant` table behind the microsecond tick, as on `axi_monitor_lite` |

## Ports

| Group | Ports | Notes |
|---|---|---|
| Clock, reset, clear | `aclk`, `aresetn`, `clear` | `clear` is synchronous and legal only while idle: no packet open, no stall running, nothing queued (the same rule as `axi_monitor_lite`, amba ISSUE-002) |
| Time | `i_mon_time` | side-band timestamp, presented with every packet |
| Stream tap | `axis_tvalid`, `axis_tready`, `axis_tlast`, `axis_tid`, `axis_tdest`, `axis_tstrb` | all inputs |
| Configuration | `cfg_freq_sel`, `cfg_timeout_cnt`, `cfg_error_enable`, `cfg_timeout_enable`, `cfg_compl_enable`, `cfg_credit_enable`, `cfg_channel_enable`, `cfg_stream_enable`, `cfg_strb_check_enable`, `cfg_stall_threshold`, `cfg_axis_pkt_mask` | `cfg_timeout_cnt` is microseconds, `16'hFFFF` = never; `cfg_stall_threshold` is cycles, 0 = off; the mask drops a packet type at the source |
| Monitor bus | `monbus_valid`, `monbus_ready`, `monbus_packet`, `monbus_timestamp` | standard monbus handshake |
| Status | `busy`, `in_packet`, `packet_count`, `error_count`, `dropped_count` | `error_count` excludes drop reports; `dropped_count` is since the last report |

## Functional Description

### Events

Priority when several fire in one cycle: Error > Timeout > Completion > Credit
> Channel > Stream. The two highest go into the queue; anything beyond that,
and anything offered to a full queue, is counted, never silently discarded.

| Class / code | Fires when | `event_data[63:0]` |
|---|---|---|
| Error / `VALID_TIMING` | TVALID withdrawn before the handshake (the AXIS rule: once asserted, TVALID holds until TREADY) | `{stall_cycles[31:0], packets[31:0]}` |
| Error / `STRB_INVALID` | an accepted beat whose TSTRB is all zero, with `cfg_strb_check_enable` (legal AXIS, a bug on a DMA stream) | `{beats_now[31:0], packets[31:0]}` |
| Timeout / `HANDSHAKE` | TVALID held without TREADY for `cfg_timeout_cnt` microseconds; once per stall | `{stall_cycles[31:0], age_us[15:0], cfg[15:0]}` |
| Timeout / `PACKET` | inside a packet, no beat accepted for `cfg_timeout_cnt` microseconds; once per gap | `{beats[31:0], age_us[15:0], cfg[15:0]}` |
| Completion / `STREAM_END` | the TLAST beat | `{tid[15:0], tdest[15:0], beats[31:0]}` |
| Credit / `BACKPRESSURE` | a stall of `cfg_stall_threshold` cycles; once per stall | `{stall_cycles[31:0], cfg_stall_threshold[31:0]}` |
| Channel / `ID_CHANGE`, `DEST_CHANGE` | TID or TDEST differs from the previous accepted beat inside a packet | `{old[15:0], new[15:0], beats_now[31:0]}` |
| Stream / `START` | the first beat of a packet | `{tid[15:0], tdest[15:0], packets[31:0]}` |
| Stream / `PAUSE`, `RESUME` | TVALID low inside a packet, and back again | `{beats[31:0], packets[31:0]}` |
| Error / `EVENT_DROPPED` | the drop count, when the queue has drained and nothing else wants it | `dropped_count` |

`channel_id` carries the beat's TID on every packet.

Two rules differ from the observer's tap, both learned from the exact-packet
tests:

- **Two events a cycle.** On a stream, events coincide: the beat that ends a
  bubble is a RESUME and, if it carries TLAST, a STREAM_END; the first beat
  after a pause may also change TID; a one-beat packet is a START and an END
  in the same cycle. The observer's one-per-cycle pick dropped and counted the
  loser every time, so its drop count reported ordinary traffic. Here the two
  highest-priority candidates are both queued (a second write port; the queue
  is flops rather than LUTRAM at this depth), and the drop count means what it
  says. Forcing the second push off fails the suite.
- **The drop report goes only into an empty queue.** The AXI lite's rule is
  "when the queue has room". Here a report pushed into a queue that is merely
  not full takes the slot the next live event needs while the bus is
  congested, which is exactly when drops happen, and each idle cycle adds
  another report. So the report waits for the queue to drain; the count keeps
  accumulating, saturating, until then.

### Timing

Age is counted in microsecond tick edges since the stall or gap began, so a
timeout of `cfg_timeout_cnt = N` fires after between `N-1` and `N` full tick
periods. The tick is entry `cfg_freq_sel` of the `counter_freq_invariant`
table; a wrapper that knows its clock sets `CFI_MIN_FREQ_MHZ = CFI_MAX_FREQ_MHZ
= ACLK_MHZ` and entry 0 is then one microsecond of that clock.

### Drop and count

Every candidate the pick cannot queue in a cycle -- the losers of the
priority pick and anything offered to a full queue -- adds to
`dropped_count`. When the queue has drained and no event fires, one
`Error/EVENT_DROPPED` packet carries the count and zeroes it. The count
saturates rather than wrapping.

## Usage Examples

```systemverilog
axis_monitor_lite #(
    .UNIT_ID          (8'h09),
    .AGENT_ID         (16'h0064),
    .DATA_WIDTH       (64),
    .ID_WIDTH         (8),
    .DEST_WIDTH       (4),
    .CFI_MIN_FREQ_MHZ (100),
    .CFI_MAX_FREQ_MHZ (100)
) u_axis_mon (
    .aclk (aclk), .aresetn (aresetn), .clear (1'b0), .i_mon_time (mon_time),
    // tap: both directions are inputs
    .axis_tvalid (m_axis_tvalid), .axis_tready (m_axis_tready),
    .axis_tlast  (m_axis_tlast),  .axis_tid    (m_axis_tid),
    .axis_tdest  (m_axis_tdest),  .axis_tstrb  (m_axis_tstrb),
    .cfg_freq_sel (4'd0), .cfg_timeout_cnt (16'd10),      // 10 us
    .cfg_error_enable (1'b1), .cfg_timeout_enable (1'b1), .cfg_compl_enable (1'b1),
    .cfg_credit_enable (1'b1), .cfg_channel_enable (1'b1), .cfg_stream_enable (1'b0),
    .cfg_strb_check_enable (1'b0), .cfg_stall_threshold (32'd64), .cfg_axis_pkt_mask (16'h0),
    .monbus_valid (mon_valid), .monbus_ready (mon_ready),
    .monbus_packet (mon_packet), .monbus_timestamp (mon_ts),
    .busy (), .in_packet (), .packet_count (), .error_count (), .dropped_count ()
);
```

Stream packets (`START`, `PAUSE`, `RESUME`) fire on every packet and every
bubble; on a busy link leave `cfg_stream_enable` low or mask the type, and read
the counters instead.

## Design Notes

- **One open packet, not a per-TID table.** A stream that interleaves several
  TIDs under one TLAST is reported as `Channel/ID_CHANGE`, not tracked per ID.
  That is the lite's trade and the observer's: the consumers in this repo
  (STREAM, RAPIDS data ports) do not interleave.
- **Everything is a handshake or a level.** No counters per packet beyond the
  32-bit beat count, one shared microsecond counter, two stamps. The pick is
  shallow enough not to need the lite's registered event stage.
- **Unreset queue storage**, as on `axi_monitor_lite`: pointers reset, the
  array does not. With two write ports it is flops, not LUTRAM; `OUT_DEPTH`
  is the knob if that matters somewhere.
- **Standalone area** (yosys generic `synth` on the sv2v-flattened core,
  NAND-2 equivalents from `bin/yosys_to_nand_equiv.py`, default parameters):
  about 45 k NAND2 and 539 flops, against the AXI lite's 91 k and 1,209 in the
  same flow. The second queue push accounts for roughly 13 k of that; the
  one-push version measured 32 k. No Vivado numbers yet.

## Related Modules

- `axi_monitor_lite` -- the AXI transaction monitor whose delivery contract this block shares
- `axis4_intf_observer` (projects/components/misc) -- the tap this block's event set comes from; a candidate to instantiate this core
- `axis{4,5}_{master,slave}_monlite` and `_monlite_cg` -- the eight wrappers that tap this core onto the stream endpoints ([axi_monitor_lite_wrappers](axi_monitor_lite_wrappers.md), Table 2)
- `axis_bus_meter` -- stream throughput and backpressure counters, the perf path (this block emits no perf packets)
- `monitor_common_pkg`, `monitor_amba4_pkg` -- packet format and the AXIS event codes

## Testing

**Formal** (`formal/amba/axis_monitor_lite/`, sv2v-flattened like the AXI
lite, `make prove cover`): BMC to depth 24 over free stream, monbus and cfg
inputs. Asserted: a presented packet holds until taken; every packet carries
the AXIS protocol code and this unit/agent; `packet_count` moves by exactly one
on a TLAST handshake and not otherwise; `in_packet` follows the TLAST run;
`clear` zeroes every counter; `dropped_count` only ever falls to zero (a report
or a clear); `busy` whenever a packet is queued or open. Cover to depth 40
reaches all seven packet classes the block emits, EVENT_DROPPED included.

**Simulation.** `val/amba/monitor-lite/test_axis_monitor_lite.py` drives the
fixture `tb_axis_monitor_lite.sv` (the core tapping a stream between the
framework AXIS master and slave BFMs) through `AxisMonitorLiteTB`. Each phase
asserts the class, code and payload of every packet and that nothing else came
out: packets of 1 to 16 beats (START and STREAM_END on every one), TID/TDEST
change under a packet, source bubbles (PAUSE/RESUME per gap), a 300-cycle held
tready (one BACKPRESSURE at 50 cycles, one HANDSHAKE timeout at 2 us, then the
completion), a 300-cycle gap inside a packet (one PACKET timeout, no
HANDSHAKE), a zero-strobe beat armed and unarmed, TVALID withdrawn (pin-driven,
the one protocol violation a BFM cannot produce), the type mask, a held monbus
(delivered + reported dropped == issued), and `clear`. The same class drives
the eight wrappers end to end (see the wrappers page): through an endpoint a
phase waits for the skid to drain before judging, and on a slave wrapper the
stall phase fills the skid first, since a single beat never stalls an upstream
tap.

Cells: core GATE 1 / FUNC 6 / FULL 12; wrappers 9 each at FULL. 84/84 at FULL
from a clean build, 2026-09-27. Three mutations of the RTL were caught: the
credit firing every stall cycle (stall phase), the change detector comparing
against the packet's first beat (channel phase), and the second queue push
disabled (packets phase, START lost on one-beat packets).

## Navigation

- [rtl-amba index](../index.md)
- [axi_monitor_lite](axi_monitor_lite.md)
- [axi_monitor_lite_wrappers](axi_monitor_lite_wrappers.md)
