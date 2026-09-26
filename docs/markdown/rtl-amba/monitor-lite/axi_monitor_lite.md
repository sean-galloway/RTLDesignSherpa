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
# AXI Monitor Lite

**Module:** `axi_monitor_lite.sv`
**Location:** `rtl/amba/monitor-lite/`
**Category:** Monitor Infrastructure
**Status:** Production Ready (TASK-098, 2026-09-25)

---

## Overview

`axi_monitor_lite` is the AXI transaction monitor rebuilt for gate count and
timing: three quarters of what `axi_monitor_base` reports, for about a fifth
of its LUTs. It sits behind the same `axi4/axi5/axil4/axil5_{master,slave}_{rd,wr}_mon`
wrappers, selected by the wrapper parameter `MONITOR_LITE = 1`, and emits
the same 128-bit `monitor_packet_t` with the same `UNIT_ID`/`AGENT_ID` on
the same monbus handshake -- the arbiter, the group, the tally and the host
tooling cannot tell which monitor produced a packet.

What it reports:

- **Error** packets: a SLVERR/DECERR response, a data or response beat with no
  owning transaction (orphan), a burst whose LAST came early or never came,
  a write burst arriving ahead of a second address, and `EVENT_DROPPED` (see
  below) -- each with the transaction's ID in `channel_id` and its address in
  `event_data`, exactly as the full monitor packs them.
- **Completion** packets on a read's last beat or a write's B, with the
  address and, in `event_data[63:48]`, the latency in cycles from the
  command handshake.
- **Timeout** packets when a transaction makes no progress for
  `cfg_timeout_cnt` microseconds, naming the phase (`CMD` for a stalled
  command channel, `DATA`, `RESP`).
- **Threshold** packets when the number of outstanding transactions crosses
  `cfg_active_trans_threshold` upward.

What it does not do, by design: performance packets and windows
(`axi_bus_meter` is the perf path), debug state-change packets, the
address-range checker and report-time address filter, the ID-range filter,
the latency threshold, three independent per-phase timers, and the
`block_ready` admission stall. The lite never touches the traffic it
watches.

---

## Why it is small

The full monitor tracks every transaction as a ~285-bit record and
re-derives everything about it every cycle: three CAM lookup ports, an
oldest-first attribution done with age ranks that every entry recomputes on
any free, a per-entry state machine that a reporter then scans, a second
copy of the table in the reporter, three 16-bit timers per entry and an
8-deep packet FIFO. Measured on `bridge_1x2_rd_mon` (Artix-7 100T -1,
default preset, 16 slots) that is 3,249 LUTs and 1,628 FFs per read
monitor, 2,370 of the LUTs in the per-slot cones.

The lite keeps one 90-bit entry per transaction and computes each event at
the handshake that causes it:

| Mechanism | Full monitor | Lite |
|---|---|---|
| Allocation | three-port CAM with free-slot encode and hit suppression | free-slot priority encode on the command handshake |
| R/B attribution to an entry | ID match, oldest-first by dense age ranks (O(N^2) age matrix) | the head of that ID's linked list (head, tail and a 3-bit next pointer per slot); a one-hot match, no age compare |
| W attribution (AXI4 W beats carry no ID) | age ranks over all live entries | an AW-order FIFO of slot indices: the head owns the beat |
| Timeout | three 16-bit timers per entry, all counting | one microsecond stamp per entry (a copy of a shared tick counter), one rotating subtract-and-compare |
| Latency | three 32-bit timestamps per entry | one 16-bit cycle stamp per entry, one shared subtractor at completion |
| Event detection | reporter scans the table with priority encoders | computed on the handshake, no scan; the cycle's events are registered, and the packet is picked and formatted from flops the next cycle |
| Output | 8-deep FIFO of 85-bit entries plus a table copy | `OUT_DEPTH`-deep queue (default 4) of 66-bit entries (type, code, id, latency, address) in an unreset array; the constant fields are added at the output |
| Backpressure | admission stall (`block_ready`) | drop and count, reported as `Error/EVENT_DROPPED` |

An entry holds stamps, not counters: the only per-slot arithmetic is an
8-bit beat decrement, kept local so the beat that lands reads one flag
("was that the last expected") instead of an 8-bit value through a mux. The
two 16-bit subtractors (latency, timeout age) sit after the read mux and are
shared by every slot, and one id/address mux serves every packet class.

Five builds got here, each measured in the same fixture. The first had a
serial running-max loop for "oldest matching entry" (89 LUT levels). The
second had a 16-bit incrementer, a 16-bit subtractor and an 8-bit decrementer
in every slot (10,120 LUTs, 38 levels at sixteen slots). The third moved the
arithmetic behind the read mux but ordered by an allocation sequence stamp,
which both wraps for a long-lived entry and puts a subtract in front of every
tournament compare, and it still formatted and queued the packet in the same
cycle as the attribution (6,339 LUTs for the bridge, 23 levels). The fourth
ordered by dense rank and registered the events before the pick (5,575 LUTs,
12 levels, 0.6 ns short); its hierarchy report put 346 of the lite's 838 LUTs
in a generic skid buffer, and its critical path through the rank tournament.
The fifth, described here, replaced the tournament with per-ID linked lists
and the skid with a four-entry unreset queue.

## Measured

Same fixture, same flow: `bridge_1x2_rd` regenerated with `mon_preset =
"error_only"` (the full monitor, 16 slots, error+timeout+compl+threshold
cones) and with `mon_preset = "lite"` (this block, 8 slots), synthesized and
routed out of context through `projects/components/bridge/fpga/` on
2026-09-25, Vivado 2025.1. Per-instance numbers are the hierarchical
utilization of one read monitor inside `cpu_rd_adapter`.

| | Full monitor | Lite | Lite / full |
|---|---:|---:|---:|
| One read monitor, LUTs | 3,249 | 677 | 21% |
| One read monitor, FFs | 1,628 | 831 | 51% |
| Whole bridge (3 monitors + arbiter + group), LUTs, Artix-7 100T -1 | 12,625 | 5,339 | 42% |
| Whole bridge, FFs | 7,433 | 5,270 | 71% |
| Bridge WNS at 10 ns, Artix-7 100T -1 | -0.303 ns | -0.160 ns | |
| Bridge WNS at 6.667 ns, Kintex-7 325T -2 | +0.212 ns | +1.092 ns | |
| Bridge without monitors, LUTs / FFs | 826 / 767 | | |

The flops are the table: eight 90-bit entries, the event register and the
four-entry queue. The full monitor's 16-slot CAM is 800 FFs on its own, so
halving the slots does most of the flop saving; the LUT saving is the
design.

Neither bridge meets 10 ns on the Artix-7, and in neither case is the path
in a monitor: the full bridge's worst path is inside `monitor_trans_cam`,
the lite bridge's inside `monbus_axil4_axil4_group` (the address-window
compare chain `s1_beats_to_limit`, 11 CARRY4 in a row), a block both
bridges share. No path through `axi_monitor_lite` is among the twenty
worst; all of them have at least 0.85 ns of slack at 10 ns. The group's
chain is filed as its own item.

<!-- MEASURED -->

---

## Parameters

| Parameter | Type | Default | Description |
|---|---|---|---|
| `UNIT_ID` | logic [7:0] | 8'h09 | Unit id in every packet |
| `AGENT_ID` | logic [15:0] | 16'h0063 | Agent id in every packet |
| `MAX_TRANSACTIONS` | int | 8 | Table slots. A command that finds none free is counted (`refused_count`), not tracked; its beats then report as orphans |
| `ADDR_WIDTH` | int | 32 | Address width stored per entry and reported |
| `ID_WIDTH` | int | 8 | Transaction ID width; 0 for AXI-Lite (one bit is kept) |
| `IS_READ` | bit | 1 | 1 = AR/R monitor, 0 = AW/W/B monitor |
| `IS_AXI` | bit | 1 | 0 = AXI-Lite: no ID compare |
| `TS_WIDTH` | int | 16 | Cycle stamp width: ordering and latency (latency saturates at 2^16 cycles) |
| `AGE_WIDTH` | int | 16 | Microsecond age width for the timeout (`cfg_timeout_cnt` is 16 bits) |
| `OUT_DEPTH` | int | 4 | Output queue depth in 66-bit entries; a power of two |
| `CFI_*` | | as `axi_monitor_timer` | Frequency-invariant microsecond tick (`counter_freq_invariant`) |

## Ports

The command/data/response taps and the `cfg_*` names are the subset of
`axi_monitor_base`'s that the lite implements; the wrappers connect the same
signals to both. `cfg_timeout_cnt` is one threshold for every phase (the
wrappers feed it their `cfg_timeout_cycles`, microseconds, `0` = never).
`cfg_axi_pkt_mask[type]` drops a packet type at the source.

Outputs beyond the monbus: `active_count` (live entries), `busy`,
`perf_completed_count` / `perf_error_count` (16-bit saturating, the wrapper's
`transaction_count` / `error_count`), `dropped_count` (events lost to
backpressure since reset or `clear`) and `refused_count` (commands that found
no slot).

## Functional Description

### Attribution

A read beat belongs to the oldest live entry whose ID matches `RID`; AXI
returns same-ID responses in issue order, so oldest-matching is exact and the
16-bit allocation stamp orders it. A write beat belongs to the entry at the
head of the AW-order FIFO, because AXI4 W beats carry no ID and follow AW
issue order; the FIFO pops on `WLAST`. A B belongs to the oldest matching
entry that has finished its data phase.

A write burst that arrives before its AW (legal on a slave-side monitor) is
buffered as a beat count and applied when the AW allocates; a second early
burst before that AW is an `Error/WRITE_BEFORE_ADDR` and is dropped.

### Errors, once per transaction

A response error, an early or missing LAST, an orphan beat: each is reported
the cycle it happens. An entry that has reported an error reports no more for
that transaction and yields no completion; it still frees on its last beat or
B, so the table never leaks on error.

### Timeout

Each entry carries a microsecond age cleared on every beat. One rotating
pointer compares one entry per cycle against `cfg_timeout_cnt`, so a stuck
transaction is reported within `MAX_TRANSACTIONS` cycles of crossing -- a
rounding error against a microsecond tick -- and reported once. A command
channel that holds VALID without READY for the same threshold reports
`Timeout/CMD`.

### Drop and count

Events go into the output queue. If the queue is full when an event fires, or
two events fire in one cycle (error > timeout > completion > threshold picks
the one that goes), the rest are dropped and counted. The next time the queue
has room and nothing else wants it, one `Error/EVENT_DROPPED` packet carries
the count and the counter restarts. The consumer therefore always knows how
many events it did not see.

## Verification

- `val/amba/test_axi_monitor_lite.py` through `axi4_slave_{rd,wr}_mon` with
  `MONITOR_LITE=1`: exact packets for singles and bursts (address, id, non-zero
  latency), one `RESP_SLVERR` and no completion for an out-of-range access,
  one `Timeout/DATA` (read) or `Timeout/RESP` (write) for a stalled slave
  followed by the completion, one threshold packet for a pile of outstanding
  transactions, and a held monbus whose dropped events sum with the delivered
  ones to the number issued. Three levels, ID widths 4 and 8, 8 and 16 slots.
- `formal/amba/axi_monitor_lite`: under unconstrained taps, `active_count`
  never exceeds the table, `clear` empties it, and an offered packet is held
  unchanged until taken; covers reach a completion, an error, a timeout, a
  threshold and a full table (the proof is not vacuous).
- The bridge's generated monitor stress tests run unchanged on
  `bridge_1x2_rd_lite_mon` (`mon_preset = "lite"`).

## Related

`axi_monitor_base` (the full monitor), the `*_mon` wrappers'
`MONITOR_LITE` parameter, `monbus_arbiter` and `monbus_group` (unchanged
consumers), `vault/Tasks/amba` TASK-098 (the review that sized this).
