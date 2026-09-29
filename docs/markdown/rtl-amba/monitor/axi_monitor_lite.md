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
**Location:** `rtl/amba/monitor/axi_monitor_lite.sv`
**Category:** Monitor Infrastructure
**Status:** Production Ready (amba/monitor-lite TASK-001, 2026-09-25); adopted by every consumer, measured in three board builds and validated on silicon, 2026-09-27

---

## Overview

`axi_monitor_lite` is the AXI transaction monitor rebuilt for gate count and
timing: three quarters of what `axi_monitor_base` reports, for about a fifth
of its LUTs. It sits behind the same `axi4/axi5/axil4/axil5_{master,slave}_{rd,wr}_mon`
wrappers as their `_monlite` siblings (`axi4_slave_rd_monlite` and fifteen more), and emits
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
  `cfg_active_trans_threshold` upward, or a completion's latency exceeds
  `cfg_latency_threshold`.
- **Address-range** packets from the optional checker (`N_ADDR_RANGES > 0`):
  `Error/ADDR_RANGE` for a miss against an error-flavoured range, `AddrMatch`
  for a hit on a match-flavoured one, gated by `cfg_addr_match_enable`.

What it does not do, by design: performance packets and windows
(`axi_bus_meter` is the perf path), debug state-change packets, the
report-time address filter, the ID-range filter, three independent per-phase
timers, and the `block_ready` admission stall. The lite never touches the
traffic it watches. Two features first listed here as dropped came back on
2026-09-26, each because a consumer bound it: the address-range checker and
the latency threshold (TASK-001 sections 11 and 13).

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
| Address-range checker | `axi_monitor_addr_check`, N ranges, muxed onto the monbus | the same module, optional (`N_ADDR_RANGES`), its packets muxed onto the monbus with a presented-packet hold (Sean, 2026-09-26: STREAM's data ports use it) |

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
routed out of context through `projects/components/fabric-gen-ip/bridge/fpga/` on
2026-09-25, Vivado 2025.1. (Since 2026-09-26 the bridge generator builds the
lite on every monitored port, so `bridge_1x2_rd_mon` regenerated today is a
lite bridge too; the full-monitor column is the 2026-09-25 baseline.) Per-instance numbers are the hierarchical
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

### In systems, on silicon (2026-09-26 and 27)

The fixture number above is one monitor. What a design saves depends on how
much of it is monitored, so the lite was measured where it is used: the three
Genesys 2 STREAM builds (Kintex-7 325T-2, 203,800 LUTs), each rebuilt from
HEAD after `make clean-all`, post-route, Vivado 2025.1; and two synth-only
matrices that hold everything but the monitor constant.

| Build | Full monitor | Lite | Saved |
|---|---:|---:|---:|
| STREAM build-obs, 4ch, both observers on (same-day A/B, 2026-09-26) | 184,047 LUTs, WNS +1.334 ns | 71,671 LUTs, WNS +4.154 ns | 112,376 LUTs, 61% |
| STREAM build-mon, 8ch, in-core monitors on (`stable/` 2026-09-09 vs 2026-09-26) | 139,293 LUTs, WNS +1.513 ns | 87,443 LUTs, WNS +3.764 ns | 51,850 LUTs, 37% |
| STREAM build-perf, 8ch, monitors compiled out | 67,956 LUTs | 68,139 LUTs | nothing to save |
| STREAM perf with in-core monitors on, synth matrix, 100 MHz | 143,914 LUTs, WNS -6.061 ns | 91,063 LUTs, WNS +1.312 ns | 52,851 LUTs, 37% |
| RAPIDS beats, 8ch, in-core monitors on, synth matrix | 71,721 LUTs | 65,974 LUTs | 5,747 LUTs, 8% |

Two rows carry the argument. On STREAM's perf clocking the full monitor does
not close (-6.061 ns at 100 MHz) and the lite does (+1.312 ns): on that design
the lite is what makes an instrumented perf build buildable at all, not merely
a smaller one. RAPIDS shows the other end: it monitors only its descriptor
read path, so the saving is 8%. The lite's advantage scales with the monitored
surface, and the build-obs row -- four monitors at 64 slots, 112,376 LUTs
back -- is what that looks like when the surface is large.

On the board the numbers held. STREAM build-obs with both observers on the
lite (`host_obs_matrix` at tool defaults, per iteration): completion 4491 to
4412, address-match 4410 to 4402, error 4402 to 4402, threshold 4402 to 4419;
the DUT's own bus meters bit-identical (R/W utilization 99.8%, 914.2 MB/s);
the six-endpoint register walk identical. Perf and Debug packet classes read
0, by design -- the perf data is in the meters and histograms, which never
lived in the monitor. Timeout went from 7 to 55 per iteration: the full
monitor parked a timed-out slot in `TRANS_ERROR` and leaked it, saturating at
about 7 per reset; the lite frees the slot and keeps reporting. STREAM
build-mon on the in-core lite walks 283 registers clean and provokes 7 of 7
monitor scenarios with nothing in the UNEXPECTED bin; RAPIDS beats on the
in-core lite passes its golden-CRC smoke and an 8-channel characterization at
2.88 GB/s.

<!-- MEASURED -->

---

## Adopted

Every consumer is on the lite, each switch measured and tested where it lives:

| Consumer | What switched | Since |
|---|---|---|
| Generated bridges | every monitored port; the `mon_preset` cone presets became aliases of the lite | `e92a5ae2d`, 2026-09-26 |
| STREAM in-core (`stream_core`, `scheduler_group_array`) | rd/wr data ports and the descriptor port | `8cce2ecce`, 2026-09-26 |
| RAPIDS beats in-core (`scheduler_group_array_beats`) | the descriptor port | `8cce2ecce`, 2026-09-26 |
| Genesys 2 STREAM bridges (`bridge_stream_mon_axil`, `bridge_stream_char_axil`) | regenerated onto the `_monlite` wrappers | `0b65960d4`, 2026-09-26 |
| Observers (`axi4_intf_master_observer`, `axi4_intf_slave_observer`) | the rd and wr taps | `78cddb5e2`, 2026-09-27 |

No design under `projects/` instantiates a full `_mon` wrapper any more (178
`_monlite` instantiations tree-wide); the full monitor remains available behind
its own sixteen `_mon_cg` wrappers for a build that wants the Perf and Debug
packet classes on the monbus.

What a consumer gives up, stated once: those two packet classes. Anything that
derives its expected classes from the hardware is correct without change --
the observers' `OBS_CAPS0` reports both cones as not built. Anything with a
hardcoded class list (STREAM's `host_obs_matrix`) reads those two rows as LOW
until it learns to ask; that is the tool, not the monitor.

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
| `N_ADDR_RANGES` | int | 0 | Address-range checker windows (`axi_monitor_addr_check`, the full monitor's); 0 = not built, zero area |
| `ADDR_RANGE_IS_ERROR` | logic [N-1:0] | '0 | Per range: 1 = a MISS is an `Error/ADDR_RANGE` packet, 0 = a HIT is an `AddrMatch` packet |
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
buffered as a beat count and applied when the AW allocates: with `e` beats
already seen, the entry expects `len + 1 - e` more. A second early burst
before that AW is an `Error/WRITE_BEFORE_ADDR` and is dropped -- unless the
AW absorbing the first burst arrives in that same cycle, in which case the
new beat simply starts the next early burst.

A W beat in the same cycle as an AW, with no AW already awaiting data,
belongs to the AW being allocated (AXI4 write data is in AW order) and is
absorbed at allocation: a single-beat write goes straight to its response
phase; a longer burst expects `len` more beats; a LAST on that first beat of
a longer burst is an `Error/BURST_LENGTH` on the new entry. While an earlier
early burst is still pending the same-cycle beat is a later transaction's and
is counted as early instead. Until 2026-09-28 the same-cycle beat was counted
as early while its own AW queued for beats that had already passed, and the B
then reported `RESP_ORPHAN`; the inherited same-cycle suite found it
(amba/monitor-lite TASK-002), along with an off-by-one in the absorbed count
that made a legal two-beat write with one early beat report `BURST_LENGTH`.

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

A timeout is a one-cycle event and an Error fired in the same cycle outranks
it. Since 2026-09-28 one fired timeout the pick could not take is held with
its own payload (code, id, address) and offered on the following cycles,
oldest first, so a sustained error stream delays a timeout rather than losing
it (the inherited starvation suite had measured the loss at one error per
cycle; monitor-lite TASK-004). A second timeout arriving while the hold is
full is still lost and counted.

### Latency threshold

A clean completion whose latency (cycle stamp at completion minus the cycle
stamp at allocation) exceeds `cfg_latency_threshold` raises a
`Threshold/LATENCY` packet. The compare is taken one stage after the
completion, from the registered latency, and the event is then held with its
own payload (id, address, latency) until the pick can take it -- so the
completed slot may be reallocated meanwhile without the packet naming the
wrong transaction. Until 2026-09-28 the compare and the hold were decided in
the completion cycle itself, which chained the RRESP decode, the slot pick,
the subtract, the compare and the drop-count adder into 21 logic levels
(amba/monitor-lite ISSUE-002).

### Drop and count

Events go into the output queue. If the queue is full when an event fires, or
two events fire in one cycle (error > timeout > completion > threshold picks
the one that goes), the rest are dropped and counted -- except the one
timeout and the one latency event the holds above can keep. The next time the queue
has room and nothing else wants it, one `Error/EVENT_DROPPED` packet carries
the count and the counter restarts. The consumer therefore always knows how
many events it did not see.

## Verification

- `val/amba/monitor-lite/test_axi_monitor_lite.py` through `axi4_slave_{rd,wr}_monlite`:
  exact packets for singles and bursts (address, id, non-zero latency), one
  `RESP_SLVERR` and no completion for an out-of-range access, one timeout naming
  the stuck phase, one active-count threshold, and a held monbus that drops
  events and then reports the count. 8 cells at full.
- `val/amba/monitor-lite/test_<wrapper>_monlite.py`, sixteen tests derived from
  the `_mon` wrapper tests on the existing monitor TB classes: the same
  scenarios with the `_monlite` DUT. 105 cells at full with the above.
- `formal/amba/axi_monitor_lite`: under unconstrained taps, `active_count`
  never exceeds the table, `clear` empties it, and an offered packet is held
  unchanged until taken; covers reach a completion, an error, a timeout, a
  threshold and a full table (the proof is not vacuous).
- The bridge's generated monitor stress tests run unchanged on
  `bridge_1x2_rd_lite_mon` (`mon_preset = "lite"`).
- The full monitor's own suites in `val/amba`, each with lite cells in its
  grid (amba/monitor-lite TASK-002, 2026-09-28). Nothing is skipped by file;
  where the lite has no equivalent of a full-monitor signal the check is the
  lite's own contract instead:

  | Suite | Lite cells | What the lite is held to |
  |---|---|---|
  | `test_axi4_monitor` | 6 (`axi_monitor_lite` core: AXI4/AXI-Lite x rd/wr, small table, 256 IDs) | all six phases: basic, bursts, response errors, orphans, sustained, zero-delay |
  | `test_axi_monitor_wr_same_cycle` | 2 | same-cycle AW+W single and first-of-burst, control, AW during an open burst, a partial early burst (phase 5, new for both cores) |
  | `test_axi_monitor_runtime_disable` | 1 | table drains with a class runtime-disabled and under backpressure; `refused_count` stays 0 (no `block_ready` to wedge) |
  | `test_axi_mon_block_ready` | 16 cells on 11 wrappers (`LiteRefuseCheck`) | the table filled and refused, `admitted == transaction_count + refused_count + live` exactly, occupancy never above the depth. Depth follows the TB's bus-measured concurrency (the AXI-Lite and AXI5 read BFMs hold at most 4 in flight, the AXI-Lite write BFM 2), and `axil4_master_wr_monlite` is not claimed: its core taps behind the write skid and never sees two outstanding |
  | `test_axi_monitor_soak` | 1 (`monitor_soak_monlite`) | 60k-200k cycles of random reads with errors, stalls and 15 % consumer backpressure: generated completions + errors + timeouts == delivered + drops reported + drops pending, exactly (60k cycles: 10,655 = 7,648 + 1,909 + 965 + 133) |
  | `test_axi_monitor_pktgen` | 2 (timeout starvation) | one stalled read against an SLVERR flood: accounting exact; the victim's timeout is delivered at a 1-in-2 error duty and LOST (counted) at 1-per-cycle -- see amba/monitor-lite TASK-004 |

  Every check reports its count, not a bare verdict.

## Related

`axi_monitor_base` (the full monitor), the sixteen `*_monlite` wrappers
(one per `*_mon`, e.g. `axi4_slave_rd_monlite`), `monbus_arbiter` and `monbus_group` (unchanged
consumers), `vault/Tasks/amba` amba/monitor-lite TASK-001 (the review that sized this).
