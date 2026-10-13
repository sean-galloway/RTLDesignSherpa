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

# serv_monitor (Block 2)

One per Delta tile; sixteen instances. The SERV core runs the trigger logic
in firmware; the surrounding glue provides the counters, taps, and injection
path the core alone cannot. Clock domain: `serv_clk` (all instances share
the domain, never communicate directly).

```
serv_monitor
├── serv_wrapper.sv        # SERV core instantiation + bus glue
├── local_mem.sv           # 2 KB I-mem + 2 KB D-mem
├── traffic_counter.sv     # Packet/cycle counters from the router tap
├── trigger_logic.sv       # Threshold compare + event detect (independent of core)
├── axis_injector.sv       # AXIS TX (PKT_CONFIG / PKT_STATUS) into CDC FIFO
└── ctrl_net_slave.sv      # Control-network slave + mailbox to core
```

: SERV monitor module tree

## Submodules

**`serv_wrapper`.** Instantiates the SERV core. Exposes a read-only tile-ID
register at core address `0xF000_0000` (firmware reads its own identity)
and routes the data bus to local memory, the injection FIFO aperture, the
counter bank, and the control mailbox.

**`traffic_counter`.** The counter bank behind the router tap:
`pkt_rx_count[4]`, `pkt_tx_count[4]`, `pkt_local_inject`,
`pkt_local_consume`, `buffer_overflow_count`, `stall_cycles` — 32-bit
wrapping, saturating-clear on read when `Reset Statistics Counters` is
issued. `buffer_occupancy[4]`, `congestion_flag`, and `error_flags` are
wired combinationally from the tap for low-latency trigger evaluation.

**`trigger_logic`.** Hardware threshold comparator running in parallel with
the core: flags `occupancy > cfg_threshold` (default 75% of buffer depth)
and error conditions immediately, so congestion detection meets the < 10
cycle target even when the bit-serial core is mid-instruction. The core
consumes trigger flags as interrupts/polled events and decides the packet
response; `trigger_logic` never injects packets by itself (firmware owns
all packet content — this split keeps policy in software, detection in
hardware).

**`axis_injector`.** TX FIFO aperture (128-bit × 4 entries) plus the AXIS
master into the per-SERV `serv_clk → delta_clk` CDC FIFO. Firmware writes
words, then commits with `TVALID`; the injector appends `tid`, `tuser`,
`tdest`, `tlast` per the commit record.

**`ctrl_net_slave`.** Receives 32-bit control frames addressed to this
monitor (HAS Chapter 4 command set), updates threshold/config registers,
raises core interrupts, and queues uplink status frames for the control
network's round-robin arbiter.

## Interfaces

Router tap in (from the tile router, `delta_clk` — synchronized at the
tap boundary inside `traffic_counter`; the tap is observation-only),
control-network slave port, AXIS TX into CDC, observation port out.

## Open Items

- Tap synchronization (decided 2026-10-13): **dual-flop synchronizers** per
  direction at the tap boundary inside `traffic_counter`.
- Whether `trigger_logic` also owns the periodic-report timer or the core
  does (core timer saves logic, hardware timer saves instruction budget —
  Phase 1 experiment).

---

**Last Updated:** 2026-10-13
