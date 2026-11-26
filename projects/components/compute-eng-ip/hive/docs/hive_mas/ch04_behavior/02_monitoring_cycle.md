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

# The Monitoring Cycle, Step by Step

One engine's steady-state monitoring loop and its alert path: gatling
context *n* and engine *n*'s peripheral set. The other three contexts run
the same loop on their own engines, interleaved by gatling's rotation.

## Steady State (every `mon_clk` cycle, per engine)

1. `traffic_counter` samples the router tap: per-direction packet strobes
   increment `pkt_rx/tx_count`; occupancy strobes update `buffer_occupancy`.
2. `trigger_logic` compares occupancy against `cfg_threshold`; the
   congestion line is combinationally current with the tap (this is what
   meets the < 10-cycle detection target — no firmware round trip).
3. The context polls `trigger_logic` and the counter bank (gatling has no
   interrupts); on the periodic-report interval it snapshots metrics into
   the uplink frame. The context issues one instruction every four
   `mon_clk` cycles.

## Periodic Report

1. The context writes a status record into its engine's `ctrl_net_slave`
   uplink mailbox.
2. `control_arbiter` grants this slave's turn (round-robin; bounded wait
   ≤ 4 frames, one per engine).
3. Frame crosses `mon_clk → hive_c_clk` (4-entry FIFO), is consumed by
   `ctrl_net_master`, and lands in the engine-monitor status AXIL window for
   firmware.

## Congestion Alert (urgent path)

```
occupancy > threshold        (combinational, tap-current)
  → trigger_logic raises the engine's flag (≤ 1 cycle)
  → the context sees it at its next poll and assembles PKT_STATUS 0x04
    (alert) — or the injector forwards a hardware pre-latched snapshot if
    configured (≤ 5 cycles to tvalid)
  → axis_injector commits: tuser=2'b11, tid = engine id
  → CDC into delta_clk; routed to HIVE-C (tdest=17) or control network
    urgent slot, per runtime configuration
```

The firmware poll adds up to one poll loop of latency to a firmware-built
alert (each loop instruction costs four cycles); the pre-latched snapshot
path does not wait for the context.

## Error Path

Parity/protocol-violation strobes set sticky `error_flags`, which the
context sees at its next poll; it emits status type `0x08` and, per policy,
may assert the local injection-halt line (its own engine's aperture only —
it cannot silence the compute element, which is Delta's path).

---

**Last Updated:** 2026-11-25
