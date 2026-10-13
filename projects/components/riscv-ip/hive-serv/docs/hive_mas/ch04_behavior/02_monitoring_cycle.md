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

One SERV monitor's steady-state loop and its alert path.

## Steady State (every `serv_clk` cycle)

1. `traffic_counter` samples the router tap: per-direction packet strobes
   increment `pkt_rx/tx_count`; occupancy strobes update `buffer_occupancy`.
2. `trigger_logic` compares occupancy against `cfg_threshold`; the
   congestion line is combinationally current with the tap (this is what
   meets the < 10-cycle detection target — no firmware round trip).
3. The SERV core polls (or is interrupted by) `trigger_logic` and the
   counter bank; on the periodic-report interval it snapshots metrics into
   the uplink frame.

## Periodic Report

1. Core writes a status record into `ctrl_net_slave`'s uplink mailbox.
2. `control_arbiter` grants this slave's turn (round-robin; bounded wait
   ≤ 16 frames).
3. Frame crosses `serv_clk → hive_c_clk` (4-entry FIFO), is consumed by
   `ctrl_net_master`, and lands in the SERV-status AXIL window for firmware.

## Congestion Alert (urgent path)

```
occupancy > threshold        (combinational, tap-current)
  → trigger_logic flags core (≤ 1 cycle)
  → core assembles PKT_STATUS 0x04 (alert) — or forwards a hardware
    pre-latched snapshot if configured (≤ 5 cycles to tvalid)
  → axis_injector commits: tuser=2'b11, tid = tile id
  → CDC into delta_clk; routed to HIVE-C (tdest=17) or control network
    urgent slot, per runtime configuration
```

## Error Path

Parity/protocol-violation strobes set sticky `error_flags` and interrupt
the core immediately; the core emits status type `0x08` and, per policy,
may assert the local injection-halt line (its own aperture only — it
cannot silence the compute element, which is Delta's path).

---

**Last Updated:** 2026-10-12
