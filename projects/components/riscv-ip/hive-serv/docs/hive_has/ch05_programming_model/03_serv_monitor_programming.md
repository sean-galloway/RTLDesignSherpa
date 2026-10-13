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

# SERV Monitor Programming

Each SERV runs a small monitor firmware image (hand-optimized RV32I
assembly is expected; a SERV executes one bit per cycle, so instruction
count directly buys reaction latency). All sixteen instances run the same
image; per-tile identity comes from a read-only tile-ID register the wrapper
exposes at address 0xF000_0000.

## Trigger Conditions

The monitor firmware evaluates five trigger classes:

| # | Trigger | Default threshold | Action |
|---|---------|-------------------|--------|
| 1 | Congestion | `buffer_occupancy > 75%` | Send PKT_STATUS congestion alert to HIVE-C; optionally throttle local injection |
| 2 | Error | parity error or protocol violation | Send error status packet; halt local injection pending recovery |
| 3 | Periodic report | 1000 cycles | Send statistics snapshot to HIVE-C |
| 4 | Descriptor queue event | RAPIDS completion signal | Notify HIVE-C for next-batch scheduling |
| 5 | Custom | user-defined via debug registers | Inject debug trace packet |

: SERV trigger conditions

Thresholds, intervals, and enable bits are configurable by HIVE-C over the
control network at runtime.

## Inband Packet Injection

```c
// SERV code to inject a packet through the AXIS TX FIFO.
// Example: 2D transfer descriptor (PKT_CDA) — descriptors may be
// injected by SERVs as well as by HIVE-C.
void serv_inject_packet(uint32_t *words, uint8_t nwords, uint8_t pkt_type,
                        uint8_t tdest) {
    for (int i = 0; i < nwords; i++) {
        AXIS_TX_FIFO[i] = words[i];
    }
    AXIS_TX_TUSER  = pkt_type;   // 2'b10 PKT_CONFIG, 2'b11 PKT_STATUS, ...
    AXIS_TX_TDEST  = tdest;
    AXIS_TX_TLAST  = 1;
    AXIS_TX_TVALID = 1;
    while (!AXIS_TX_READY) { }   // Wait for handshake
    AXIS_TX_TVALID = 0;
}
```

The TX FIFO abstracts the AXIS master; depth and handshaking are implemented
in the wrapper (MAS Chapter 2). A SERV should never block on `tready` while
holding time-critical counters — the reference firmware snapshots metrics
first, then transmits.

## Reporting Discipline

- **Periodic snapshots** ride the control network uplink (32-bit frames,
  round-robin arbitrated).
- **Urgent alerts** (congestion, errors) may use either the control network
  fast path or a PKT_STATUS injection through Delta, per HIVE-C's runtime
  configuration; the control network is preferred during data-plane quiesce.
- **Timestamps** are local `serv_clk` cycle counts; HIVE-C treats them as
  sequence indicators, not comparable clocks.

---

**Last Updated:** 2026-10-12
