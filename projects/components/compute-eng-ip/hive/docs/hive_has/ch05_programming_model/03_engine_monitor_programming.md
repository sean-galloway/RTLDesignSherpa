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

# Engine Monitor Programming

The engine monitor is one gatling core (riscv-ip/gatling-rv32i): four
barrel contexts, context *n* watching compute engine *n*. Each context runs a
small monitor firmware image from its own 4 KB bank, and all four run the
same image. gatling contexts cannot tell themselves apart (`mhartid` reads 0
on every context, gatling PRD §3.3); instead the monitor top routes each
context's accesses to the peripheral window to its own engine's peripherals,
so the same address names a different engine's counters in each context.
(v0.2 had sixteen SERV cores, each reading its tile ID from a register at
0xF000_0000.)

What gatling's ISA means for monitor firmware:

- **RV32I only.** No CSRs: every CSR reads 0 and drops writes, and there is
  no cycle counter (Zicntr was removed from gatling). A time base comes from
  the peripheral window.
- **No interrupts.** Firmware polls `trigger_logic`'s flags; the hardware
  comparator keeps congestion detection inside its < 10 cycle budget
  whatever the firmware is doing.
- **A trap halts only the faulting context** (ecall, ebreak, an illegal or
  misaligned access). The other three engines stay monitored, and HIVE-C
  sees the halt in the context's status and can reload and restart it.
- **Throughput:** each context retires one instruction every four cycles
  (25 MIPS per engine at 100 MHz), where a SERV took one bit per cycle.

## Trigger Conditions

The monitor firmware evaluates five trigger classes:

| # | Trigger | Default threshold | Action |
|---|---------|-------------------|--------|
| 1 | Congestion | `buffer_occupancy > 75%` | Send PKT_STATUS congestion alert to HIVE-C; optionally throttle local injection |
| 2 | Error | parity error or protocol violation | Send error status packet; halt local injection pending recovery |
| 3 | Periodic report | 1000 cycles | Send statistics snapshot to HIVE-C |
| 4 | Descriptor queue event | RAPIDS completion signal | Notify HIVE-C for next-batch scheduling |
| 5 | Custom | user-defined via debug registers | Inject debug trace packet |

: Engine monitor trigger conditions

Thresholds, intervals, and enable bits are configurable by HIVE-C over the
control network at runtime.

## Inband Packet Injection

```c
// Monitor code to inject a packet through its engine's AXIS TX FIFO.
// Example: 2D transfer descriptor (PKT_CDA) — descriptors may be
// injected by the engine monitor as well as by HIVE-C.
void monitor_inject_packet(uint32_t *words, uint8_t nwords, uint8_t pkt_type,
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
in the per-engine `axis_injector` (MAS Chapter 2). A context should never
block on `tready` while holding time-critical counters — the reference
firmware snapshots metrics first, then transmits. A context spinning on
`tready` costs only its own slot in the rotation; the other three engines'
contexts keep their rate.

## Reporting Discipline

- **Periodic snapshots** ride the control network uplink (32-bit frames,
  round-robin arbitrated across the four engines).
- **Urgent alerts** (congestion, errors) may use either the control network
  fast path or a PKT_STATUS injection through Delta, per HIVE-C's runtime
  configuration; the control network is preferred during data-plane quiesce.
- **Timestamps** are monitor-clock cycle counts from the peripheral window;
  HIVE-C treats them as sequence indicators, not comparable clocks.

---

**Last Updated:** 2026-11-25
