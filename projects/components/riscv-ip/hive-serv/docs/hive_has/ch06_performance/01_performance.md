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

# Performance Characteristics

All values in this chapter are **targets**, not measured results — they are
the acceptance criteria RTL bring-up will be verified against.

## Latency Targets

| Metric | Target | Notes |
|--------|--------|-------|
| Descriptor injection (HIVE-C → RAPIDS) | < 30 cycles | Includes AXIS handshake + Delta traversal |
| CDA packet latency through Delta | ~10-20 cycles | One hop per router; tile 16 is edge-attached |
| Command response (host → HIVE-C action) | < 1 µs @ 100 MHz | Host interface round trip |
| Context switch (incl. quiesce) | < 25 cycles | Deterministic; 10-20 typical |
| Congestion detection (occupancy → alert sent) | < 10 cycles | SERV trigger evaluation + packetize |
| Status packet generation | < 5 cycles | From trigger to `tvalid` |
| SERV aggregation (all 16 via control network) | < 100 cycles | HIVE-C-side collection; per-uplink < 20 |

: Latency targets

## Throughput and Overhead Targets

| Metric | Target |
|--------|--------|
| Delta Network throughput | ≥ 80% of theoretical maximum |
| SERV monitoring overhead | < 5% of compute time |
| Context-switch overhead | < 1% for 1000+ cycle phases |
| Descriptor processing | Continuous, no stalls at full injection rate |

: Throughput and overhead targets

## Design Tradeoffs

**Virtual channels per router** (Delta-owned; HIVE is the consumer that
cares about deadlock freedom and latency):

| VCs | Area (LUTs) | Max Freq (MHz) | Deadlock Free | Latency (cycles) | Verdict |
|-----|-------------|----------------|---------------|------------------|---------|
| 1 | 400 | 250 | No | 3.2 | Minimal area, unsafe for XY |
| 2 | 500 | 220 | Yes (XY) | 3.5 | **PoC choice** |
| 4 | 650 | 180 | Yes | 4.1 | QoS headroom, revisit at 8×8 |

: VC tradeoff (per router estimates)

**SERV reporting interval** (how often each monitor reports):

| Interval (cycles) | Overhead (%) | Detection Latency | Memory (bytes) |
|-------------------|--------------|-------------------|----------------|
| 100 | 8.5 | Excellent | 512 |
| 500 | 2.1 | Good | 256 |
| 1000 | 1.2 | Acceptable | **PoC default (128)** |
| 5000 | 0.3 | Poor | 64 |

: SERV interval tradeoff

## Success Criteria

Functional: inband descriptor control demonstrated end-to-end; 16 monitors
tracking accurately; context switch < 25 cycles; correct routing for all
four packet classes; zero packet loss under normal operation; congestion
alert < 10 cycles.

Performance: ≥ 100 MHz on NexysA7 100T; descriptor injection < 30 cycles;
NoC ≥ 80% theoretical throughput; SERV overhead < 5%; switch overhead < 1%
on 1000+ cycle phases.

Educational: SimPy models predict hardware within ±10%; 100% of RTL modules
with passing unit tests; API docs with examples; ≥ 5 tutorials; modular
replacement of any block without system redesign.

---

**Last Updated:** 2026-10-12
