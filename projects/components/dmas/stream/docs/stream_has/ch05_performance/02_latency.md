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

# Latency Characteristics

## Latency Components

### End-to-End Latency Breakdown

For a single-descriptor transfer (kick-off to completion):

| Phase | Typical Cycles | Notes |
|-------|----------------|-------|
| APB write processing | 2-3 | APB transaction |
| Descriptor fetch | 10-50 | Memory latency dependent |
| Descriptor parse | 2-4 | Fixed pipeline |
| Arbitration wait | 0-100+ | Depends on contention |
| Read phase setup | 2-3 | AXI AR channel |
| Read data transfer | N + 10-50 | N beats + memory latency |
| Write phase setup | 2-3 | AXI AW channel |
| Write data transfer | N + 5-20 | N beats + response latency |
| Completion handling | 2-4 | Status update, IRQ |

### Total Latency Formula

```
Latency = T_apb + T_desc_fetch + T_parse + T_arb + T_read + T_write + T_complete

Where:
  T_apb        = 3 cycles (fixed)
  T_desc_fetch = Memory_latency + 10 cycles
  T_parse      = 3 cycles (fixed)
  T_arb        = 0 to N (contention dependent)
  T_read       = Memory_latency + (Transfer_length / Beats_per_burst) * Burst_overhead + Transfer_length
  T_write      = Memory_latency + Transfer_length + Response_latency
  T_complete   = 3 cycles (fixed)
```

---

## First-Byte Latency

Time from kick-off to first data beat arriving at destination:

| Component | Cycles | Cumulative |
|-----------|--------|------------|
| APB processing | 3 | 3 |
| Descriptor fetch | 30 | 33 |
| Parse + setup | 5 | 38 |
| Read AR accepted | 10 | 48 |
| First read data | 20 | 68 |
| Write AW + first W | 10 | 78 |
| **Total** | **~80** | - |

At 200 MHz: ~400 ns first-byte latency (typical)

---

## Latency by Transfer Size

### Small Transfers

| Transfer Size | Total Latency | Efficiency |
|---------------|---------------|------------|
| 64 bytes (1 beat) | ~100 cycles | 1% |
| 256 bytes (4 beats) | ~110 cycles | 4% |
| 1 KB (16 beats) | ~130 cycles | 12% |
| 4 KB (64 beats) | ~180 cycles | 35% |

### Large Transfers

| Transfer Size | Total Latency | Efficiency |
|---------------|---------------|------------|
| 16 KB (256 beats) | ~400 cycles | 64% |
| 64 KB (1024 beats) | ~1200 cycles | 85% |
| 256 KB (4096 beats) | ~4400 cycles | 93% |
| 1 MB (16384 beats) | ~17000 cycles | 96% |

---

## Latency Variability

### Sources of Variability

| Source | Impact | Range |
|--------|--------|-------|
| Memory system load | High | 10-100+ cycles |
| AXI interconnect | Medium | 5-50 cycles |
| Channel arbitration | Medium | 0-100+ cycles |
| Descriptor chaining | Low | 2-5 cycles |

### Worst-Case Latency

Conditions for worst-case latency:

1. All 8 channels active (maximum arbitration delay)
2. Memory system fully loaded (maximum memory latency)
3. Small transfer size (maximum overhead ratio)
4. Low priority descriptor (maximum wait time)

Under these conditions, first-byte latency could exceed 1000 cycles.

---

## Latency Optimization

### Software Recommendations

| Recommendation | Benefit |
|----------------|---------|
| Use larger transfers | Better efficiency |
| Minimize active channels | Reduce arbitration |
| Use higher priority for latency-sensitive | Earlier service |
| Pre-stage descriptors in cache | Faster fetch |

### Hardware Configuration

| Setting | Effect |
|---------|--------|
| Increase outstanding limit | Hide memory latency |
| Enable descriptor prefetch | Reduce chaining overhead |
| Configure larger SRAM | Support longer bursts |

---

## Interrupt Latency

Time from transfer completion to interrupt assertion:

| Phase | Cycles |
|-------|--------|
| Last write response | 0 |
| Completion FSM | 2 |
| Status register update | 1 |
| Interrupt assertion | 1 |
| **Total** | **4 cycles** |

At 200 MHz: 20 ns from completion to interrupt.

---

**Last Updated:** 2026-01-03
