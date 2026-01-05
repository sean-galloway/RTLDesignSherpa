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

# Throughput Characteristics

## Maximum Throughput

### Single Master

With a single master accessing any slave:

| Metric | Value | Notes |
|--------|-------|-------|
| Minimum cycles per transaction | 2 | APB protocol minimum |
| Maximum transactions per cycle | 0.5 | 1 transaction / 2 cycles |
| Data throughput (32-bit @ 100MHz) | 200 MB/s | Theoretical maximum |
| Data throughput (32-bit @ 250MHz) | 500 MB/s | Theoretical maximum |

: Single Master Throughput

### Multi-Master (Uncontended)

When masters access different slaves:
- Each master achieves single-master throughput
- Aggregate throughput = M x single-master throughput
- No arbitration overhead

### Multi-Master (Contended)

When masters compete for the same slave:

| Masters | Effective Throughput | Notes |
|---------|---------------------|-------|
| 2 | 50% per master | Round-robin sharing |
| 3 | 33% per master | Round-robin sharing |
| 4 | 25% per master | Round-robin sharing |

: Contended Access Throughput

## Zero-Bubble Operation

### Grant Persistence

The crossbar implements grant persistence:
- Once a master wins arbitration, it holds the grant
- Grant released only when master releases PSEL
- Enables back-to-back transactions without re-arbitration

### Back-to-Back Timing

```
       Cycle 1    Cycle 2    Cycle 3    Cycle 4
       |  T1 setup|  T1 data |  T2 setup|  T2 data|
PSEL   --|--------|----------|----------|----------|--
PENABLE--|________|----------|__________|----------|--
PREADY  _|________|----------|__________|----------|__

Transaction T1 and T2 are consecutive with no idle cycles.
```

## Throughput Factors

### Factors That Reduce Throughput

| Factor | Impact | Mitigation |
|--------|--------|------------|
| Slave wait states | Variable | Choose faster peripherals |
| Arbitration conflicts | 1+ cycle | Distribute access across slaves |
| Slave response time | Variable | Design slaves for quick response |

: Throughput Reduction Factors

### Optimal Usage Pattern

For maximum throughput:
1. Distribute master access across different slaves
2. Minimize slave wait states
3. Use burst-like access patterns (same master, same slave)
4. Avoid rapid master switching on same slave

---

**Next:** [Latency Analysis](02_latency.md)
