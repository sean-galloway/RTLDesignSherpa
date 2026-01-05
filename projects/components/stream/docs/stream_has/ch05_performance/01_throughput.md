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

# Throughput Targets

## Theoretical Maximum

### Per-Interface Bandwidth

| Interface | Data Width | Frequency | Bandwidth |
|-----------|------------|-----------|-----------|
| Descriptor Fetch | 256 bits | 200 MHz | 6.4 GB/s |
| Data Read | 512 bits | 200 MHz | 12.8 GB/s |
| Data Write | 512 bits | 200 MHz | 12.8 GB/s |

### Aggregate Bandwidth

- **Bidirectional:** 25.6 GB/s (simultaneous read + write)
- **Descriptor Overhead:** ~0.1% for large transfers

---

## Practical Throughput

### Single-Channel Performance

| Scenario | Expected Efficiency | Effective Bandwidth |
|----------|---------------------|---------------------|
| Large sequential (>1MB) | >95% | >12.0 GB/s |
| Medium sequential (64KB-1MB) | 85-95% | 10.8-12.0 GB/s |
| Small sequential (4KB-64KB) | 70-85% | 9.0-10.8 GB/s |
| Very small (<4KB) | 40-70% | 5.0-9.0 GB/s |

### Multi-Channel Performance

| Active Channels | Per-Channel BW | Aggregate BW |
|-----------------|----------------|--------------|
| 1 | 12.8 GB/s | 12.8 GB/s |
| 2 | 6.4 GB/s | 12.8 GB/s |
| 4 | 3.2 GB/s | 12.8 GB/s |
| 8 | 1.6 GB/s | 12.8 GB/s |

**Note:** Aggregate limited by shared AXI masters. Individual channel throughput scales inversely with active channel count.

---

## Throughput Limiting Factors

### Memory System Factors

| Factor | Impact | Mitigation |
|--------|--------|------------|
| Memory latency | Reduces efficiency for small transfers | Use deeper outstanding |
| Memory bandwidth | Hard limit | Match STREAM to memory capability |
| Interconnect contention | Variable impact | Priority configuration |

### STREAM Internal Factors

| Factor | Impact | Mitigation |
|--------|--------|------------|
| Descriptor fetch overhead | Fixed per descriptor | Use longer transfers |
| SRAM depth | Limits outstanding | Configure adequate depth |
| Arbitration overhead | Multi-channel penalty | Reduce active channels |
| Burst splitting | 4KB boundary crossings | Align transfers |

---

## Performance Targets

### Design Targets

| Metric | Target | Condition |
|--------|--------|-----------|
| **Peak throughput** | 12.8 GB/s | Single direction, ideal |
| **Sustained throughput** | >11.0 GB/s | Large transfers, single channel |
| **Multi-channel aggregate** | >10.0 GB/s | 8 channels active |
| **Small transfer efficiency** | >50% | 4KB transfers |

### Verification Criteria

| Scenario | Pass Criteria |
|----------|---------------|
| 1MB sequential read | >95% efficiency |
| 1MB sequential write | >95% efficiency |
| 64KB scatter (4x16KB) | >80% efficiency |
| 4KB × 100 descriptors | >60% efficiency |

---

## Descriptor Chain Efficiency

### Descriptor Overhead

| Transfer Size | Descriptor Fetches | Overhead |
|---------------|-------------------|----------|
| 64 KB | 1 | 0.05% |
| 256 KB | 1 | 0.01% |
| 1 MB | 1 | <0.01% |
| 4 KB (100 chained) | 100 | 0.5% |

### Chaining Efficiency

For chained descriptors, next descriptor fetch can overlap with current transfer:

```
Desc 0: [Fetch][-----Transfer 0-----]
Desc 1:             [Fetch][-----Transfer 1-----]
Desc 2:                         [Fetch][-----Transfer 2-----]
```

This pipelining minimizes chaining overhead for continuous transfers.

---

**Last Updated:** 2026-01-03
