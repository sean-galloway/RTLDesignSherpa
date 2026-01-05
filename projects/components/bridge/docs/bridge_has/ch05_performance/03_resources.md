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

# Resource Estimates

## FPGA Resource Summary

### Baseline Configuration (2x2, 64-bit)

| Resource | Count | Notes |
|----------|-------|-------|
| LUTs | ~2,000-3,000 | Logic and routing |
| Registers | ~1,500-2,000 | Pipeline stages |
| Block RAM | 0-1 | Optional ID CAM |
| DSP | 0 | No arithmetic |

: Table 5.11: Baseline Resource Requirements

### Scaling Factors

| Component | Scaling |
|-----------|---------|
| Crossbar core | O(M x N) |
| Master adapters | O(M) |
| Slave routers | O(N) |
| ID tracking | O(M x Outstanding) |
| Width converters | O(per-path ratio) |

: Table 5.12: Resource Scaling Factors

## Component Breakdown

### Per-Master Resources

| Component | LUTs | Registers |
|-----------|------|-----------|
| Skid buffer | ~50-100 | ~DATA_WIDTH |
| ID extension | ~20 | ~ID_WIDTH |
| Channel mux | ~100 | ~50 |
| **Per Master Total** | ~200-300 | ~DATA_WIDTH + 100 |

: Table 5.13: Per-Master Resource Breakdown

### Per-Slave Resources

| Component | LUTs | Registers |
|-----------|------|-----------|
| Address decode | ~50 | 0 |
| Arbiter | ~100-200 | ~50 |
| Response mux | ~100 | ~50 |
| **Per Slave Total** | ~250-350 | ~100 |

: Table 5.14: Per-Slave Resource Breakdown

### Crossbar Core

| Component | LUTs | Registers |
|-----------|------|-----------|
| AW mux (N-way) | ~100 x N | ~50 x N |
| W mux (N-way) | ~100 x N | ~50 x N |
| B demux (M-way) | ~50 x M | ~50 x M |
| AR mux (N-way) | ~100 x N | ~50 x N |
| R demux (M-way) | ~50 x M | ~50 x M |

: Table 5.15: Crossbar Core Resources

## Width Converter Resources

| Ratio | LUTs | Registers | Notes |
|-------|------|-----------|-------|
| 1:2 upsize | ~200 | ~DATA_IN | Pack logic |
| 1:4 upsize | ~300 | ~DATA_IN | Pack logic |
| 1:8 upsize | ~400 | ~DATA_IN | Pack logic |
| 2:1 downsize | ~200 | ~DATA_OUT | Split logic |
| 4:1 downsize | ~300 | ~DATA_OUT | Split logic |
| 8:1 downsize | ~400 | ~DATA_OUT | Split logic |

: Table 5.16: Width Converter Resources

## Protocol Converter Resources

### AXI4 to APB

| Component | LUTs | Registers |
|-----------|------|-----------|
| FSM | ~100 | ~20 |
| Burst counter | ~50 | ~8 |
| Data buffer | ~100 | ~DATA_WIDTH |
| Response logic | ~50 | ~10 |
| **Total** | ~300 | ~DATA_WIDTH + 50 |

: Table 5.17: AXI4 to APB Converter Resources

## Example Configurations

| Config | Masters | Slaves | Data | LUTs | Registers |
|--------|---------|--------|------|------|-----------|
| 2x2 Basic | 2 | 2 | 64 | ~2,500 | ~1,500 |
| 4x4 Standard | 4 | 4 | 64 | ~5,000 | ~3,000 |
| 4x4 Wide | 4 | 4 | 256 | ~8,000 | ~5,000 |
| 8x8 Large | 8 | 8 | 128 | ~12,000 | ~8,000 |
| RAPIDS (4x3) | 4 | 3 | 512 | ~10,000 | ~6,000 |

: Table 5.18: Complete Bridge Resource Estimates

### Notes

- Estimates include all converters and adapters
- Actual results vary by synthesis tool and FPGA family
- Block RAM usage depends on ID table implementation
- DSP usage is zero (no multiplication/division)

## Optimization Strategies

### Resource Reduction

1. **Use channel-specific masters** - 40-60% port reduction
2. **Match data widths** - Avoid converter logic
3. **Use APB sparingly** - Reduces AXI4 overhead
4. **Limit outstanding transactions** - Smaller ID tables

### Performance/Resource Trade-off

| Feature | Resource Impact | Performance Impact |
|---------|-----------------|-------------------|
| Deeper skid buffers | +registers | +timing margin |
| Larger ID tables | +BRAM | +OOO depth |
| Pipeline stages | +registers | +frequency |
| Wider data paths | +routing | +throughput |

: Table 5.19: Performance/Resource Trade-offs
