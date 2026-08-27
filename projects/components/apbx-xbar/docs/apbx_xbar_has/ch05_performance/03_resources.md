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

## FPGA Resource Usage

### Pre-Generated Variants

Estimated resource usage for common configurations (32-bit data width):

| Variant | LUTs | FFs | Description |
|---------|------|-----|-------------|
| apbx_xbar_thin | ~50 | ~20 | Minimal passthrough |
| apbx_xbar_1to1 | ~150 | ~80 | Full 1x1 with buffering |
| apbx_xbar_2to1 | ~300 | ~150 | 2 masters, arbitration |
| apbx_xbar_1to4 | ~400 | ~200 | 4 slaves, decode |
| apbx_xbar_2to4 | ~800 | ~400 | Full 2x4 crossbar |

**Hand estimates, not synthesis results, and the single source of truth
for this component.** PRD §9.3 previously carried a second, different
set of numbers (2-3x smaller in every cell); that table now refers here
rather than competing with it. Nothing in the repo has been synthesized
to confirm either set -- treat these as order-of-magnitude only.

: FPGA Resource Estimates (32-bit)

### Scaling Factors

Resource usage scales approximately as:

| Component | Scaling | Notes |
|-----------|---------|-------|
| apb4_slave instances | M x base | Linear with masters |
| apb4_master instances | N x base | Linear with slaves |
| Arbiters | N x log2(M) | Per slave, sized for masters |
| Address decode | N | Comparators per slave |
| Response mux | N x M | Full crosspoint for responses |

: Resource Scaling Factors

## Lines of Code

Source code metrics for pre-generated variants:

| Variant | Lines of Code | Modules | Complexity |
|---------|---------------|---------|------------|
| apbx_xbar_thin | ~150 | 1 | Low |
| apbx_xbar_1to1 | ~200 | 3 | Low |
| apbx_xbar_2to1 | ~400 | 5 | Medium |
| apbx_xbar_1to4 | ~500 | 7 | Medium |
| apbx_xbar_2to4 | ~1000 | 11 | Medium-High |

: Source Code Metrics

## Power Considerations

### Static Power

Static power scales with:
- Total register count (FFs)
- Routing resources used
- Technology node

### Dynamic Power

Dynamic power depends on:
- Transaction rate (activity factor)
- Data width (toggling bits)
- Clock frequency

### Power Optimization

| Technique | Benefit | Trade-off |
|-----------|---------|-----------|
| Clock gating | Reduce idle power | Adds gating logic |
| Lower data width | Fewer toggling bits | Reduced throughput |
| Fewer slaves | Less decode logic | Reduced flexibility |

: Power Optimization Techniques

## Area Comparison

Relative area comparison (normalized to apbx_xbar_1to1):

| Variant | Relative Area |
|---------|---------------|
| apbx_xbar_thin | (withdrawn -- compared a 2x4 core against a 1x1; see CLAUDE.md) |
| apbx_xbar_1to1 | 1.0x (baseline) |
| apbx_xbar_2to1 | 2.0x |
| apbx_xbar_1to4 | 2.5x |
| apbx_xbar_2to4 | 5.0x |

: Relative Area Comparison

## Custom Configuration Estimation

For custom MxN configuration:

```
Estimated LUTs ~= 50 + (M * 75) + (N * 50) + (M * N * 10)
Estimated FFs  ~= 20 + (M * 40) + (N * 30)
```

**Example: 4x8 crossbar**
- LUTs: 50 + (4*75) + (8*50) + (4*8*10) = 50 + 300 + 400 + 320 = ~1070
- FFs: 20 + (4*40) + (8*30) = 20 + 160 + 240 = ~420

---

**Next:** [Chapter 6: Integration](../ch06_integration/01_system_requirements.md)
