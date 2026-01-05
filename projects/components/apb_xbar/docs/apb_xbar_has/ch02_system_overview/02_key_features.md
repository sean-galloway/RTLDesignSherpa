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

# Key Features

## Feature Summary

The APB Crossbar provides the following key features:

### F1: Parametric MxN Configuration

- Support for any combination of M masters and N slaves
- Pre-generated variants for common configurations (1x1, 2x1, 1x4, 2x4)
- Python generator for custom configurations up to 16x16
- Single RTL source serves all configurations

### F2: Automatic Address-Based Routing

- Parallel address decode for all slaves
- Fixed 64KB address space per slave
- Configurable base address via `BASE_ADDR` parameter
- Zero-decode-latency routing

**Address Calculation:**
```
slave_index = (PADDR - BASE_ADDR) >> 16
```

### F3: Round-Robin Arbitration

- Independent arbiter per slave
- Fair rotation of master priority
- No master starvation guaranteed
- Grant persistence through transaction completion

### F4: Zero-Bubble Throughput

- Back-to-back transactions without idle cycles
- Grant held during entire transaction
- Immediate response routing
- Maximum APB bandwidth utilization

### F5: Proven Building Blocks

- Built from production-tested `apb_slave.sv` and `apb_master.sv` modules
- No new protocol logic - pure composition
- Each component independently verified

## Feature Comparison

| Feature | apb_xbar_1to1 | apb_xbar_2to1 | apb_xbar_1to4 | apb_xbar_2to4 | apb_xbar_thin |
|---------|---------------|---------------|---------------|---------------|---------------|
| Masters | 1 | 2 | 1 | 4 | 1 |
| Slaves | 1 | 1 | 4 | 4 | 1 |
| Arbitration | No | Yes | No | Yes | No |
| Address Decode | No | No | Yes | Yes | No |
| Approximate LOC | 200 | 400 | 500 | 1000 | 150 |

: Pre-Generated Variant Comparison

## Design Philosophy

### Composition Over Complexity

The crossbar is built by composing well-tested building blocks:

1. **APB Slaves** (M instances) - Convert incoming APB to internal cmd/rsp
2. **Arbiters** (N instances) - Select winning master per slave
3. **Address Decode** - Route commands to appropriate slave
4. **Response Routing** - Return responses to originating masters
5. **APB Masters** (N instances) - Convert internal cmd/rsp back to APB

### Scalability

Resource usage scales predictably:
- M x N routing paths
- N independent arbiters
- Linear growth with configuration size

---

**Next:** [System Context](03_system_context.md)
