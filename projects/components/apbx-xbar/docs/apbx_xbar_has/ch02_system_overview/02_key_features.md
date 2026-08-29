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
slave_index = ((PADDR - BASE_ADDR) >> 16)[$clog2(S)-1:0]
```

### F3: Round-Robin Arbitration

- Independent arbiter per slave
- Fair rotation of master priority
- No master starvation guaranteed
- Grant persistence through transaction completion

### F4: Back-to-Back Transactions

- Accepted with no master-side idle cycles required
- Grant held for the duration of one transaction, released at the
  response handshake
- They do NOT overlap inside the fabric: `apb4_slave` is
  one-command-at-a-time. Sustained cadence measures 10 pclk cycles
  PREADY-to-PREADY, one more than the 9-cycle SETUP-to-PREADY single
  transfer, the extra cycle being the next transfer's mandatory SETUP
  phase (see 5.1/5.2)

### F5: Proven Building Blocks

- Built from production-tested `apb4_slave.sv` and `apb4_master.sv` modules
- No new protocol logic - pure composition
- Each component independently verified

## Feature Comparison

| Feature | apbx_xbar_1to1 | apbx_xbar_2to1 | apbx_xbar_1to4 | apbx_xbar_2to4 | apbx_xbar_2to2_mixed |
|---------|---------------|---------------|---------------|---------------|---------------|
| Masters | 1 | 2 | 1 | 2 | 2 |
| Slaves | 1 | 1 | 4 | 4 | 2 |
| Arbitration | No | Yes | No | Yes | Yes |
| Address Decode | No | No | Yes | Yes | Yes |
| APB5 sideband | No | No | No | No | Yes -- per-port version gating |

: Pre-Generated Variant Comparison

All five are generator output. LOC per variant is in HAS
ch05_performance/03_resources.md, the single source of truth for it -- the
row that used to sit in this table drifted stale within two days of being
reconciled. `apbx_xbar_thin`, a hand-written
parameterized core that once occupied a sixth column here, was retired
and deleted on 2026-08-27 along with its tests, formal harnesses and
testplan; nothing in the tree depends on it.

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
