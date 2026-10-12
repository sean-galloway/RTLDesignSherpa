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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Module Header and Parameters

The `Module` framework emits the module header automatically from the parameter and port strings added by `DeltaFlatCrossbar.__init__`.

## Header comment

The generated file begins with a block comment documenting the configuration:

```systemverilog
//==============================================================================
// Module: delta_axis_flat_2x4
// Project: Delta - AXI-Stream Crossbar Generator
//==============================================================================
// Description: AXI-Stream 2×4 Flat Crossbar Switch
//
// Configuration:
//   - Topology: flat
//   - Masters: 2
//   - Slaves: 4
//   - Data Width: 64 bits
//   - TDEST Width: 2 bits
//   - TID Width: 1 bits
//   - Arbiter: round_robin
//
// Features:
//   - Per-slave round-robin arbitration
//   - Packet atomicity (locked grant until TLAST)
//   - Registered outputs for timing closure
//   - Full AXI-Stream compliance
//==============================================================================
```

## Port naming convention

| Direction | Naming |
|-----------|--------|
| Master-side inputs | `s_axis_<signal>[NUM_MASTERS]` |
| Master-side outputs | `s_axis_tready[NUM_MASTERS]` |
| Slave-side outputs | `m_axis_<signal>[NUM_SLAVES]` |
| Slave-side inputs | `m_axis_tready[NUM_SLAVES]` |

Optional signals (`tstrb`, `twakeup`, the `t*chk` check signals and the `s_/m_parity_error` flags) are declared only when enabled. With `--amba5` the header also gains derived check-width parameters (`TDATACHK_W = DATA_WIDTH / 8` and so on), and the module instantiates `rtl/common/dataint_parity`.
