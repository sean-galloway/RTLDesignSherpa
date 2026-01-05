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

# Document Conventions

## Terminology

| Term | Definition |
|------|------------|
| Master | AXI4 initiator that issues transactions |
| Slave | AXI4 target that responds to transactions |
| Crossbar | NxM interconnect connecting masters to slaves |
| Channel | AXI4 communication path (AW, W, B, AR, R) |
| Converter | Logic that transforms width or protocol |

: Table 1.1: Common Terminology

## Signal Naming

Bridge uses consistent signal prefixes:

| Prefix | Meaning |
|--------|---------|
| `s_*` | Slave-side interface (master port on bridge) |
| `m_*` | Master-side interface (slave port on bridge) |
| `axi4_*` | AXI4 protocol signals |
| `apb_*` | APB protocol signals |
| `cfg_*` | Configuration signals |
| `dbg_*` | Debug signals |

: Table 1.2: Signal Naming Prefixes

## Diagrams

### Figure 1.1: Block Diagram Legend

Block diagrams in this specification use the following conventions:

| Symbol | Meaning |
|--------|---------|
| Rectangle | Functional block |
| Arrow | Data/signal flow |
| Dashed box | Optional/configurable block |
| Double line | Multi-signal bus |

: Table 1.3: Block Diagram Symbols

## Code Examples

SystemVerilog code examples are formatted as:

```systemverilog
// Module instantiation example
bridge_4x4 u_bridge (
    .aclk       (sys_clk),
    .aresetn    (sys_rst_n),
    // ... port connections
);
```

## Parameter Notation

Parameters use the following format:

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| NUM_MASTERS | int | 1-32 | 2 | Number of master ports |
| NUM_SLAVES | int | 1-256 | 2 | Number of slave ports |

: Table 1.4: Parameter Format Example
