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

# Boundary Module Instantiation

Delta does not instantiate external boundary modules for the flat crossbar. The `DeltaFlatCrossbar` class directly emits the full crossbar logic using the `Module` framework. However, the generator does produce small protocol-agnostic primitives when tree generation is requested.

## Flat crossbar

The entire crossbar is self-contained in `delta_axis_flat_<M>x<N>.sv`:

- No external arbiter module is instantiated; arbitration is emitted inline.
- No external FIFOs are used; the design is purely combinational between registered arbitration state.

## Tree primitives

When `--nodes` is passed, `delta_split_1to2.sv` is emitted by the same generator. The `complete_tree_generator.py` script emits additional primitives:

| Primitive | Purpose |
|-----------|---------|
| `delta_split_1to2` | Routes one AXI-Stream input to two outputs based on a `TDEST` bit. |
| `delta_merge_2to1` | Arbiters two inputs to one output with packet atomicity. |
| `delta_fanout_1to<N>` | Schematic fan-out tree using splitters (partial implementation). |
| `delta_fanin_<N>to1` | Schematic fan-in tree using mergers (partial implementation). |

: Tree Primitives

The tree primitives are not yet production-complete; they exist as building blocks and documentation of the intended topology.
