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

# What the Generator Produces

The Delta generator (`bin/delta_generator.py`) emits a parameterized AXI-Stream flat crossbar module. A companion script (`bin/complete_tree_generator.py`) emits tree-structured primitives (1:2 splitters, 2:1 mergers, fan-out trees, and fan-in trees). All output is single-file SystemVerilog with no post-processing required.

## Output artifacts

| Artifact | Description |
|----------|-------------|
| `delta_axis_flat_<M>x<N>.sv` | Core flat crossbar module. |
| `delta_split_1to2.sv` | 1:2 splitter primitive (when `--nodes` is used). |
| `delta_merge_2to1.sv` | 2:1 merger primitive from `complete_tree_generator.py`. |
| `delta_fanout_1to<N>.sv` | Fan-out tree scaffold (partial implementation). |
| `delta_fanin_<N>to1.sv` | Fan-in tree scaffold (partial implementation). |

## Architecture in the generated flat module

The generated `delta_axis_flat_<M>x<N>` module contains:

1. **Request decode** — `TDEST` is decoded directly into a slave request matrix.
2. **Per-slave arbitration** — round-robin with packet atomicity (grant held until `TLAST`).
3. **Crossbar mux** — routes `TDATA`, `TVALID`, `TLAST`, `TDEST`, `TID`, `TUSER`, optional `TSTRB`, and with `--amba5` the payload check bits.
4. **Optional AMBA 5 logic** — `TWAKEUP` steering, plus the IHI 0051B ch. 5 check signals: payload checks on ingress, control checks generated or checked, and sticky per-port error flags. Built from `rtl/common/dataint_parity`.
5. **Backpressure logic** — `s_axis_tready` driven from `m_axis_tready` of the granted slave.
6. **Optional performance counters** — packet counts per master and per slave.
7. **Optional assertions** — one-hot grant and TDEST-range checks under `FORMAL`.

Tree generation is currently a scaffold; the flat crossbar is the production-ready artifact.
