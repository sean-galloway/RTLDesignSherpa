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

# Pipeline Overview

The Delta generator uses the `Module` framework from `bin/rtl_generators/verilog/`. It builds the RTL as a sequence of method calls that append comments, instructions, and assignments to an internal buffer, then writes the completed module to disk.

![Delta Generator Pipeline](assets/images/delta_generator_pipeline.png)

**Figure 1: Delta Generator Pipeline.** The generator takes CLI/API arguments, builds a `DeltaConfig`, constructs the `DeltaFlatCrossbar` object, and calls `verilog()` to emit the flat crossbar file. Optional tree primitives are emitted separately.

## Stages

1. **Argument parsing** — CLI flags become `DeltaConfig` fields.
2. **Width calculation** — `dest_width` and `id_width` are derived from `num_slaves` and `num_masters` unless overridden.
3. **Object construction** — `DeltaFlatCrossbar(config)` declares parameters and ports through the framework.
4. **RTL emission** — `verilog()` calls the generator methods in order:
   - `generate_header_comment()`
   - `generate_request_decode()`
   - `generate_arbiter_logic()`
   - `generate_crossbar_mux()`
   - `generate_backpressure_logic()`
   - `generate_wakeup_logic()` (AMBA 5 only)
   - `generate_performance_counters()` (unless disabled)
   - `generate_assertions()`
5. **Framework finalization** — `start()` emits the module header; `end()` emits `endmodule`.
6. **File write** — `write()` saves `delta_axis_flat_<M>x<N>.sv`.

The `complete_tree_generator.py` script is independent and emits splitter/merger/tree scaffolds directly as strings.
