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

The generator runs in a single Python function (`generate_apbx_xbar`) and emits one SystemVerilog file. There is no separate AST framework; the output is built by string composition.

![APB Crossbar Generator Pipeline](assets/images/apbx_xbar_generator_pipeline.png)

**Figure 1: APB Crossbar Generator Pipeline.** The generator takes scalar arguments and version lists, validates them, then emits the module header, master-side boundary modules, decode/arbitrate/routing fabric, and slave-side boundary modules.

## Stages

1. **Validation** — counts, version lists, and `slave_size` checks.
2. **Header emission** — SPDX banner, module name, parameter list, port list, and address-map comment.
3. **Master-side boundary instantiation** — one `apb4_slave` or `apb5_slave` per master with its cmd/rsp nets.
4. **Request decode** — per-master address-to-slave index calculation (offset from `BASE_ADDR`).
5. **Arbitration and routing** — per-slave round-robin arbiter, command mux, response mux, and ready routing.
6. **Slave-side boundary instantiation** — one `apb4_master` or `apb5_master` per slave.
7. **Footer** — `endmodule` and module-name label.

The batch script `generate_xbars.py` loops over the standard variant table and calls the generator once per variant.
