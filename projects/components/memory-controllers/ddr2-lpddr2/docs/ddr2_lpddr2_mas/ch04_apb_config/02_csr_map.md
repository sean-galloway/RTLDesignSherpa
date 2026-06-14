<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> &middot; <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> &middot;
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> &middot;
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Register Map

**Status:** Skeleton — to be authored during MAS week


> The full CSR map is in HAS §6.3. This MAS section is the **implementation-level** view: how each register is generated, what the reset value generation rule is, how runtime overrides are staged, and the canonical CSR YAML source.

## Source of Truth

The CSR map is generated from `regs/ddr2_lpddr2_csrs.yaml` (PeakRDL- or RDL-style YAML). The build runs the generator to produce:

- `regs/ddr2_lpddr2_csr_pkg.sv` — SV package with offsets, masks, reset values
- `regs/ddr2_lpddr2_csr_block.sv` — the wrapped register file
- `regs/ddr2_lpddr2_csrs.h` — C header for software
- `regs/ddr2_lpddr2_csr_block_uvm.sv` — UVM register model

The MAS does not re-publish the bit-level register table; it documents the **generation pipeline** and the **runtime semantics** (quiet-point staging, etc.).

## Staging vs. Live State

Every R/W field has two storage cells:

1. **APB-side staging register** — written immediately on the APB write
2. **MC-side live register** — copied from staging on the next quiet point

The staging→live commit is one MC cycle. Reads can return either side depending on the field — observation fields (`OBS_*`) read live state; configuration fields (`*_TUNING`) read staging by default but switch to live after `CTRL.config_apply` is acknowledged.

## TODO

- CSR YAML schema reference
- Generation script invocation
- Quiet-point handshake protocol detail
- Software access pattern (config-apply sequence)
- Generated UVM register model overview

