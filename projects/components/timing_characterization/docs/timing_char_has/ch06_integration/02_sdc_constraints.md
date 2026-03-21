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

# 6.2 SDC Constraints

## Multi-Flow SDC

The constraint file `char_top.sdc` supports three flows via the `FLOW` variable:

| Flow | Tool | Setup Required |
|------|------|---------------|
| `"asic"` | Synopsys DC / Cadence Genus | Target library, operating conditions |
| `"vivado"` | Xilinx Vivado | Part number |
| `"quartus"` | Intel Quartus Prime | FAMILY, DEVICE in .qsf |

## Overridable Parameters

All SDC parameters use `if {![info exists ...]}` guards for external override:

| SDC Variable | Default | Description |
|-------------|---------|-------------|
| `FLOW` | `"asic"` | Selects tool-specific constraint blocks |
| `TARGET_FREQ_MHZ` | 500.0 | Target clock frequency |
| `INPUT_DELAY_FRACTION` | 0.80 | Input delay as fraction of period |
| `OUTPUT_DELAY_FRACTION` | 0.20 | Output delay as fraction of period |
| `CLK_UNCERTAINTY_NS` | 0.100 | Clock uncertainty (jitter + skew) |

## The 80/20 I/O Split

The 80% input / 20% output delay split forces all interesting timing into
register-to-register paths within each FUB:

- **80% input delay:** Consumed by the LFSR-to-FUB-input path (trivially met)
- **20% output delay:** Consumed by the FUB-output-to-port path (trivially met)
- **Register-to-register paths:** Where the real characterization data lives

## Per-Flow Specifics

- **ASIC:** Enables `group_path` for per-FUB reporting and `set_dont_touch`
- **Vivado:** Sets `set_load`; DONT_TOUCH and IOSTANDARD available as comments
- **Quartus:** Sets `set_load`; PRESERVE_REGISTER available as comments

See `rtl/syn/char_top.sdc` for the complete constraint file and
`rtl/syn/SYNTHESIS_GUIDE.md` for detailed per-flow setup instructions.
