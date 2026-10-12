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

# Filelist

The filelist (`<bridge_name>.f`) declares the complete compile closure for one variant. It is generated in `bridge_generator.py` by `_emit_bridge_variant()`.

## Path convention

All paths inside the filelist are anchored to `$REPO_ROOT`. This allows the filelist to be included from another filelist regardless of the including file's base directory.

## Example filelist head

```text
# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Reset macro header (`ALWAYS_FF_RST / `RST_ASSERTED)
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Monitor packages (must precede any module that references them)
-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f

# Subtractive catch-all slave (unmapped-address terminator)
-f $REPO_ROOT/rtl/amba/filelists/axi4_subtractive_slave.f

# Bridge RTL files (generated)
$REPO_ROOT/projects/components/fabric-gen-ip/bridge/rtl/generated/bridge_mix_e/bridge_mix_e_pkg.sv
$REPO_ROOT/projects/components/fabric-gen-ip/bridge/rtl/generated/bridge_mix_e/bridge_mix_e_xbar.sv
$REPO_ROOT/projects/components/fabric-gen-ip/bridge/rtl/generated/bridge_mix_e/bridge_mix_e.sv
$REPO_ROOT/projects/components/fabric-gen-ip/bridge/rtl/generated/bridge_mix_e/apb_periph_adapter.sv
...

# AXI4 Wrapper modules (timing isolation)
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_wr.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_rd.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_wr.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_rd.f

# Width converters
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/axi_data_upsize.f
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/axi_data_dnsize.f
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/axi4_dwidth_converter_rd.f
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/axi4_dwidth_converter_wr.f
```

## Filelist is generated, not hand-maintained

Because the converter and wrapper selections depend on the port protocols, the filelist is regenerated every time the bridge is regenerated. Do not hand-edit a generated filelist; instead, change the generator's selection logic and regenerate.
