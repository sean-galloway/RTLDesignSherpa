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

# Lint and Synthesis Checks

Every generated bridge is expected to pass Verilator lint and out-of-context synthesis.

## Verilator lint

The `rtl/Makefile` runs lint:

```bash
cd projects/components/fabric-gen-ip/bridge/rtl
make verilator
```

This lints every generated fixture using its filelist. The generator aims for lint-clean output; any new warning class must be either fixed in the generator or documented with a scoped waiver.

## Out-of-context synthesis

The FPGA flow in `projects/components/fabric-gen-ip/bridge/fpga/` supports out-of-context synthesis:

```bash
cd projects/components/fabric-gen-ip/bridge/fpga
make synth BRIDGE=bridge_2x2_rw PART=xc7a100tcsg324-1 CLK_NS=10
```

Resource and timing tables in the HAS/MAS are produced by this flow.

## When to run checks

Run lint and at least one synthesis check after:

- Adding a new protocol or option.
- Changing the adapter or crossbar emission templates.
- Updating converter/wrapper dependencies.

A generator change that passes simulation but fails synthesis is not done.
