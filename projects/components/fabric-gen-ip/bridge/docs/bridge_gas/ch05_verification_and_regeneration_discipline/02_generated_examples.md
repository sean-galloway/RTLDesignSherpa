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

# Generated Examples

The checked-in `rtl/generated/` directory contains a variety of fixtures that serve as regression anchors and integration examples.

## Representative fixtures

| Fixture | Masters | Slaves | Notable features |
|---------|---------|--------|------------------|
| `bridge_2x2_rw` | 2 | 2 | Plain AXI4, 32-bit addresses, per-port widths. |
| `bridge_2x2_axi5` | 2 | 2 | Native AXI5 fabric with MTE/chunking. |
| `bridge_1x2_rw_apb5` | 1 | 2 | APB5 slave, single master. |
| `bridge_2x2_axi3_masters` | 2 | 2 | AXI3 masters on AXI4 fabric. |
| `bridge_mix_e` | 3 | 3 | AXI3 + AXI4 + APB masters → AXI3 + AXI4 + APB slaves. |
| `bridge_1x2_rd_regblock_mon` | 1 | 2 | `use_cfg_regblock=true`, `"mon"` variant. |
| `bridge_2x2_rw_qos_pipe` | 2 | 2 | `arbitration="qos"`, `xbar_pipeline=true`. |

## How to verify a regeneration

After `make all`, every fixture in `rtl/generated/` should be byte-identical to the checked-in version **if** the generator and inputs have not changed. Because the generated files carry a generation-date-free header, a clean regeneration should not introduce spurious diffs.

To compare:

```bash
cd projects/components/fabric-gen-ip/bridge
# Regenerate everything
make -C bin clean && make -C bin all
# Check for unexpected diffs
git diff -- rtl/generated/ | head -n 200
```

(Note: the user instruction forbids running git commands; the command above is for illustration only and is the responsibility of the agent that owns the shared tree.)

If the generator code changed intentionally, the diffs are expected and must be reviewed.

## Fixture as documentation

The `bridge_mix_e` fixture is the canonical mixed-protocol example. Its TOML and generated top module are referenced throughout this specification. To understand how a new protocol or width combination is emitted, generate a minimal fixture and compare it to the closest existing one.
