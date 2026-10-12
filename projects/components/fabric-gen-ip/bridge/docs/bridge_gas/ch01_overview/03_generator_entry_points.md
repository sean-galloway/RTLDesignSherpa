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

# Generator Entry Points

Bridge has two invocation modes: single-bridge and bulk.

## Single-Bridge Mode

```bash
cd projects/components/fabric-gen-ip/bridge/bin
python3 bridge_generator.py \
    --ports test_configs/bridge_2x2_rw.toml \
    [--connectivity test_configs/bridge_2x2_rw_connectivity.csv] \
    [--name bridge_2x2_rw] \
    [--output-dir ../rtl/generated]
```

For TOML inputs, `--connectivity` is optional: the loader auto-detects `<bridge_name>_connectivity.csv` next to the TOML file. CSV port files are no longer supported.

CLI flags:

| Flag | Default | Purpose |
|------|---------|---------|
| `--ports` | required | Path to the TOML port configuration |
| `--connectivity` | auto | Path to the CSV connectivity matrix |
| `--name` | from TOML or auto | Output module base name |
| `--output-dir` | `../rtl/generated` | Where to write the bridge directory |
| `--generate-tests` | off | Also emit cocotb TB class and test runner |
| `--output-tb` | `../dv/tbclasses` | TB class output directory |
| `--output-test` | `../dv/tests` | Test runner output directory |

## Bulk Mode

```bash
python3 bridge_generator.py --bulk bridge_batch.csv
```

The batch CSV columns are:

```csv
name,ports,connectivity,output_dir,output_tb,output_test
```

Comment lines starting with `#` are ignored. The `name` and `connectivity` fields may be empty; empty connectivity triggers auto-detection from the TOML filename.

## Makefile Targets

The `bin/Makefile` wraps the bulk path:

| Target | Action |
|--------|--------|
| `make all` | `bridge_generator.py --bulk bridge_batch.csv` |
| `make clean` | remove `rtl/generated/` and `rtl/filelists/` |
| `make regen` | alias for `make clean && make all` |

## Return Value

`generate_bridge()` returns a tuple `(success: bool, emitted_variants: list[tuple[str, bool]])`. A non-empty `emitted_variants` list means at least one variant was written. The bulk driver exits non-zero if any bridge or test generation fails.
