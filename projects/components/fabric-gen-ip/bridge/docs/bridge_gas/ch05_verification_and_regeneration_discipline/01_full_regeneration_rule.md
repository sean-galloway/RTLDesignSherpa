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

# Full Regeneration Rule

Generated RTL must be treated like compiler output: when the compiler changes, rebuild everything.

## Why partial regeneration is dangerous

- The package file defines widths used by every other generated file.
- Converter selection logic affects adapter port lists and the filelist.
- The `bridge_id` width is global; a change changes the crossbar and every adapter.
- The filelist pulls in external IP closures; an interface change there must be reflected in every generated bridge.

## Required workflow

```bash
cd projects/components/fabric-gen-ip/bridge/bin
make clean
make all
```

If tests are generated:

```bash
python bridge_generator.py --bulk bridge_batch.csv --generate-tests
cd ../dv/tests
make clean-all && make run-all-func
```

## Code changes that trigger full regeneration

- `bin/bridge_generator.py`
- Any file under `bin/bridge_pkg/`
- Any Jinja template under `bin/bridge_pkg/jinja_templates/`
- Any shared converter/wrapper IP whose interface changed

## Files that are never regenerated

- `rtl/bridge_wr_rate_buf.sv` — hand-written rate-matching buffer on upsized paths into shared slaves.
- `rtl/bridge_id_remap.sv` — hand-written transaction-ID remap table in the master adapters (bridge TASK-018).
- `deprecated/` — code no flow uses (`bridge_cam.sv` and its test and proof, the analytical model), kept out of every regression.
- Anything outside `rtl/generated/` and `rtl/filelists/`.

## Version-mismatch symptoms

- Tests that previously passed now fail.
- Simulation errors about missing signals or mismatched widths.
- Address decode routing to wrong slaves.
- Verilator warnings about undeclared identifiers in the package.

If any of these appear after a generator change, the first recovery step is `make clean && make all`.
