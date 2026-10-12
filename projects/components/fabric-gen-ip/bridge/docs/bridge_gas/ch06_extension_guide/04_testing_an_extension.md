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

# Testing an Extension

Any generator extension must be proven by regeneration, lint, and DV.

## Minimum test plan

1. **Single-bridge generation**

   ```bash
   python bridge_generator.py --ports test_configs/my_extension.toml
   ```

   Verify the output directory contains the expected files and that the new logic appears in the generated `.sv`.

2. **Validation failure paths**

   Create deliberately invalid TOML files and confirm the generator raises `ValidationError` with a clear message.

3. **Bulk regeneration**

   ```bash
   make clean && make all
   ```

   Confirm no fixture regresses.

4. **Lint**

   ```bash
   cd ../rtl && make verilator
   ```

5. **DV smoke**

   ```bash
   cd ../dv/tests
   make clean-all && make run-<fixture>-func
   ```

6. **Synthesis sanity**

   For area-sensitive options, run out-of-context synthesis on the smallest fixture that exercises the option.

## Regression fixtures

Add at least one fixture to `bridge_batch.csv` that exercises the new protocol or option. If the option is off by default, also add a fixture with the option enabled.

## Documentation

Update this GAS and `CLAUDE.md` if the extension changes the way users configure or extend the generator. Keep the validator rule list, the configuration tables, and the extension-guide steps in sync.
