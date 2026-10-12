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

Every generator change must be exercised by at least one generated fixture and one DV test.

## Minimal test plan

1. **Generator unit test** — call `DeltaFlatCrossbar(cfg).verilog()` with the new option and verify the emitted string contains the expected constructs.
2. **Fixture regeneration** — generate the affected fixtures and inspect the diff.
3. **Simulation test** — add or extend a cocotb test that exercises the new behavior.
4. **Lint/synthesis smoke** — run the lint flow on the affected variant.

## Example: adding a custom variant test

```python
# dv/tests/test_delta_flat_4x4.py
import cocotb

class TestDeltaFlat4x4:
    @cocotb.test()
    async def test_basic_routing(self, dut):
        # exercise all 4 masters against all 4 slaves
```

The test must be added to the `run-all-gate` target or an equivalent regression list.

## Commit discipline

Commit generator source changes, regenerated RTL, and DV tests in a single logical change. Do not commit hand-edited generated files.
