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

# Generated Tests

When `--generate-tests` is passed, the generator emits a cocotb testbench class and a pytest runner for each variant.

## TB class

The TB class is written to `dv/tbclasses/<tb_class_module>.py`. Its name is derived from the bridge name:

```python
bridge_2x2_rw  → Bridge2x2RwTB
bridge_mix_e   → BridgeMixETB
```

The class inherits from `TBBase` and implements:

- `setup_clocks_and_reset()` — drives `aclk` and `aresetn`.
- `assert_reset()` — drives `self.dut.aresetn.value = 0`.
- `deassert_reset()` — releases reset.

It constructs `GAXIMaster` / `GAXISlave` BFMs per port using the AXI4 field configs derived from the generated widths.

## Test runner

The test runner (`dv/tests/test_<bridge>.py`) contains `cocotb.test` functions and pytest wrappers. Each wrapper names its `testcase=` explicitly. Example shape:

```python
@cocotb.test()
async def basic_read_write(dut):
    tb = Bridge2x2RwTB(dut)
    await tb.run_basic_read_write()

@pytest.mark.parametrize("seed", [0, 1, 2])
def test_bridge_2x2_rw_basic(seed):
    run_test(
        module="test_bridge_2x2_rw",
        testcase="basic_read_write",
        extra_env={"SEED": str(seed)}
    )
```

## Monitor stress test

For `"mon"` variants, `generate_monitor_tests()` emits:

- A TB class with the full monbus/cfg surface.
- `test_<bridge>_monitor.py` driving backpressure and error injection phases scaled by `TEST_LEVEL`.

## Regeneration discipline for tests

Tests are generated artifacts. After any change to the test templates or to widths that affect BFM construction, regenerate tests with `--generate-tests` from a clean state. Hand-written tests for generated DUTs should live in separate files (for example, `test_bridge_2x2_rw_tracking.py`) and not be overwritten by the generator.
