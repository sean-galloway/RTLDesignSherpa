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

# DV Suite

The component-level DV suite lives in `dv/tests/` and uses cocotb.

## Test list

| Test | Focus |
|------|-------|
| `test_apbx_xbar_1to1.py` | Passthrough behavior. |
| `test_apbx_xbar_2to1.py` | Two masters contend for one slave. |
| `test_apbx_xbar_1to4.py` | Single master accesses multiple slaves by address. |
| `test_apbx_xbar_2to4.py` | Full decode + arbitration stress. |
| `test_apbx_xbar_2to2_mixed.py` | APB4/APB5 sideband conversion. |
| `test_apbx_xbar_timing.py` | PREADY backpressure and timing. |

## Running the suite

```bash
cd projects/components/fabric-gen-ip/lattice-apbx-xbar/dv/tests
make clean-all && make run-all-gate
```

The `run-all-gate` target exercises every standard fixture through the gate-level-style regression flow. After a generator change, this must pass with zero failures before the regenerated RTL is committed.

## Adding a new test

1. Add a new `test_apbx_xbar_<variant>.py` file in `dv/tests/`.
2. Reference the matching generated module in the test's `Makefile` or parameter list.
3. Add the test name to the area regression list (component `Makefile` or `tests.mk`).
