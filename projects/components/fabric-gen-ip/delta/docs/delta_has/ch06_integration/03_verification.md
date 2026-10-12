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

# Verification Strategy

## Current Status

As of 2026-10-12, **there is no `dv/` test suite for Delta**. The generator output is verified by linting (Verilator) and by visual/code review. A cocotb-based testbench is the known TODO.

## Generator Verification

- Run `bin/delta_generator.py` for several configurations.
- Compare output against checked-in reference RTL (`rtl/delta_axis_flat_4x16.sv`, `rtl_test/delta_axis_flat_*.sv`).
- Verify that default output is byte-identical to pre-2026-10-12 generations.

## Lint Verification

```bash
verilator --lint-only rtl/delta_axis_flat_4x16.sv
```

Or use the provided `rtl/Makefile`:

```bash
cd rtl && make verilator
```

## Planned RTL Verification

When a cocotb testbench is added, the recommended coverage includes:

- All master-to-slave routing combinations.
- Concurrent traffic to the same slave (round-robin fairness).
- Concurrent traffic to different slaves (no crosstalk).
- Backpressure stress tests.
- Packet atomicity verification (no interleaving before `TLAST`).
- Rich-flavor tests (`TSTRB`, `TWAKEUP`, `TPARITY`).
- Reset behavior.

## Formal Properties

When `FORMAL` is defined, the generated RTL includes:

- One-hot grant assertion per slave.
- TDEST range assertion per master.

These can be exercised with a SystemVerilog formal tool.
