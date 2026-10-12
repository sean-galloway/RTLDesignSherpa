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

As of 2026-10-12, Delta has one cocotb suite in `dv/tests/`. It covers the `--amba5` flavor through the checked-in example `rtl_test/delta_axis_flat_2x4_strb_amba5.sv` (2x4, 32-bit, `TSTRB`), using a thin flattening harness (`dv/tb/delta_axis_flat_2x4_strb_amba5_th.sv`) and RDS-DV AXIS5 BFMs on every port:

- **routing:** every master sends to every slave at once. Each slave must receive exactly its beats, every beat must pass the slave BFM's odd-parity check, the crossbar-driven `TVALIDCHK`/`TWAKEUPCHK`/`TREADYCHK` must equal the inversion of their signals on every cycle, and no error flag may set. At func and full the BFMs add random VALID gaps and READY stalls.
- **wakeup:** `TWAKEUP` with no `TVALID` reaches only the `TDEST` slave, with `TWAKEUPCHK` inverted.
- **chk_errors:** a bad `TDATACHK`, a bad `TVALIDCHK` and a bad `TREADYCHK` each set the right sticky flag and no other. Reset clears it.

Run it with `make clean-all && make run-all-func-parallel` in `dv/tests/`. The base flavor (`rtl/delta_axis_flat_4x16.sv` and the plain `rtl_test/` shapes) still has no simulation suite. It is verified by lint and review only.

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

Still to add:

- All master-to-slave routing combinations.
- Concurrent traffic to the same slave (round-robin fairness).
- Concurrent traffic to different slaves (no crosstalk).
- Backpressure stress tests.
- Packet atomicity verification (no interleaving before `TLAST`).
- Base-flavor equivalents of the `--amba5` suite (the AMBA 5 check signals are covered today).
- Reset behavior.

## Formal Properties

When `FORMAL` is defined, the generated RTL includes:

- One-hot grant assertion per slave.
- TDEST range assertion per master.

These can be exercised with a SystemVerilog formal tool.
