---
title: Static loop bounds
summary: A for-loop bounded by a runtime value simulates and lints clean, and Vivado refuses it.
---

# Static loop bounds

A `for` loop in RTL is unrolled at elaboration, so its bounds must be
constants. If the bound or start value is a signal or a function argument
fed by one (`for (j = winner + 1; j < N; j++)`), Verilator and the
simulators run it happily: they execute the loop as software. Vivado has to
unroll it and cannot, and stops with `[Synth 8-3380] loop condition does
not converge after 2000 iterations`.

Write the loop over the full static range and let the runtime value select
what changes:

```systemverilog
for (int r = 0; r < CLIENTS; r++)
    for (int c = r + 1; c < CLIENTS; c++)
        if (r == winner)      nxt[idx(r, c)] = 1'b0;
        else if (c == winner) nxt[idx(r, c)] = 1'b1;
```

The behavior is the same and the hardware is what the loop always meant: a
compare per position.

*Case (2026-10-18): `rtl/common/arbiter_matrix.sv` and
`arbiter_matrix_weighted.sv` had passed their FULL cocotb suites and lint
for a week. They had never been through synthesis. The first block to
instantiate one in an FPGA build (the bridge's `bridge_cdc_slave_arb`)
failed in Vivado on `matrix_update`'s winner-bounded loops. Fixed as above;
both suites still pass, 18/18.*

The general rule this is one instance of: a module is not done until it has
been through the synthesis tool it will meet. Lint and simulation are not
that tool. See [[area-measure-by-hierarchy]] for the synthesis pass every
block should get.
