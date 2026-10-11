# Formal verification for `arbiter_matrix_weighted`

**Status: pending.**

A formal wrapper (`formal_arbiter_matrix_weighted.sv`) is provided, but the local Yosys
installation does not include Verific support, and the module's SystemVerilog
constructs (`function automatic`, packed array indexing in the matrix helper
functions) are not accepted by Yosys's native Verilog frontend:

```
arbiter_matrix_weighted.sv:NNN: ERROR: syntax error, unexpected '-', expecting ';'
```

The wrapper targets the same no-ACK safety properties used for
`arbiter_matrix` and `arbiter_round_robin`:

- grant is one-hot when `grant_valid` is asserted
- grant is only issued to a requesting client
- `grant_id` matches the one-hot grant bit and is in range
- `last_grant` is the previous cycle's grant
- reset clears all outputs

To run the proof when a Yosys+Verific build is available:

```bash
cd formal/common/arbiter_matrix_weighted
sby arbiter_matrix_weighted.sby
```

An example `arbiter_matrix_weighted.sby` that uses Verific:

```ini
[tasks]
prove
cover

[options]
prove: mode bmc
prove: depth 25
cover: mode cover
cover: depth 50

[engines]
prove: smtbmc z3
cover: smtbmc z3

[script]
verific -sv arbiter_matrix_weighted.sv
verific -sv formal_arbiter_matrix_weighted.sv
prep -top formal_arbiter_matrix_weighted

[files]
arbiter_matrix_weighted.sv ../../../rtl/common/arbiter_matrix_weighted.sv
formal_arbiter_matrix_weighted.sv
includes/reset_defs.svh ../../../rtl/amba/includes/reset_defs.svh
```

A separate `arbiter_matrix_weighted_c1.sby` should override `CLIENTS` to 1 to
exercise the `gen_single_client` degenerate branch.
