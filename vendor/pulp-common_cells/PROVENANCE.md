# PROVENANCE — vendor/pulp-common_cells

Vendored subset of the PULP platform common cells: the ones `axi_xbar`
(`vendor/pulp-axi`) instantiates.

- **Upstream:** https://github.com/pulp-platform/common_cells
- **Version:** 1.39.0 (git tag `v1.39.0`, commit
  `9ca8a7655f741e7dd5736669a20a301325194c28`, 2025-11-20). This is the
  version `vendor/pulp-axi/Bender.yml` (axi v0.39.11) requires. Newer
  common_cells (the v2 line) renames every module with a `cc_` prefix.
- **Vendored:** 2026-10-23
- **License:** Solderpad Hardware License 0.51 (see `LICENSE`)
- **Kept:** `include/common_cells/{registers,assertions}.svh`;
  `src/cf_math_pkg.sv`, `addr_decode.sv`, `addr_decode_dync.sv`,
  `counter.sv`, `delta_counter.sv`, `fifo_v3.sv`, `lzc.sv`,
  `rr_arb_tree.sv`, `spill_register.sv`, `spill_register_flushable.sv`;
  upstream `README.md`, `Bender.yml`, `LICENSE`
- **Dropped:** every other cell, `test/`, `formal/`, `scripts/`
- **Local edits:** none

## Update procedure

```bash
rm -rf /tmp/pulp-cc-up && git clone --branch <tag> https://github.com/pulp-platform/common_cells /tmp/pulp-cc-up
cd vendor/pulp-common_cells
cp /tmp/pulp-cc-up/{LICENSE,README.md,Bender.yml} .
cp /tmp/pulp-cc-up/include/common_cells/{registers,assertions}.svh include/common_cells/
for f in src/*.sv; do cp /tmp/pulp-cc-up/$f src/; done
# bump the lines above; the tag must be the one vendor/pulp-axi/Bender.yml names
```
