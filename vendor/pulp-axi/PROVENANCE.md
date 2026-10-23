# PROVENANCE — vendor/pulp-axi

Vendored subset of the PULP platform AXI library: `axi_xbar` and what it
instantiates, used as leg C2 of the Genesys 2 fabric benchmark
(`projects/fpga-systems/Genesys2/fabric-benchmark`). It depends on
`vendor/pulp-common_cells` (see its PROVENANCE.md).

- **Upstream:** https://github.com/pulp-platform/axi
- **Version:** v0.39.11 (git tag `v0.39.11`, commit
  `42ca270ebd8bbbc1c64ddc0ca712e722eb9e3f06`, 2026-09-08)
- **Vendored:** 2026-10-23
- **License:** Solderpad Hardware License 0.51 (see `LICENSE`; permissive,
  Apache-2.0 based)
- **Kept:** `include/axi/{typedef,assign,port}.svh`; `src/axi_pkg.sv`,
  `axi_intf.sv` (its `AXI_BUS` interface is named by `axi_xbar_intf` in
  `axi_xbar.sv`), `axi_xbar.sv`, `axi_xbar_unmuxed.sv`, `axi_demux.sv`,
  `axi_demux_simple.sv`, `axi_demux_id_counters.sv`, `axi_mux.sv`,
  `axi_id_prepend.sv`, `axi_err_slv.sv`, `axi_atop_filter.sv`,
  `axi_multicut.sv`, `axi_cut.sv`; upstream `README.md`, `Bender.yml`
  (dependency pins), `LICENSE`. The set is the closure Verilator elaborates
  for `axi_xbar`, plus `axi_atop_filter` and `axi_cut`, which sit behind
  generate branches (ATOPs, PipelineStages) the benchmark does not take.
- **Dropped:** every other module, `test/`, `doc/`, `scripts/`
- **Local edits:** none

## Update procedure

```bash
rm -rf /tmp/pulp-axi-up && git clone --branch <tag> https://github.com/pulp-platform/axi /tmp/pulp-axi-up
cd vendor/pulp-axi
cp /tmp/pulp-axi-up/{LICENSE,README.md,Bender.yml} .
cp /tmp/pulp-axi-up/include/axi/{typedef,assign,port}.svh include/axi/
for f in src/*.sv; do cp /tmp/pulp-axi-up/$f src/; done
# Bender.yml names the common_cells version this tag needs: update
# vendor/pulp-common_cells to it. Then add any module a new version
# instantiates (verilator --lint-only reports it), bump the lines above, and
# run fabric-benchmark make sim and make ooc LEG=pulp.
```
