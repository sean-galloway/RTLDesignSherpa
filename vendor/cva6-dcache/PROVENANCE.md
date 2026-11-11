# PROVENANCE -- vendor/cva6-dcache

Vendored subset of the OpenHW Group CVA6 core: its write-back data cache
(`std_nbdcache`, the "blocking" L1 the HPDcache is measured against) and the
packages and cells it elaborates with, used as the blocking reference L1 of
the cache-ip comparison (cache-ip common-ip TASK-003, rig
`projects/fpga-systems/Genesys2/cache-ip/ref`).

- **Upstream:** https://github.com/openhwgroup/cva6
- **Version:** master, commit `742dc82a0c706e0a3bfb98b709fd3ee06d50d12a`
  (2026-10-23, "Note: master made read-only. (#3664)")
- **Vendored:** 2026-11-11
- **License:** Solderpad Hardware License 0.51 (see `LICENSE`)
- **Kept:** `core/include/{config_pkg,riscv_pkg,ariane_pkg,std_cache_pkg,
  build_config_pkg,cv64a6_imafdc_sv39_wb_config_pkg}.sv` (the last one is
  the write-back configuration the reference derives its own from, kept for
  reference; the rig's package is `ref_cva6_cfg_pkg.sv` beside the wrapper);
  `core/cache_subsystem/{std_nbdcache,cache_ctrl,miss_handler,tag_cmp,
  amo_alu,axi_adapter}.sv`; `common/local/util/{sram,tc_sram_wrapper}.sv`;
  upstream `README.md`, `LICENSE`.
- **Dropped:** the core, the write-through and HPDcache subsystems, the
  I-cache, every other package, `corev_apu`, verification, docs, and
  upstream's `README.md` (its relative links point into the dropped tree).
- **Not vendored, supplied by the consumer:** `tc_sram` (pulp-platform
  tech_cells_generic, a git submodule upstream) and the `tc_sram_wrapper`
  around it: the rig's `projects/fpga-systems/Genesys2/cache-ip/ref/rtl/
  tc_sram.sv` and `tc_sram_wrapper.sv` are a behavioural byte-enabled
  single-cycle memory and a plain-vector wrapper with the same parameters
  and ports.
  `lfsr_8bit` and `cf_math_pkg` come from `vendor/pulp-common_cells`, the
  `axi_pkg` that `axi_adapter` imports from `vendor/pulp-axi`.
- **Local edits:** none.

## Update procedure

```bash
rm -rf /tmp/cva6-up && git clone --filter=blob:none https://github.com/openhwgroup/cva6 /tmp/cva6-up && git -C /tmp/cva6-up checkout <commit>
V=/tmp/cva6-up; D=vendor/cva6-dcache
cp $V/LICENSE $D/
for f in config_pkg riscv_pkg ariane_pkg std_cache_pkg build_config_pkg cv64a6_imafdc_sv39_wb_config_pkg; do cp $V/core/include/$f.sv $D/core/include/; done
for f in std_nbdcache cache_ctrl miss_handler tag_cmp amo_alu axi_adapter; do cp $V/core/cache_subsystem/$f.sv $D/core/cache_subsystem/; done
cp $V/common/local/util/{sram,tc_sram_wrapper}.sv $D/common/local/util/
# Diff cv64a6_imafdc_sv39_wb_config_pkg against ref_cva6_cfg_pkg.sv for new
# cva6_user_cfg_t fields, bump the lines above, lint the ref rig top and
# re-run its gate.
```
