# PROVENANCE -- vendor/cv-hpdcache

Vendored subset of the CEA / OpenHW Group High-Performance L1 Dcache
(HPDcache): the cache itself and what it instantiates, used as the
non-blocking reference L1 of the cache-ip comparison (cache-ip common-ip
TASK-003, rig `projects/fpga-systems/Genesys2/cache-ip/ref`).

- **Upstream:** https://github.com/openhwgroup/cv-hpdcache
- **Version:** master, commit `40d2897eda70644df2eb857efd9fa573eaacafab`
  (2026-11-05, "fix: add missing comma in the port list of the blackbox
  hpdcache_sram_wbyteenable_ecc_1rw")
- **Vendored:** 2026-11-11
- **License:** Apache-2.0 WITH SHL-2.1 (see `LICENSE`)
- **Kept:** `rtl/include/hpdcache_typedef.svh`; every `rtl/src/**/*.sv`
  named by upstream `rtl/hpdcache.Flist` (the package, `common/`,
  `hwpf_stride/`, the cache modules, the two `utils/` memory arbiters);
  the three behavioural SRAM macros `rtl/src/common/macros/behav/
  hpdcache_sram_{,wbyteenable_,wmask_}1rw.sv` (reference only: Vivado maps
  their two-dimensional entries to registers, so the consumer supplies
  block-RAM `hpdcache_sram_1rw` and `hpdcache_sram_wbyteenable_1rw` in
  `projects/fpga-systems/Genesys2/cache-ip/ref/rtl/`; the blackbox and ECC
  variants are not used); the memory-to-AXI
  adapters `rtl/src/utils/hpdcache_mem_to_axi_{read,write}.sv` (they import
  the PULP `axi_pkg`, taken from `vendor/pulp-axi`); the Verilator waiver
  file `rtl/src/hpdcache.vlt`; upstream `README.md`, `LICENSE`.
- **Dropped:** `rtl/tb`, `rtl/fv`, `rtl/lint`, `rtl/syn`, `rtl/src/target`
  (the CVA6 wrapper), the ECC SRAM macros and `utils/ecc`, the L1.5 /
  OpenPiton adapters, `docs`, CI, and upstream's `README.md` (its relative
  links point into the dropped tree; the repo's link checker would count
  them broken).
- **Local edits:** none. The configuration (sets, ways, line, MSHR, write
  buffer, write-back) is set by the consumer (`ref_hpdcache_top.sv`), not
  by editing upstream.

## Update procedure

```bash
rm -rf /tmp/hpd-up && git clone https://github.com/openhwgroup/cv-hpdcache /tmp/hpd-up && git -C /tmp/hpd-up checkout <commit>
H=/tmp/hpd-up; D=vendor/cv-hpdcache
cp $H/LICENSE $D/; cp $H/rtl/include/hpdcache_typedef.svh $D/rtl/include/
for f in $(grep -oE '\$\{HPDCACHE_DIR\}/rtl/src/[^ ]+\.sv' $H/rtl/hpdcache.Flist | sed 's#${HPDCACHE_DIR}/##'); do cp $H/$f $D/$f; done
cp $H/rtl/src/common/macros/behav/hpdcache_sram_{,wbyteenable_,wmask_}1rw.sv $D/rtl/src/common/macros/behav/
cp $H/rtl/src/utils/hpdcache_mem_to_axi_{read,write}.sv $D/rtl/src/utils/
# Regenerate the module list in vendor/filelists/cv_hpdcache.f from the new
# Flist, bump the lines above, then lint the ref rig top and re-run its gate.
```
