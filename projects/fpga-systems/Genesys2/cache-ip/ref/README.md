# cache-ip reference rig (Genesys 2)

The jet pair harness with ONE cache in the slot and no coherence fabric, so
the OpenHW HPDcache (`REF_CACHE_SEL=0`), the CVA6 write-back dcache
(`REF_CACHE_SEL=1`) and the house jet-prime straight onto memory
(`REF_CACHE_SEL=2`, jet-prime TASK-001 step 1: jet's RTL without the pair
fabric, snoop port tied off) can be measured behind the same pipelined cycle
injector, memory, UART stack and clock as amber and jet. Work item: cache-ip common-ip TASK-003
(`vault/tracking/projects/components/cache-ip/common-ip/task/`); results and
every place the comparison is not like-for-like:
`projects/components/cache-ip/docs/reference_l1_comparison.md`.

- `rtl/` -- `ref_harness.sv`, `ref_genesys2_top.sv` (clones of the jet rig
  minus coherence), the two wrappers `ref_hpdcache_top.sv` /
  `ref_cva6_dcache_top.sv`, the block-RAM SRAM stand-ins the vendored caches
  need on Vivado, `ref_null_cache.sv`, `ref_axil_stub.sv`.
- `dv/tests/` -- `make clean-all && make run-all-gate-parallel`.
- `build-bringup/` -- `make bitstream smoke REF_CACHE_SEL=0|1|2`; `make ooc
  CACHE=hpd|cva6|jet|jetp|amber` for the cache-only area row.
- `bin/ref_compare.py` -- the comparison tables from the sweep JSONs.
- Host stack: the jet rig's (`../jet/host`, `../jet/bin`); same bridge map.
- Vendored sources: `vendor/cv-hpdcache`, `vendor/cva6-dcache` (PROVENANCE.md
  in each).
