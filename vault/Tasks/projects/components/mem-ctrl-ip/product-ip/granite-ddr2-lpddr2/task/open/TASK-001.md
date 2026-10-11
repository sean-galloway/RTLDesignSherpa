---
title: TASK-001 — granite first build (wrapper dissolution + product top)
summary: Dissolve the pumice layer wrappers into the common-ip layer macros, then compose the granite product top from common-ip only.
---

# TASK-001 — granite first build (wrapper dissolution + product top)

**State:** open · **Area:** product-ip/granite-ddr2-lpddr2 · **Opened:** 2026-10-11

## Why

Granite's configuration is scaffolded (`config/product_config.md`,
`rtl/includes/granite_pkg.sv`, `rtl/filelists/top/granite.f`). The product
top module (`granite_core`) is deliberately not written yet: composing it
today would require instantiating the `pumice_scheduler_layer` /
`pumice_training_layer` wrappers, re-introducing a product → research-ip
dependency the 2026-10-11 migration eliminated.

All wrapper children are now common (`mc_xddr2_init_sequencer`,
`mc_xddr2_mode_register`, `mc_xddr2_refresh_ctrl`, `mc_page_policy`,
`mc_cmd_history_checker`, `mc_lpddr2_zq_ctrl`, `mc_lpddr2_dq_cal`), so the
wrappers no longer own anything pumice-specific. The composition belongs in
the common layer macros.

## Work

1. **Dissolve the wrappers (common-ip):** move the child instantiation +
   wiring from `research-ip/pumice-ddr2-lpddr2/rtl/macro/pumice_scheduler_layer.sv`
   into `common-ip/rtl/macro/mc_scheduler_layer.sv` (parameters/generates
   select children; default = the v2 set), and likewise
   `pumice_training_layer` → `mc_training_layer` (LPDDR2 clients via
   parameter). Delete the two wrapper files; re-point `pumice_core` to the
   common macros directly. Verify pumice lint + fub tests unchanged.
2. **Compose the granite top:** `rtl/top/granite_core.sv` instantiating the
   common layers per `granite.f`, with `granite_pkg` parameters (lite
   storage N=1, SKU write-data staging, no RAS layer).
3. **Product CSR baseline:** narrow the pumice PeakRDL surface (no RAS
   decode beyond reserved, no research-harness knobs) into
   `regs/granite_csr.rdl`; generate.
4. **Board:** pick the product board; commit constraints + PHY part; set
   the frequency plan (timer CSRs derive from it — frequency change
   invalidates the whole set).

## Acceptance

- `granite.f` elaborates a lint-clean `granite_core` with zero
  research-ip filelist references (registry audit proves it).
- pumice lint + registry green after wrapper dissolution.
- Product config values that were TBD are either committed or carry an
  explicit bring-up owner.
