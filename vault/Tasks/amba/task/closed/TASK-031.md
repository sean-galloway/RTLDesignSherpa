# TASK-031: REORG — pull CDC out of amba into a top-level rtl/cdc area

> Migrated 2026-09-27 from `vault/Tasks/amba/closed.md` as **AMBA-CDC** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** DONE 2026-07-25 — every checklist item worked and verified.
Move this block to closed.md.

**Completed 2026-07-25** (commits `dc922a54`, `cd2a2dc3`, `8b2de284`):

- [x] `bin/filelists.toml`: `cdc` area registered. `--check` reports cdc 12
      modules / 12 covered / 0 uncovered, no exemptions needed.
- [x] `.f` for `gaxi_skid_buffer_async` created (it was the one module of twelve
      without one).
- [x] `bin/filelist_registry.py --check` PASS **and `--audit` PASS**. Registering
      the area exposed 27 cross-area hand-listed sources — all pre-existing but
      invisible, since they were intra-area before the move. All 27 converted to
      `-f` includes. Verified behaviour-preserving: `fifo_async.f` resolves to
      the same 14 sources in the same order.
- [x] Moved-module tests run: `val/cdc` 62 passed after `clean-all`;
      `val/amba/test_apb5_slave_cdc` 3 passed; `test_gaxi_buffer_async` 12 passed.
- [x] `val/cdc/` exists — 11 tests git-moved from val/common (7) and val/amba (4),
      plus a four-line Makefile and a conftest that DERIVES its area name rather
      than typing it.
- [x] `docs/markdown/rtl-cdc/` — 8 module pages + cdc.md moved in, with `index.md`,
      `overview.md` and `_book_cdc_index.md`. Casing settled on **rtl-cdc**; the
      empty lowercase `RTLcdc/` is gone. 14 referring pages repathed, 0 broken
      links to any moved page.
- [x] `formal/` — 10 harnesses moved to `formal/cdc/`, 13 files repathed.
- [x] Kimi findings referencing old paths: handled during the round_2 integration
      (the bundle was rebuilt post-move, so `common_meta` flagged the relocation
      itself rather than producing stale-path findings).

**Two things this surfaced that were NOT part of the move:**

1. `test_fifo_async_wavedrom` hand-listed eight `rtl/common` source paths instead
   of taking a filelist, so it had been broken since `c0daf18a` — the one test
   the original path rewrite missed, unnoticed because val/common's suite had not
   been run since. Now takes `rtl/cdc/filelists/fifo_async.f`.
2. The four `apb*_slave_cdc` formal harnesses referenced `cdc_handshake.sv`,
   which exists nowhere and which neither slave instantiates — and they were
   also missing `gaxi_fifo_async` and its whole dependency tree, which the
   slaves DO instantiate. **Fixed 2026-07-25 (`6eab2377`):** each harness's
   `[script]`/`[files]` are now GENERATED from the area's audited filelist, so
   they cannot drift from the closure the cocotb tests compile. 14/17/17/21
   sources, up from 3/4/4/5; all 77 refs resolve and each set elaborates under
   Verilator. The proofs themselves are still unrun — `sby`/`yosys` are not
   installed on this box.

3. Two more stranded tests, same defect as (1): `test_counter_bingray_wavedrom`
   and `test_counter_johnson_wavedrom` sat in val/common hand-listing
   `rtl/common/<dut>.sv`, broken since the move. Confirmed RED, moved to
   val/cdc, put on their filelists. They were missed initially because the move
   swept tests referencing a cdc FILELIST; these referenced a PATH.

**Not blocking, noted:** 387 unresolvable source refs remain in `formal/common/`
`.sby` files, all `math_*` fallout from the earlier arithmetic split. Untouched
here; they want their own task. *(They got one: paths mechanically repaired
2026-08-09, 5 modules spot-verified prove+cover PASS; the full re-run is
MATH-006 in vault/Tasks/math. The TOOL-012 blindspots baseline can be
lowered accordingly.)*

---
