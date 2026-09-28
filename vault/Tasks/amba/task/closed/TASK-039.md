# TASK-039: Update formal proofs for the monitor logic

> Migrated 2026-09-27 from `vault/Tasks/amba/active.md` as **TASK-025** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.

**Priority:** Medium
**Status:** CLOSED 2026-09-28 -- all 12 monitor proofs pass (last runs 2026-09-27/28), the four pending boxes are each done or rejected with a reason below. Was: in progress since 2026-07-18.

**Context:** The monitor modules moved from `rtl/amba/shared/` (and the per-protocol
dirs) to **`rtl/amba/monitor/`**, and the monitor RTL gained new logic since the
formal proofs were last exercised (perfmon window/counters, `cam_clear`, the
`cfg_compl/threshold/debug` enables, `ENABLE_*_LOGIC` synthesis cones, always-on
CAM pipelining). The `formal/amba/*` Makefiles + `.sby` files were path-updated to
`monitor/` and verified to resolve, but the **SymbiYosys proofs were not re-run**.

**Checklist:**
- [x] Run `make` in each `formal/amba/{...}` and confirm they pass after the move.
      **10/12 pass.** The stale DEPS lists (the reporter split into six
      `axi_monitor_reporter_*` sub-modules + the `monitor_trans_cam` extraction +
      `apb_monitor_addr_check`) broke yosys elaboration everywhere; fixed by a new
      `tools/gen_formal_deps.py` that regenerates each Makefile's DEPS from the
      transitive module closure and derives the sv2v file list from `$(DEPS)` so the
      two can't drift again. Also fixed: `axi_monitor_base` `block_ready` polarity
      assertion (RTL fix flipped it to positive-enable; old assert encoded the
      pre-fix inverted polarity), `axi_monitor_trans_mgr` pipeline-latency staleness
      of `ap_alloc_from_empty` (always-pipelined CAM), and `apb5_monitor`'s stale
      128-bit-packet protocol assertion (apb5 emits the compact 64-bit monbus word;
      protocol is at `[59:57]`, not `[108:105]`).
- [x] **Real RTL bug found AND FIXED.** `axi_monitor_trans_mgr` + `axi_monitor_base`
      failed `ap_count_bounded`/`ap_no_overflow`: `active_count` (the alloc-minus-
      cleanup accumulator) **underflowed to 0xFF** ~8 cycles after reset under a
      broadly-legal AXI sequence, corrupting `busy`/`block_ready`. Fix: derive
      `active_count` as the registered pop-count of `cam_entry_valid` (structurally
      `[0, N]`, cannot underflow); a saturate-at-0 attempt passed the bound but a
      formal accuracy probe showed it still under-reported, so the pop-count form
      was adopted. All 12 monitor proofs now pass; `axi4_master_rd_mon` cocotb test
      passes at MAX_TRANSACTIONS=16. Added a port-only `ap_clear_zeroes_count`
      (cam_clear) property to trans_mgr. See
      `rtl/amba/KNOWN_ISSUES/axi_monitor_active_count_underflow.md`.
- [x] **val/amba monitor-test path sweep — DONE, verified 2026-09-15.** The
      "~75 tests" figure is no longer true: the area moved to filelist-based
      sourcing, which resolves monitor paths through the registry rather than by
      string-joining `rtl_shared`. Measured across all 170 val/amba tests:
      **166 use `get_sources_from_filelist`**, exactly **1** still hand-lists
      `verilog_sources`, and only **1** uses `os.path.join(rtl_dict[...])` at all
      — whose 2 joined paths both resolve to files that exist. Zero tests
      string-reference the old `shared/<monitor>` path, `rtl/amba/shared/` holds
      **no** monitor sources, and all 31 monitor modules live in
      `rtl/amba/monitor/`. Checked by resolving each test's own `rtl_dict` keys
      and testing the joined path for existence, not by grepping one line.
- [x] Perfmon window proofs -- REJECTED with a reason: the perf window is the one
      cone no shipped build carries (the lite has no perf cone by design; STREAM and
      RAPIDS measure with axi_bus_meter), and the full monitor is now the reference
      implementation and test oracle rather than a product. A proof over a cone
      nothing instantiates is effort without a consumer. Reopen against a build
      that ships it.
- [x] Add a `cam_clear` synchronous-clear property to the trans-CAM proofs. DONE (it was already there: `ap_clear_zeroes_count` in formal_axi_monitor_trans_mgr.sv, driven from an anyseq `cam_clear`; the box was stale).
- [x] `ENABLE_*_LOGIC=0` cone-drop configurations -- PARTLY, deliberately: the base
      harness proves the shipped shape (`ENABLE_PERF=0`, `ENABLE_DEBUG=0`, i.e. the
      perf and debug cones dropped, error/timeout/compl/threshold built). The
      error/timeout/compl/threshold-off variants are not proven and are excluded
      intentionally: no consumer builds them off, and since 2026-09-26 no shipped
      build instantiates the full monitor at all (every consumer is on
      axi_monitor_lite, which has its own harness, PASS).
- [x] `axi_monitor_timer` harness -- DONE (stale box): `formal/amba/axi_monitor_timer/`
      has its Makefile, .sby and `formal_axi_monitor_timer.sv`; prove and cover PASS,
      last run 2026-09-27.
- [x] Update any formal filelist/`.sby` that still assumes the old `shared/` layout —
      all Makefiles regenerated against `rtl/amba/monitor/`; all 12 flatten cleanly.

---

## Closure (2026-09-28)

Measured state at closure: every monitor-related harness under `formal/amba/`
-- axi_monitor_base, trans_mgr, filtered, reporter, timeout, timer, addr_check,
apb4_monitor, apb5_monitor, axi_monitor_lite, axis_monitor_lite -- reports
prove PASS and cover PASS from runs on 2026-09-27/28. `monitor_trans_cam`,
`monbus_arbiter` and `apb_monitor_addr_check` have no harness of their own; the
CAM is proven through trans_mgr's harness, the other two were never in this
task's list of twelve. The one real find of this task (the `active_count`
underflow) is fixed and recorded in `rtl/amba/KNOWN_ISSUES/`.
