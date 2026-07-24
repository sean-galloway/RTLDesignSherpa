<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# AMBA tasks — active (in progress)

### TASK-025: Update formal proofs for the monitor logic

**Priority:** Medium
**Status:** [~] In progress (2026-07-18) — infrastructure fixed, **all 12 pass**;
the real RTL bug the proofs surfaced (active_count underflow) is FIXED and
functionally re-validated; some extensions + a val/amba path sweep still pending.

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
- [ ] **val/amba monitor-test path sweep (NEW, pending).** The monitor move left
      ~75 val/amba tests building monitor source paths via
      `os.path.join(rtl_dict['rtl_shared'], "...")` where `rtl_shared='rtl/amba/shared'`
      — the earlier string-based sweep missed these because the path is assembled at
      runtime. `test_axi4_master_rd_mon.py` fixed (repointed to `rtl/amba/monitor`);
      the rest still need the same repoint.
- [ ] Extend the proofs to cover the new perfmon window state machine + the four
      utilization / beat-byte-burst counters (`axi_monitor_base`). *(pending)*
- [ ] Add a `cam_clear` synchronous-clear property to the trans-CAM proofs. *(pending)*
- [ ] Confirm the `ENABLE_*_LOGIC=0` cone-drop configurations still prove (or are
      excluded intentionally). *(pending)*
- [ ] `axi_monitor_timer` has a `formal/amba/` dir but **no Makefile/harness** — it
      was never set up. Decide whether to author one (net-new proof) or drop it from
      the list.
- [x] Update any formal filelist/`.sby` that still assumes the old `shared/` layout —
      all Makefiles regenerated against `rtl/amba/monitor/`; all 12 flatten cleanly.

---

