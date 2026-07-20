<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Known Issue: active_count Accumulator Underflow

**Status:** ✅ FIXED (2026-07-18) — `active_count` now derived as a registered
CAM-occupancy pop-count (structurally `[0, N]`, cannot underflow).
**Severity:** MEDIUM–HIGH — corrupted `active_count`, `busy`, and `block_ready`
**Date Reported:** 2026-07-18 (found by formal proof during TASK-025)
**Date Fixed:** 2026-07-18
**Affects:** `rtl/amba/monitor/axi_monitor_trans_mgr.sv` (`r_active_count`), and by
propagation `rtl/amba/monitor/axi_monitor_base.sv` (`busy`, `block_ready`,
`active_count` outputs)
**Found by:** `formal/amba/axi_monitor_trans_mgr` and `formal/amba/axi_monitor_base`
SymbiYosys BMC proofs (`ap_count_bounded` / `ap_no_overflow`).

---

## Fix (2026-07-18)

`active_count` is now derived directly as the registered pop-count of
`cam_entry_valid` (option 1 below), replacing the alloc-minus-cleanup
accumulator entirely:

```systemverilog
always_comb begin
    w_occupancy = '0;
    for (int i = 0; i < N; i++) w_occupancy += cam_entry_valid[i];
end
`ALWAYS_FF_RST(aclk, aresetn, ... r_active_count <= w_occupancy; ...)
```

It is structurally bounded to `[0, N]`, cannot underflow, and lags occupancy by a
single cycle (which `block_ready`'s `BLOCK_MARGIN=3` absorbs).  An intermediate
saturate-at-0 attempt made `ap_count_bounded` pass but a formal accuracy probe
showed the count still drifted (under-reported), so the pop-count derivation was
adopted.  Verified: all 12 monitor formal proofs pass, and the
`axi4_master_rd_mon` cocotb integration test passes at `MAX_TRANSACTIONS=16`.

The historical analysis below is retained for reference.

---

## Summary

`active_count` in `axi_monitor_trans_mgr` is not a direct count of live CAM
entries — it is a free-running **accumulator**:

```systemverilog
r_active_count <= r_active_count + r_alloc_cnt - r_cleanup_cnt;   // 8-bit, wraps
```

where `r_alloc_cnt` and `r_cleanup_cnt` are pipelined pop-counts of the per-slot
alloc one-hots (`addr/data/resp_alloc_oh`) and the cleanup vector
(`cam_entry_valid & w_can_cleanup`). Under an adversarial-but-broadly-legal AXI
input sequence, cumulative cleanup can exceed cumulative alloc, so the accumulator
**underflows to 0xFF** and never recovers (it is free-running). Once wrong,
`active_count` stays wrong for the rest of the session.

The RTL comment at the accumulator claims *"alloc and cleanup are registered by
the SAME amount so the active_count accounting stays consistent."* The formal
proof shows this invariant does **not** hold for all input timings.

---

## Symptoms

1. `active_count` reads `0xFF` (or other wrong values) while the trans CAM is
   actually empty (`cam_entry_valid == 0`).
2. `busy = (active_count > 0)` sticks high with no live transactions.
3. `block_ready = (active_count < MAX-BLOCK_MARGIN)` sticks **low** →
   upstream is stalled indefinitely (a flow-control wedge). This is a plausible
   contributor to the separate `axi_monitor_blockready_hang_partial_channels`
   long-session hang.

---

## Reproduction (formal)

```bash
source env_python
cd formal/amba/axi_monitor_trans_mgr
make clean && make axi_monitor_trans_mgr_flat.v
sby -f axi_monitor_trans_mgr.sby prove      # FAIL: ap_count_bounded / ap_no_overflow
```

The counterexample reaches `active_count == 0xFF` with `cam_entry_valid == 0`
roughly **8 cycles after reset release**.

### What was ruled OUT (the harness models a legal bus and still fails)

The `formal_axi_monitor_trans_mgr` harness was hardened with sound, standard
legal-AXI environment constraints; the underflow survives all of them:

| Constraint added                                             | Result |
|-------------------------------------------------------------|--------|
| 5-cycle (and 10-cycle) reset hold to flush the pipeline     | still fails (failure just shifts later — input-driven, not reset-flush) |
| AXI VALID stability (VALID held w/ stable payload until READY)| still fails |
| Well-formed reporter feedback (`event_reported ⊆ valid`)     | still fails |
| Legal read ordering (no R beat with zero outstanding reads)  | still fails |
| Unique outstanding IDs (no duplicate in-flight AR ID)        | still fails |
| `MAX_TRANSACTIONS = 2` and `= 4`                             | fails at both (not a small-N corner) |

So the underflow is **not** an initial-state artifact, not phantom feedback,
not orphan (R-before-AR) beats, and not same-ID aliasing. It is a genuine
accounting error in the pipelined alloc/cleanup accumulator.

---

## Suspected root cause

The alloc side sums **three** one-hots (`addr_alloc_oh + data_alloc_oh +
resp_alloc_oh`) while cleanup sums **one** (`cam_entry_valid & w_can_cleanup`).
These are registered through the alloc/cleanup pipeline (`q_*_alloc_oh` →
`r_alloc_cnt`; `w_cleanup_vec` → `r_cleanup_cnt`). When a slot is allocated and
retired with certain relative timing — or when the alloc and its matching
cleanup land in different pipeline batches — the pop-count of cleanups entering
the accumulator can transiently exceed the pop-count of allocs, and because the
accumulator is 8-bit free-running with no floor at 0, it wraps to 0xFF.

---

## Recommended fixes (pick one — design decision)

1. **Derive `active_count` structurally** (preferred): drive it from the true CAM
   occupancy `active_count = $countones(cam_entry_valid)` (registered once for
   timing) instead of an alloc−cleanup accumulator. Structurally in `[0, N]`,
   can never underflow. This was likely avoided for a route-timing reason on the
   pop-count; if so, register the pop-count and accept one cycle of extra
   `active_count` latency (block_ready already carries a `BLOCK_MARGIN=3`
   headroom that tolerates it).
2. **Clamp the accumulator**: never let `r_active_count` go below 0 (saturate the
   subtract) and add an assertion `r_alloc_cnt`-cumulative ≥ `r_cleanup_cnt`-cumulative
   as a design invariant. This masks the symptom but leaves the accounting skew.
3. **Document a legal-AXI env assumption** and waive the formal property — only
   acceptable if analysis proves the skew is unreachable on a strictly-legal bus.
   The formal evidence above suggests it is reachable under legal AXI, so this is
   the weakest option.

---

## Formal-proof status (after fix)

All 12 monitor formal proofs pass, including `ap_count_bounded` / `ap_no_overflow`
in `formal/amba/axi_monitor_trans_mgr` and `formal/amba/axi_monitor_base`.  The
trans_mgr proof also gained a port-only `ap_clear_zeroes_count` property (the
synchronous CAM clear zeroes `active_count` next cycle).  The stale DEPS,
`block_ready` polarity, and pipeline-latency issues found alongside this were also
fixed (see TASK-025).
