# MC-003 residual read-side hang — root-cause report

**Scope:** `projects/components/mem-ctrl-ip/`  
**Repro:** `projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2_char_framework/dv/tests/test_granite_char_gap.py::test_granite_char_col_major_gap` with `TEST_TREFI=200`  
**Trace:** `projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2_char_framework/dv/tests/local_sim_build/cocotb_test_granite_col_major_gap/dump_current.vcd`

---

## 1. Observed failure

```bash
source env_python
export PYTHONPATH="$(pwd)/bin"
TEST_TREFI=200 pytest projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2_char_framework/dv/tests/test_granite_char_gap.py::test_granite_char_col_major_gap -v -s
```

Result:

| metric | value |
|---|---|
| `wr` | `True` (write engine finishes) |
| `wr_status` | 3 |
| `rd` | `False` (read engine times out) |
| `rd_status` | 4 |
| `mism` | 19 |
| `errors` | 256 |
| `match`/`valid` | `True` (CRC matches the *corrupted* stream, so the engine did consume data, just wrong data) |

The write path is clean.  The read path returns the right **number** of beats (`RD_ALIGNER probe: valids=512 captured=512`) but some beats land in the wrong AR-order slots after a refresh boundary, so the engines/CRC declare failure.

---

## 2. Cycle-cited trace evidence

All times are in ps, sampled on `aclk` rising edges (`granite_char_uart_tb_top.aclk`).

### 2.1 Allocation and issue order are correct

Return-ring allocations are per-AR and sequential (`alloc_valid_i = ar_push_valid_o && rd_cam_ins_ready_i`, `mc_axi4_plane.sv:457`):

| time | `alloc_tk` | event |
|---|---|---|
| 516590000 | 0 | AR0 admitted, ticket 0 |
| 516600000 | 1 | AR1 admitted, ticket 1 |
| 516610000 | 2 | AR2 admitted, ticket 2 |
| … | … | … |

Read scheduler issues (entry-store `rd_iss_valid_o`/`rd_iss_ticket_o`) are out-of-order by bank, as expected for the per-bank core:

| time | ticket | bank | slot | col | op |
|---|---|---|---|---|---|
| 516630000 | 0 | 0 | 0 | 0 | RD |
| 516650000 | 1 | 0 | 1 | 4 | RD |
| 516670000 | 2 | 0 | 2 | 8 | RD |
| 516710000 | 8 | 1 | 6 | 0 | RD |
| 516730000 | 9 | 1 | 2 | 4 | RD |
| 516750000 | 10 | 1 | 7 | 8 | RD |
| … | … | … | … | … | … |

The return ring writes DFI read data into ticket slots in issue order and drains in AR order (ticket 0, 1, 2, …).  This part of the design is working.

### 2.2 A refresh is granted while read returns are still in flight

At 516890000 `refresh_req_i` rises.  The per-bank scheduler blocks **new** demand columns via `w_ref_col_block` (`mc_bank_sched.sv:215-219`), so reads stop issuing, but reads issued earlier are still returning.

The scheduler’s read-return hold counter (`r_rdret_cnt`, `mc_bank_sched.sv:374-379`) is a simple 48-cycle down-count loaded on `rd_issue_valid_o`.  Because no new RD issues during the refresh-pending window, the counter reaches 0:

| time | `refresh_req_i` | `r_rdret_cnt` | `refresh_grant_o` | `rr_head` | `rr_tail` | `rr_occ` | last / next `dfi_ret_valid_i` |
|---|---:|---:|---:|---:|---:|---:|---|
| 516890000 | 1 | 48 | 0 | 0 | 17 | 17 | previous return: ticket 13 @ 517020000 |
| 517370000 | 1 | **0** | **1** (REFab) | 3 | 19 | 16 | last return before REF: ticket 14 @ 517090000; next return after REF: ticket 17 @ 517760000 |

At **517370000 ps** a REFab is granted while `rr_occ == 16` and the read-return path still has outstanding tickets (head = 3, tail = 19).  The next DFI read return does not arrive until **517760000 ps** — a 67-cycle gap — precisely because the refresh clipped/aborted the in-flight read returns.

### 2.3 Return framing breaks after the refresh

Before the refresh, ticket slots become ready (`r_ready[t]`) in the expected issue order:

| ticket | first `r_ready` high |
|---|---|
| 0 | 516850000 |
| 1 | 516870000 |
| 2 | 516890000 |
| 8 | 516930000 |
| 9 | 516950000 |
| 10 | 516970000 |
| 11 | 516990000 |
| 12 | 517010000 |
| 13 | 517030000 |
| 14 | 517100000 |
| 16 | 517080000 |

After the refresh, tickets 3–7 (the next AR-order head) do **not** become ready until much later and out of natural order:

| ticket | first `r_ready` high |
|---|---|
| 3 | 518310000 |
| 4 | 518330000 |
| 5 | 518350000 |
| 6 | 518370000 |
| 7 | 518390000 |

Meanwhile the read aligner resumes producing returns for newly-issued reads (ticket 17 @ 517760000, 18 @ 517780000, …).  The AR-order drain is therefore fed mis-framed beats, producing the 19 `mism` and 256 `errors` observed by the engines.

---

## 3. Mechanism

The per-bank scheduler in `mc_bank_sched.sv` has a combinational fire stage.  It can issue a read and then, one cycle later, start draining PREs and grant a refresh **before** the read data has returned.  The read-aligner (`mc_dfi_rd_aligner`) derives its `rd_last` framing from a modulo word counter with no resync.  If a refresh (or any PRE that closes the bank) lands inside the read-return window, the return burst is clipped, the modulo counter reframes `rd_last` onto the wrong word, and **every subsequent read** lands in the wrong ticket slot in the return ring.

The existing `r_rdret_cnt` counter was intended to prevent this by holding REF out for 48 cycles after each RD issue.  It is insufficient because:

1. It is reloaded only by `rd_issue_valid_o`.  During a refresh-pending window `w_ref_col_block` stops new RD issues, so the counter can expire while previously-issued reads are still in flight.
2. It measures time since the **last** issue, not the actual open read-return window.  The return window stays open until the last outstanding read burst finishes, which can be much longer than 48 cycles when issue stalls.
3. The refresh-drain PRE path (`w_ovr_op == OP_PRE` in `mc_bank_sched.sv:417-435`) is not gated by `w_rdret_busy`; only the REF grant itself is.

---

## 4. Why the FRFCFS core avoids it

The FRFCFS core (`mc_cmd_arbiter.sv`) has two structural differences:

1. **No stale read-return gap.** Its `w_ref_safe` predicate (`mc_cmd_arbiter.sv:1254`) requires `!w_inflight_preact && (r_guard0 == '0) && (r_guard1 == '0)` in addition to no active rows.  These guards mean no command (including a just-issued read) is still in the arbiter pipeline when refresh is granted.
2. **Pipeline spacing.** The FRFCFS core has a registered 5-stage pick pipeline.  A read issues today and fires to DRAM several cycles later; a refresh grant cannot squeeze into the narrow return window because the pipeline naturally spaces the two events.  The per-bank core’s fire stage is combinational, so it can issue a read and grant a refresh in adjacent cycles.

The per-bank core’s fixed `RDRET_HOLD` counter is an attempt to emulate that spacing, but because it is not tied to the actual return activity it collapses whenever new reads cannot issue for 48 cycles.

---

## 5. Minimal fix proposal

**Option A (recommended): track the real read-return window.**

Add a `rd_ret_busy_i` input to `mc_bank_sched.sv` driven by the read aligner / DFI plane (asserted while `dfi_rddata_en` is high or while the aligner has outstanding/uncompleted read bursts).  Include it in the refresh safety predicates:

```systemverilog
assign w_ref_safe   = !w_any_active && !w_rfc_busy && !w_rdret_busy && !rd_ret_busy_i;
assign w_refpb_safe = !r_row_act[RK0][refresh_bank_i] && !w_rfc_busy && !w_rdret_busy && !rd_ret_busy_i;
```

This keeps REF out of the return window even when the issue-side counter has expired, and it does not depend on estimating a worst-case delay.

**Option B (local stop-gap): reload the counter from return activity.**

If adding a new scheduler input is undesirable, route `dfi_ret_valid_i` (or the aligner’s equivalent) back to `mc_bank_sched.sv` and reload `r_rdret_cnt` on **both** `rd_issue_valid_o` and the return-valid signal.  This keeps the counter alive while beats are still arriving.  It is less precise than Option A because it still does not know when the **last** beat of the last outstanding burst has arrived.

**Option C (aligner-side) is possible but larger:** make the aligner resynchronize its word counter whenever `dfi_rddata_valid` resumes after a gap.  That would make the controller robust to clipped returns, but it does not prevent the underlying JEDEC violation of refreshing while read data is returning.

**Recommendation:** implement Option A.  It is the smallest change that fixes the root cause and mirrors the FRFCFS core’s structural “no in-flight command” safety predicate.

---

## 6. Files examined

- `projects/components/mem-ctrl-ip/common-ip/rtl/fub/mc_bank_sched.sv` — per-bank scheduler, read-return hold counter, refresh safety predicates.
- `projects/components/mem-ctrl-ip/common-ip/rtl/fub/mc_cmd_arbiter.sv` — FRFCFS core, `w_ref_safe` and in-flight guards.
- `projects/components/mem-ctrl-ip/common-ip/rtl/fub/mc_xddr2_entry_store.sv` — read ticket storage and issue handshake.
- `projects/components/mem-ctrl-ip/common-ip/rtl/fub/mc_rd_return_ring.sv` — AR-order return buffer.
- `projects/components/mem-ctrl-ip/common-ip/rtl/macro/mc_axi4_plane.sv` — allocation wiring (`alloc_valid_i = ar_push_valid_o && rd_cam_ins_ready_i`).
- `projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/rtl/top/granite_core.sv` — top-level connections.
- `projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2_char_framework/dv/tests/test_granite_char_gap.py` — repro test.

---

*No RTL changes were made.  This report is based on the current state of the repo (stale-skid fix already in `mc_bank_sched.sv`).*
