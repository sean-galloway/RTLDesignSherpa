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

# Formal Targets

**Harnesses:** `formal/onyx/onyx_ccu/` (N_PORTS 2), `formal/onyx/onyx_ccu_n3/`
and `formal/onyx/onyx_ccu_n4/` (one N-generic harness,
`onyx_ccu_n3/formal_onyx_ccu_n.sv`, built at N_PORTS 3 and 4). Method:
`vault/handbook/dv/formal.md` (sv2v flatten, SymbiYosys BMC, every
assertion mutation-checked, vacuity covers). Run results and their dates
are in onyx TASK-001; the status below is as of 2026-11-27.

## Geometry

All three harnesses flatten `onyx_ccu.f` specialized to `ADDR_WIDTH = 8`
(16 lines), `LINE_BYTES = 16`, `BUS_WIDTH = 32` (four beats a line),
`AXI_ID_WIDTH = 3`, `SLOTS = 4`, `SNOOP_INFLIGHT = 2`, `DEFER_AR = 0`,
`SERIAL_MODE = 0`; only `N_PORTS` differs. The IO port is free under the
harness's IO assumptions (single-line full-width INCR shareable reads,
`ARSNOOP` 0, `AWSNOOP` 0 / 1, AXI stability, W after AW).

## Tasks and bounds

| Harness | Task | Properties | BMC depth |
|---|---|---|---|
| N = 2 | `prove` | the local properties (27 per the `.sby`) | 24 |
| N = 2 | `prove_book` | the end-to-end bookkeeping properties | 16 |
| N = 2 | `cover` | the covers | 40 |
| N = 3, 4 | `prove` | all 29 local properties | 20 |
| N = 3, 4 | `prove_fast` | 17 of those 29 | 32 |
| N = 3, 4 | `prove_book` | 4 bookkeeping properties | 16 |
| N = 3, 4 | `cover` | 41 covers | 40 |

: Table 5.1: Formal tasks (from the `.sby` files)

**Status** (commit c6273863b and onyx TASK-001): at N = 3 and 4, cover
41/41 and `prove_fast` (17 properties, depth 32) PASS, and 19 mutants fail,
at both N; the N = 3 `prove` (29 properties, depth 20) PASS. The N = 4
`prove`, both `prove_book` runs, and N = 2's re-prove on flat 34a9908c
(after BUG-001..003): running, see onyx TASK-001.

Every depth is a **BMC bound, not a proof**. The `onyx_ccu_n3.sby` header
derives them: the longest uncontended single-transaction path at four beats
a line is a PassDirty fill of about 20 steps, independent of N (a gather
costs its slowest peer, not the sum); what N adds is contention, about 69
steps for one transaction under full three-way contention, which no
affordable depth reaches at any N. The header states what each bound
covers.

## What is stated, by block

| Block (Chapter 2) | Properties |
|---|---|
| Front end (ch02/01) | `ap_arready_slot`, `ap_ar_pairing`, `ap_grant_one_ar`, `ap_pend_count`, `ap_no_pend_ovf` |
| Table, lock, release (ch02/02) | `ap_line_unique`, `ap_grant_unlocked`, `ap_release_after_retire`, `ap_rack_source`, `ap_free_complete`, `ap_table_flags`, `ap_engines_live` |
| Fanout and gather (ch02/03) | `ap_ac_legal`, `ap_ac_stable`, `ap_sn_count`, `ap_cd_slot`; at N = 3 and 4 the per-peer shadow `ap_peer_shadow`, `ap_cr_slot`, `ap_snq_count` |
| Memory read path (ch02/04) | `ap_mar_legal`, `ap_mar_stable`, `ap_mar_no_wr_race` (BUG-002), `ap_route_mem`, `ap_mo`, `ap_r_inflight`, `ap_r_beats` |
| Buffers and replay (ch02/05) | `ap_route_rpl`, `ap_r_stable` |
| Write port (ch02/06) | `ap_wb_select_hold`, `ap_abs_after_old_wb` (BUG-003), `ap_wb_order` (jet-prime BUG-002), `ap_abs_legal` |
| IO port (ch02/07) | `ap_io_port` |

: Table 5.2: Properties by block

The N = 2 harness reads the gather through the DUT's all-accepted and
gathered flags; the N-generic harness adds a per-peer shadow of which
peers each slot still owes an AC and a CR, which the counters summarize,
and checks the counters against it.

## The mutation record

Each harness header carries its mutation record. The mutants that tie
properties to the bugs this design has had: the gather declared complete
at once, the fanout including the requester, a second grant with an AR
untaken (TASK-001 step 4); CleanUnique back to MakeInvalid (BUG-001), the
memory read without the write-in-flight hold (BUG-002), WriteClean back
into `is_coh_req`, the old-write-back order removed (BUG-003)
(TASK-001, 2026-11-26).

## Not stated

- `DEFER_AR = 1` is in no harness; the core-alone rig and the reference
  rig simulate it (Chapter 5.2).
- `SERIAL_MODE = 1` is in no harness and, in the test files read for this
  book, in no simulated configuration either (the core-alone rig pins it
  to 0).
- Liveness is not proven; the bounds above are safety BMC.
- The event taps are not read by the properties.
