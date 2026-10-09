# TASK-024: SPLIT axi4_intf_observer into master + slave versions; retire the original and dma_slave_monitors

> Migrated 2026-09-27 from `vault/Tasks/amba/closed.md` as **TASK-065** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Priority:** P1
**Status:** DONE -- both halves (re-measured 2026-08-31). The retirement
completed itself while the page went stale -- again. One NEW defect fell out of
the re-measurement; see the end of this entry.
**Owner:** TBD

**Re-measured 2026-08-31 -- the 08-30 "retirement outstanding" text below is
now wrong too, and is kept only to show what changed:**

* `axi4_intf_observer.sv` -- GONE (was already true).
* `dma_slave_monitors` -- **GONE ENTIRELY**. `find` returns NOTHING: no
  `.sv` in either location, no `_tb.py` in either location, no filelist.
* Blocker 1 (the `stream_mon_harness.sv:1622` instantiation) went with the
  whole NexysA7 `stream_characterization` area in `9461b6aa`.
* Blocker 2 (the `build-mon` FUB test `test_dma_slave_monitors.py`) is gone
  too; `build-mon/dv/tbclasses/` now holds only `__init__.py`.
* No live reference remains anywhere -- every surviving mention is prose in a
  comment, a doc, or a task page.

So there is nothing left to delete. The duplication this task set out to remove
removed itself, via an area deletion nobody connected back to here. **That is
the second time this page described a live blocker that the tree had already
overtaken**, which is the lesson worth keeping: a task page asserting the state
of the tree is a claim with a shelf life, and re-measuring is cheaper than
planning against it ([[kimi-review-rounds]] rule 11 is the same idea for docs).

**NEW DEFECT, found by the re-measurement -- host/RTL regmap mismatch:**

`slvmon_regs` outlived the module it configured. On the RTL side it is now
ORPHANED: `slvmon_regs_top` is instantiated nowhere and no filelist pulls
`slvmon_regs_top.f`. But it is still live from the HOST side, and pointed at
the wrong block:

* `stream_harness.sv:452` routes the `slvmon_apb` window (@ 0x180000) to
  `u_slave_observer`, which instantiates **`obs_regs_top`**.
* `build-mon/host/host_reg_walk.py` still walks that same window with
  **`slvmon_device`**'s map, labelled "slvmon_apb  dma_slave_monitors".

The two maps are unrelated at the same offsets -- at `0x024`, obs_regs has
`AXIS_MASK1` and slvmon_regs has `RDSLV_ADDR_RANGE_HIGH`. So a register walk or
any configuration through that window reads and writes the wrong fields, in
silence.

NOT FIXED HERE, deliberately: `build-mon/host/` is another session's live area
(Genesys2 board bring-up) and this needs their call on whether the host
retargets to the obs_regs map or the window moves. Reported to them
2026-08-31. Once the host is repointed, the whole `slvmon_regs` set --
`.rdl`, `.vlt`, the filelist and the generated RTL/regmap -- can be deleted as
dead, the same shape as the four dead packages closed in `65fa8cf0`.

**Measured state -- read this before planning, the label was stale:**

DONE, the split half:

* `projects/components/utility-ip/misc/rtl/axi4_intf_master_observer.sv` and
  `axi4_intf_slave_observer.sv` both exist.
* The original `axi4_intf_observer.sv` is GONE from the tree.
* The new observers are adopted in three harnesses:
  `Genesys2/stream/rtl/stream_harness.sv`, `.../harness_csr.sv`, and
  `NexysA7/pumice/build-perf/rtl/ddr2_char_harness.sv`.

NOT DONE, the retirement half. `dma_slave_monitors` is live in TWO
independent places, so it cannot simply be deleted:

1. `NexysA7/stream_characterization/flows-stream-monitor/rtl/stream_mon_harness.sv:1622`
   instantiates it -- the one remaining RTL instantiation, to be converted to
   the slave observer.
2. Genesys2 `build-mon` has an ACTIVE FUB test,
   `build-mon/dv/tests/test_dma_slave_monitors.py`, which compiles
   `projects/components/utility-ip/misc/rtl/filelists/dma_slave_monitors.f`. So the
   misc/rtl copy is not dead code -- it is what that test builds. Decide
   whether the test is retargeted at the slave observer or retired with the
   module.

Then the duplication goes: TWO copies of `dma_slave_monitors.sv` (misc/rtl
and flows-stream-monitor/rtl), TWO copies of `dma_slave_monitors_tb.py`
(Genesys2 build-mon and NexysA7 flows-stream-monitor), and two filelists.

**COORDINATE BEFORE EDITING.** As of 2026-08-30 `stream_mon_harness.sv` and
both `dma_slave_monitors_tb.py` copies are modified in the shared worktree by
another session, on branch `feat/stream-observer-monitor-instrumentation` --
which is plausibly this very work in flight. Check that before starting, or
two sessions will convert the same harness.

**GOAL — say it first, because it sets every sizing decision:** exercise ALL
FOUR axi4 monitor flavours in the **stream `build-mon` configuration**:

    axi4_master_rd_mon   axi4_master_wr_mon
    axi4_slave_rd_mon    axi4_slave_wr_mon

The monitors are the DUT here, not instrumentation. That has consequences:

- In `build-mon` the taps must be **ON** (`ENABLE_MON_TAPS=1`) — a monitor with
  its taps off is not under test. Which means the table MUST be sized so
  `block_ready` never drops, because with taps on the wrapper's gate is live
  and a saturated table corrupts the bus (see the 49->367 replay below). The
  ID slice / `NUM_BANKS` work exists to make that sizing closeable.
- In `build-perf` the taps stay **OFF**: no instrumentation in the datapath,
  no gate, nothing to saturate.
- Success = all four modules driven under heavy traffic with monbus/tally
  evidence per flavour, not merely "the build runs".

**Mechanism:** `axi4_intf_observer` (ex-`axi4_dma_observer`) is SPLIT INTO TWO
MODULES — a master version and a slave version. **The original goes away**;
this is a replacement, not a second instance added alongside it. Two observers
because one role cannot exercise the other role's monitors.

- master version — wraps `axi4_master_rd_mon` / `axi4_master_wr_mon`, hangs off
  the STREAM ports. (This is what today's `axi4_intf_observer` already does
  internally, so it is the closer descendant of the original.)
- slave version — wraps `axi4_slave_rd_mon` / `axi4_slave_wr_mon`, hangs off
  the DMA slaves.
- When both exist, DELETE `axi4_intf_observer` and repoint `u_dma_observer` in
  `stream_harness.sv` at the master version. No module keeps the old name: a
  block that instantiates master monitors must not be reachable under a name
  that reads as role-neutral, which is how the slave side ended up hand-rolled
  as `dma_slave_monitors` in the first place.
- **Parallel snoop**, not series pass-through. Each observer carries its own
  AXIL monbus group feeding its **own** tally module.
- A monitor OBSERVES. It must never drive the datapath handshake.

**Step 0 — the hang fix, independent of the rest.** Retire
`dma_slave_monitors` and instantiate `axi4_dma_slaves` raw in
`stream_harness.sv` (`u_dma_slaves`). That alone restores the 8-channel perf
build.

**Why (measured, from the ch3 wedge in build-perf):**
`dma_slave_monitors` (commit `ee07c71a`, 2026-08-09 — inside the regression
bracket: `f22fafb9` passes 8ch, HEAD hangs) splices slave monitors INLINE on
the DMA-slave bus with a single un-sliced `MAX_TRANSACTIONS(16)` table, while
STREAM runs 8 channels x 8 outstanding = 64 concurrent. The table saturates,
`w_block_ready` drops (first at 6977.92 us), and
`axi4_slave_rd_mon.sv:491` masks only the OUTWARD `s_axi_arready` while the
core underneath still sees the ungated `s_axi_arvalid` and accepts. STREAM,
never having seen a handshake, holds the same AR on the bus and the core
accepts it again — every cycle.

Counted at both ends over 0..7030 us:

| tap | AR handshakes, id 3 |
|---|---|
| `harness.f_rd_ar` (what STREAM sees) | 49 |
| `u_rd_injector.fub_axi_ar` (what the slave sees) | 367 |

Each replay is a well-formed 16-beat burst (15.97 beats/AR), so every
per-transaction property passed. What broke was CONSERVATION, which nothing
was watching. Nothing in `build-perf` even reads these monitors, and
`slvmon_regs.rdl` defaults `MON_EN=1`, so they came up enabled and unread.

**Enabling work already landed (uncommitted at time of writing):**
- ID-filter restore, 15 files — `1e6b1d9d` had removed the per-tap ID slice
  (`ID_FILTER_ENABLE` / `ID_MATCH_BASE` / `ID_MATCH_COUNT`); restored
  byte-identical to `1e6b1d9d^`. 4 taps x 2 channels verified via
  `test_axi_mon_id_slice[0,2,4,6]`.
- `USE_WDATA_ORDER_Q` (`axi_monitor_trans_mgr.sv`, default 0) — AW-order queue
  replacing the WID-less O(N^2) oldest-select. Push slot on AW handshake, pop
  on W-last. 9 passed off, 9 passed on.
- `NUM_BANKS` (default 1) — same-bank guards on `pick_oldest` and the rank
  update (elaboration constants, so cross-bank comparators are never built),
  per-bank survivor counts, plus `addr/data/resp_alloc_mask` on
  `monitor_trans_cam` so an ID can only allocate inside its own bank.
- Both parameters plumbed wrapper -> `axi_monitor_filtered` -> `axi_monitor_base`
  -> `trans_mgr` across all 12 wrappers.

**Open work:**
- [ ] Step 0 above (fixes the hang on its own).
- [x] **DONE 2026-08-14.** Split into `axi4_intf_master_observer.sv` (taps
      `axi4_master_{rd,wr}_mon`) and `axi4_intf_slave_observer.sv` (taps
      `axi4_slave_{rd,wr}_mon`), both in `projects/components/utility-ip/misc/rtl/`.
      Naming is the owner's: `axi4_intf_<role>_observer`, not
      `axi4_intf_observer_<role>`.

      **They are OBSERVERS: every AXI4 port is an INPUT** (46 of them, zero
      outputs on the observed bus), including both halves of each handshake so
      a beat is recognisable from the wire alone. The only outputs are the
      AXIL monbus egress, the APB config slave, and status. This settles the
      "parallel snoop vs taps ON" contradiction in this task's own text: the
      observers no longer sit in the path at all.

      `stream_harness.sv` rewired accordingly — what used to run
      `rd_* -> u_dma_observer -> f_rd_*` is now a direct assign, with the
      observer watching those wires. The instrument can no longer gate the
      DMA. Both observers lint clean; the rewired harness elaborates with 0
      errors.

      Filelists created for both, and they now pull their own tap closure
      (`axi4_<role>_{rd,wr}_mon.f` + `axi_perf_latency_hist.f`) — the old
      filelist did not, so it could not stand alone and lint needed the taps
      added by hand.
- [x] **DONE 2026-08-14.** DELETED `axi4_intf_observer.sv` + its filelist, and
      repointed every caller: `stream_harness.sv` (instantiation + 3 comments),
      `harness_csr.sv` (2), `stream_harness.f`, `monbus_group.f`,
      `dma_slave_monitors.f`, both NexysA7 harness filelists, the host/DV
      Python (`obs_addrs.py`, `host_bus_meters.py`, `host_reg_walk.py`,
      `test_stream_mon{,_perf}.py`, `val/amba/test_axi_mon_block_ready.py`),
      `build-perf/Makefile`, five `docs/markdown/rtl-amba` pages, and the
      pumice / rapids task pages. `grep axi4_intf_observer` over `*.sv`/`*.f`
      returns nothing; the only surviving mentions are this task page's own
      historical record.
- [ ] **Egress mismatch — THIS IS THE BLOCKER for instantiating the slave
      observer (confirmed against the harness 2026-08-16).** `stream_harness`
      wires the slave monbus path as `m_axil_*` (AXIL write master -> bridge
      master `slave_monbus_wr` -> `u_slave_tally`), which is what
      `dma_slave_monitors` provides via `monbus_axil4_axil4_group`. Both new
      observers inherit `monbus_axil4_axi4_group` from the original, so they
      expose `m_axi_*` (AXI4 burst master) instead. The slave observer cannot
      take `u_dma_slaves`' place until the group is parameter-selected:
      declare both port sets and generate-select so the port list is stable.

      **The rest of that swap is mapped and mechanical.** Replace
      `dma_slave_monitors u_dma_slaves` (harness ~1692-1775) with
      `axi4_dma_slaves`, carrying the same `s_axi_*` / CRC / beat-count /
      busy connections, and add the slave observer snooping the SAME
      `f_rd_*` / `f_wr_*` nets. Those are the nets the MASTER observer
      already snoops -- one bus, both roles, which is exactly what exercises
      all four monitor flavours. Non-AXI ports to carry over from the old
      instance: `cam_clear` (csr_cam_clear), `s_apb_*` (slvmon_apb_*),
      `s_axil_*` (se_*), `m_axil_*` (slmon_*), `irq_out`,
      `cfg_base_addr`/`cfg_limit_addr` (0x000C0000 / 0x000FFFFF).
- [ ] **Generate the CAM NUM_BANKS times** (generate loop of
      `monitor_trans_cam`, depth MAX_TRANSACTIONS/NUM_BANKS each) so each
      instance closes timing. Currently only the age/rank logic is banked;
      one full-depth CAM is still instantiated. See the GAP note above.
- [ ] Then synthesise to confirm convergence at N=64/B=4 (16 per CAM), and
      run that config against observer traffic.
- [ ] `stream_harness.sv:1956` currently passes `NUM_RD_PORTS(1)`/
      `NUM_WR_PORTS(1)` with `ENABLE_MON_TAPS=0`; confirm against the intended
      4x2 topology.

**WHY 4x — TIMING, not capacity.** The observers are instantiated with params
set so the **CAM is GENERATED 4 TIMES**. Each generated CAM is then small
enough to close timing (16 entries measured at WNS +1.018 ns; a single table at
40 entries is -25.183 ns and will not close, 72 never). The 4x is a timing
measure that happens to also give enough slots; do not describe it as sizing.

**CAM replication: DONE.** `monitor_trans_cam` is now instantiated inside a
`generate` loop, NUM_BANKS times, each of depth MAX_TRANSACTIONS/NUM_BANKS
(`g_cam_bank` in `axi_monitor_trans_mgr.sv`). Per-bank one-hots are stitched
back into the flat N-wide vectors, so everything downstream is unchanged, and
allocation is confined by construction (`*_wants_alloc` gated on
`bank_of(id) == gb`). At NUM_BANKS=1 it is a single CAM of depth N -- the
original design. Verified: NUM_BANKS=1 passes (3 passed), lint clean.

The age/rank logic (`pick_oldest` + the rank update, the two O(N^2) structures)
is banked by the same-bank guards, and `USE_WDATA_ORDER_Q` removes the
WID-less cross-ID oldest-select that would otherwise have forced a global
compare.

**RESOLVED 2026-08-14 — it was (b), a real defect, and it is FIXED.**

The recorded `test_axi4_master_wr_mon[8-32-32-1-4-16-4-8-4-func]` failure does
NOT reproduce: that test passes at NUM_BANKS=1 and 4, with the order queue on
and off, across 10 seeds each (30/30). It was never sensitive to the defect —
the test could not even express NUM_BANKS until this session (it now takes
`NUM_BANKS` / `USE_WDATA_ORDER_Q` from the environment and puts both in the
`sim_build` name, so a banked run cannot silently reuse an unbanked binary).

The defect is real and was found by inspection, then proven directly.
`pick_oldest` compares SAME-BANK ONLY, justified by "candidates come from an
ID-matched vector, and every entry with a given ID lives in one bank". True
for the read path (`w_data_cand_open` <- `data_match_oh`) and for
`addr_update_oh` (<- `addr_match_oh`); FALSE for the WID-less write path,
whose candidate set `w_data_state_pred_oh` is a state predicate spanning every
bank. So at NUM_BANKS=B the write select returned one winner PER BANK and a
single W beat advanced up to B transactions — the issue #41 double-count,
reintroduced across banks. Measured at N=16/B=4: one W beat advanced slots 0
and 4 together.

**Why nothing saw it:** `val/amba/test_axi_monitor_trans_mgr.py` hardcodes
`IS_READ: '1'`, so the entire transaction-manager regression exercises the
read path only. "trans_mgr passes at 8-32-16" was never evidence about writes
at any bank count.

**Fix (owner's design, 2026-08-14): a common WID FIFO.** Push the AWID on the
AW handshake, pop on W-LAST; the head AWID keys the write-data candidate set.
That puts the write path back inside the ID-matched world `pick_oldest`
assumes — every candidate shares one ID, therefore one bank, so the same-bank
compare is exact by construction rather than by luck. Replaces the slot-index
queue that `USE_WDATA_ORDER_Q` used to select (same parameter name, new
implementation, so no wrapper re-plumbing).

Carries a REPO-WIDE bus requirement, recorded in
[[valid-ready-contracts]]: **W must not lead AW.** Same-cycle AW+W stays
supported via the empty-queue bypass; W strictly before its AW has no AWID to
attribute it to and is treated as a stray. This is the restriction commercial
VIPs commonly impose.

`NUM_BANKS>1` on a write monitor now REFUSES to elaborate without
`USE_WDATA_ORDER_Q=1` (`$error`) — the combination has no correct behaviour to
fall back to. Covered by
`val/amba/test_axi_monitor_trans_mgr_wr_bank.py::test_banked_write_without_widq_is_refused`
alongside the attribution check itself (5 passed: nb1/nb4 x wq, plus the board
sizing N=64/B=4, plus the refusal).

TIMING at N=64/B=4 remains unverified — that is still a synthesis question,
untouched by this fix.

**SECOND BANKING DEFECT, found by the wq=1 sweep and FIXED 2026-08-14.** The
same-cycle AW+W bypass reads a LOCAL MIRROR of the CAM's allocation pick, and
the mirror scanned for the lowest free slot GLOBALLY. Under banking the CAM
allocates inside the ID's bank, so the mirror named a slot in a different bank
and the bypass bound the W beat to an entry that was never allocated:

```
0 completion packet(s), expected 1 -- the same-cycle W beat was lost
1 spurious error packet(s) (codes=['0x4']) -- B after a lost W beat
                            fabricates EVT_PROTOCOL 'response before data'
```

That is the exact failure `95c9490a` originally fixed, back again via banking.
Fix: mask the mirror scan with `w_addr_bank_mask` (all ones at NUM_BANKS=1, so
the unbanked path is bit-identical). Verified `test_axi_monitor_wr_same_cycle`
+ `test_axi4_master_wr_mon` at wq1/nb4, wq1/nb1, wq0/nb1 — 5 passed each; the
pre-fix RED at wq1/nb4 is the mutation evidence.

**The pattern worth carrying forward:** banking invalidated TWO separately
documented invariants — "candidates come from an ID-matched vector"
(`pick_oldest`) and "the CAM allocates the lowest free index" (the bypass
mirror). In both cases the comment asserting the invariant survived the change
while the property it described did not.

**That audit is now DONE and comes back clean.** All six `pick_oldest` call
sites were re-read against B>1: `w_widq_cand_oh` (head AWID, ID-matched — the
fix), `w_addr_pend_oh` (<- `addr_match_oh`), `w_data_cand_open`/`_any` (<-
`data_match_oh`), and `w_resp_cand_open`/`_any` (<- `resp_match_oh`) are all
ID-matched and therefore same-bank by construction. The one non-ID-matched
set, `w_data_state_pred_oh`, is now unreachable when banked (elaboration
guard). The allocation mirror was the only other flat-table assumption and is
bank-masked. No further sites outstanding.

**FORMAL COVERAGE GAP (found 2026-08-14, still open).** The banked
configurations are not proved. `formal/amba/axi_monitor_trans_mgr/*.sby` has
no `NUM_BANKS` / `USE_WDATA_ORDER_Q` override, so the flattened DUT is built
at the parameter defaults (`NUM_BANKS=1`) and every monitor proof runs the
UNBANKED design only. That is not a small hole: `ap_bypass_alloc_mirror`
asserts precisely the invariant that banking broke a second time (see the
same-cycle bypass mirror below), and it passes — because at NUM_BANKS=1 the
invariant is still true. Banking needs its own proof configuration, or the
properties that encode "one flat table" assumptions have to be re-read against
B>1 by hand every time.

**Consequence of ID banking (the constraint that follows):** every transaction
sharing an ID lands in one CAM, so per-ID concurrency is capped by the
GENERATED CAM's depth, not by the total:

    MAX_TRANSACTIONS/NUM_BANKS >= (IDs per bank) * (outstanding per ID)

8ch x 8 outstanding over 4 banks = 16/bank -> `MAX_TRANSACTIONS=64,
NUM_BANKS=4`, and 16 is the depth measured to close (WNS +1.018 ns; 40 entries
= -25.183 ns). Undersize it and entries are refused, not mis-tracked:
`test_axi_monitor_trans_mgr` reports "four outstanding AR(id=2) occupy 2
slot(s), expected 4" at N=8/B=4, and passes at N=16/B=4.

**Debug collateral:** `projects/fpga-systems/Genesys2/dma-ip/stream/build-perf/dv/tests/GTKW/ch3-sram-counts.gtkw`
(110 signals across the three SRAM pointer pairs and both engines) against the
pinned `local_sim_build/ch3-hang.fst`.

---
