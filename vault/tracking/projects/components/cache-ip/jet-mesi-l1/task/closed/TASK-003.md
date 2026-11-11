# TASK-003: give jet its hit latency back (sync-read address lead, v3 classify overlap)

**Date:** 2026-11-08
**Priority:** P2
**Status:** CLOSED 2026-11-10 (lat_min 3 on bin 16, == the v2 baseline)
**Owner:** jet

## Why

The Genesys2 pair-rig sweeps across the FPGA review bins (cache-ip/common-ip
TASK-001) show jet's resident read-hit latency at 6 cycles against the v2
baseline's 3 and amber's 4:

| step | lat_min | r4k_we0 cycles / 20k txn | disjoint64k cycles |
|---|---|---|---|
| v2 baseline (2026-11-03, 100 MHz) | 3 | 100,480 | 402,042 |
| v3 capture/classify pipeline (bin 3) | 5 | 140,464 | 407,409 |
| BRAM sync-read data array (bin 5) | 6 | 160,608 | 417,246 |
| bins 6-10 (RAM stores, snoop fix, reset tree) | 6 | 160,608 | 417,246 |
| step 1: data-array address lead (bins 11-15, 2026-11-09) | 5 | 140,624 | 409,845 |
| steps 2+3: transparent skid + head-deposit bypass (bin 16, 2026-11-10) | 3 | 100,624 | 369,845 |

Two cycles are the v3 lookup split (ISSUE-001's fix); one is the registered
data array read. Amber paid nothing for the same array because `l1_control`
presents the data address in LOOKUP, a stage ahead of the way select.

## What

1. Present the data-array read address one stage earlier in `jet_control`
   (the amber pattern: address leads, "address last cycle was mine"
   qualifier on the data), keeping `DATA_SYNC_READ=1` and the BRAM mapping.
   Expected: lat_min 6 -> 5, r4k_we0 back to ~140k.
2. Then look at whether classify can overlap the tag read in v3 instead of
   following it, which is the remaining +2 against v2. This changes the
   accept handshake; formal (safety 64, live 176) and the pair rig are the
   gate, as for v3.

## Done when

- Jet component DV gate+func+full green; jet-g2 harness gate green; from-reset
  disjoint64k board run == the 20k cosim CRCs.
- `formal/jet/jet_control` prove, prove-live and cover PASS on the final flat.
- Genesys2 bin with lat_min <= 5 at 100 MHz, WNS >= 0, sweep err 0; the
  per-step table above extended with the new row in the task's closure.

## Progress

### 2026-11-09 step 1 implemented: port A address lead (bin 11)

`jet_control` presents the classify-stage occupant's `{set, beat}` on data
port A whenever neither the commit read cursor nor an unfired read serve
needs the port; `r_pa_srv_d1` records the lead at the accept, so under
`DATA_SYNC_READ` the read serve fires in the cycle the record is loaded.
With the combinational array the record owns the port for its residence,
as before. Lint clean; jet gate 19/19, func 60/60, jet-g2 harness gate 2/2.

Genesys2 bin 11 (same flow as the review bins; 21,676 LUT / 24,444 FF, WNS
+0.152 at 100 MHz, no budget yet), 20k-txn sweep, bin 10 -> bin 11:

| config | lat_min | run cycles | delta | CRCs | err |
|---|---|---|---|---|---|
| r4k_we0 | 6 -> 5 | 160,608 -> 140,624 | -12.4% | same | 0 |
| r64b / r1k / smoke4k we64 | 5 -> 5 | ~155.5k -> ~140.5k | -9.6% | same | 0 |
| r16k_we64 | 5 -> 5 | 159,709 -> 144,786 | -9.3% | same | 0 |
| r64k_we64 / disjoint64k | 5 -> 5 | 416,138 / 417,246 -> 408,684 / 409,845 | -1.8% | same | 0 |
| r64k_we255 / r128k_we64 | 5 -> 5 | -0.0% / -0.7% | | same | 0 |

From-reset disjoint64k: ci0 0x6c206c22 / ci1 0x84d28860 (== bin 10 == the
20k cosim), 411,047 cycles. The resident configs are back at the v3 bin-3
numbers (140,464): the sync-read cycle is recovered in full. jmon drops on
r64k_we64 1549 -> 1435 (ISSUE-002, unchanged in kind).

Timing: bin 10 closed at +0.517 (worst path on u_jet1), bin 11 at +0.152 on
an UNCHANGED cone (u_jet0 r_sn_state -> data-array write address, not the
read-address mux this step touched): the placer band the owner's rule names.
Both cache-ip XDCs now carry `set_clock_uncertainty -setup 0.200` on the
MMCM clock (the DDR2-board rule, MC-011); bin 12 = the same RTL rebuilt
under it.

Bin 12 (same RTL, under the budget): 21,703 LUT / 24,444 FF, WNS +0.129
with the 0.200 ns uncertainty applied (the report's clock-uncertainty term
reads -0.261 against bin 11's -0.061) -- closed with real margin by the
owner's rule. Worst path again a port B address cone (u_jet1 r_fq_done_ptr
-> b_addr), unrelated to step 1.

Bin 12 on the board: smoke PASS, from-reset disjoint64k CRCs and cycles
identical to bin 11, and the full sweep identical to bin 11 in every
config's CRCs, run cycles and lat_min (`results/perf_sweep_bin12_*.json`).
The board holds bin 12.

Still to land for step 1: jet FULL on the edited tree, formal prove /
prove-live on the regenerated flat (cover PASS 7/7 + live cover 6/6).

### 2026-11-09 the first FULL-level run of jet since v3, and what it found

The pushed review RTL had never run its FULL suites. Run on a `git archive`
snapshot of HEAD (2bb8dd321) and on the edited tree: 108 / 42 failures, in
three classes, none of them the lead:

1. **Build failures at two parameter corners**, both introduced by the
   review commits: jet BUG-001 (`jet_mshr` set_full width at MSHR_COUNT=2,
   WAYS=4) and jet BUG-002 (`jet_wb_buffer` store index width at
   VICTIM_DEPTH=1). 25 cells never ran. Both fixed; all 25 build and pass.
2. **Read-data mismatches in every jet_core FULL cell**: a testbench
   regression from the v3 per-way rewrite (carried in da431d86b). A merged
   read must observe the write slots ahead of it in the merge list
   (`jet_control`'s C_MERGE contract, unchanged since v2, and what the RTL
   deposited); the v3 TB expected raw memory. The v2 TB's line-keyed
   `_content()` modelled it, which is why the pre-review grid passed 36/36
   (re-run on a 28571cf33 archive). Fixed in `jet_core_tb.py`.
3. **`ovb: set_oversub stall observed`** at s128w4 with K >= 8: the
   scenario's burst (2 + merge list + WAYS) exceeds the K+2 response ring,
   so under v3's tag-at-capture the overflow misses wait as TAG_FULL and
   classify after the claims retire. A reporting effect, also on the pushed
   RTL; the scenario's carve-out now covers it and logs the reason.

Also: the golden harness's `repo_root()` ran `git rev-parse` eagerly inside
an `os.environ.get` default and killed every parity cell in a non-git tree;
fixed. Clean jet FULL on the final tree, harness gate + 20k cosim, bin 13
(lead + BUG-001/002 + budget) and the formal re-run on the regenerated flat
are in flight.

Bin 13 (lead + BUG-001/002 fixes, under the budget): 21,703 LUT / 24,444 FF
and WNS +0.129, identical to bin 12 -- the two fixes are logic-identical at
the default parameters. Board: smoke PASS, from-reset disjoint64k CRCs
0x6c206c22 / 0x84d28860 at 411,047 cycles, the full sweep identical to bins
11 and 12 in every config (`results/perf_sweep_bin13_*.json`). The board
holds bin 13.

### 2026-11-09 the clean FULL run after the fixes: two more finds

Clean jet FULL on the lead + BUG-001/002 + TB fixes: 146 passed, 3 failed.

4. **jet BUG-003 (P1): the pair fabric hangs** at `s128w4l64b64_m16v1_fifo`,
   seed 54355, deterministic. `jet_pair_fabric`'s buffer-free rule skipped
   the trailing-absorption clear during ANY `F_REPLAY_R`, not just a replay
   from that buffer; an absorption BVALID for direction 0 landing during
   direction 1's replay left `buf_vld_q[0]` set forever and `g_take[0]`
   false forever (dump: grant_q 1, buf 01, absp 00, pend_cnt0 1, AR held).
   Owner-qualified the guard; the seed replays clean. The same fabric is
   on the Genesys2 rig, so this was a board hang waiting for its timing.
   The cell had never built before BUG-002.
5. **`vc: claim-aware stall observed`** at `s128w4_m02v{1,4}_lru`, seeds
   51255 / 53505: a construction miss -- the claim's glacial fill retired
   before the stalling miss was captured, so no window existed. The pin now
   scores the real property (the miss allocates only after the claim
   retires), logs a snoop-held or missed window instead of failing, and
   reports the reasons it saw. Both seeds pass with the miss logged.

Bin 14 (lead + BUG-001/002/003 fixes, under the budget): 21,730 LUT (+27 for
the fabric fix) / 24,444 FF, WNS +0.347. Board: smoke PASS, from-reset
disjoint64k identical, full sweep identical to bins 11-13 in every config
(`results/perf_sweep_bin14_*.json`), harness gate 2/2 and 20k cosim CRCs
unchanged on the fixed fabric. The board holds bin 14.

Clean jet FULL on the final tree (lead + BUG-001/002/003 + TB fixes):
**149 passed, 0 failed** (2026-11-09 10:13). The first green FULL for jet
since v3.

Formal, `formal/jet/jet_control`, 2026-11-09. On the lead alone (flat
regenerated from jet_control with the address lead): cover 7/7, live cover
6/6, prove depth 64 PASS (5h31m), prove-live depth 176 PASS (5h21m). On the
flat regenerated again with BUG-001 (jet_mshr) and BUG-002 (jet_wb_buffer),
both of which are inside the flat: cover 7/7 and live cover 6/6 (no
unreached), prove depth 64 PASS (4h20m), prove-live depth 176 PASS (4h10m).
The committed `jet_control_flat.v` is that second flat.

Step 1 committed 2026-11-09 with BUG-001/002/003 closed. Step 2 (the
classify/tag-read overlap, the remaining +2 against v2) is what keeps this
task active.

### 2026-11-10 steps 2+3: the two remaining cycles, without touching jet_control (bin 16)

Step 2 as filed was "overlap classify with the tag read". Counting the
resident read hit cycle by cycle on the v3 pipe showed the +2 against v2
was not in `jet_control` at all: it was two empty FIFOs that each cost a
cycle on the way through.

| cycle | bin 15 (lat 5) | where the cycle went |
|---|---|---|
| c0 | CPU handshake, frontend pulse, skid write | |
| c1 | skid presents to lkup; tag read, capture | **the request skid was empty** |
| c2 | classify; data-array address lead (step 1) | |
| c3 | data lands, read serve fires, deposit into `jet_rsp_seq` | |
| c4 | ring `r_valid` visible, release into the frontend staging FIFO | **the response ring's head slot was empty** |
| c5 | `cpu_rsp` valid | |

- **Step 2, `jet_cpu_plane`: the request skid is transparent while empty.**
  An arriving request is presented to the lookup in its own cycle
  (`w_skid_bypass = fe_req_valid & ~skid_rd_valid`); the skid is written only
  when the lookup does not accept it that cycle, so the hold-until-accepted
  contract and `jet_control`'s capture logic are unchanged. c1 is gone.
- **Step 3, `jet_rsp_seq`: head-deposit bypass.** A deposit whose tag is the
  release head of an empty ring is offered as `rsp_valid_o` in the deposit
  cycle, with `rsp_data_o` taken from `cpl_data_i`; if the consumer takes it,
  `r_valid` is never set. The bypass is deliberately NOT offered to
  `tag_gnt_o` (the grant keeps the deposit cone off the accept path). c4 is
  gone.

`jet_control.sv` and the shared `l1_cpu_frontend` are untouched. Both
changes are the handbook's one-buffer-per-hop rule read for latency: an
empty buffer still costs a cycle unless it is transparent
(`vault/handbook/design/one-buffer-per-hop.md`, new section).

DV on the final tree: jet lint at the 168-warning baseline; jet gate 19/19;
jet FULL **149 passed, 0 failed** (10m16s); `jet_rsp_seq` unit test; jet-g2
harness gate 2/2 with the 20k cosim; `jet_control_tb` taught the same-cycle
bypass release (a deposit released in its own cycle never enters the
deposit set -- `_bypass_rel` / `_record_deposit`).

Formal, `formal/jet/jet_control`, flat regenerated with the rsp_seq bypass
(the flat includes `jet_rsp_seq`): cover 7/7 and live cover 6/6, prove
depth 64 PASS (4h46m), prove-live depth 176 PASS (4h11m). The committed
`jet_control_flat.v` is that flat. Note for the next run: the sby status DB
(`status.sqlite`, shared by the prove and cover tasks of one `.sby`) is
corrupted when two tasks start together ("database disk image is
malformed" at the end of cover); start them a few seconds apart.

Bin 16 (steps 2+3 on bin 15's RTL, under the 0.200 ns budget): 21,714 LUT /
24,268 FF, WNS **+0.468**, 0 failing endpoints. Board at 100 MHz: smoke
PASS; from-reset disjoint64k ci0 0x6c206c22 / ci1 0x84d28860 (== the 20k
cosim, == every bin since 10) at 371,047 cycles; full sweep err 0,
unexpected 0 in all 11 configs (`results/perf_sweep_bin16_*.json`). In
every config `lat_sum` and `run_cycles` fell by exactly 40,000 (2 cycles x
20k transactions), the latency histogram moved one bucket down with
identical populations, and every CRC matched bin 15:

| config | lat_min | run cycles bin 15 -> 16 | v2 baseline | CRCs |
|---|---|---|---|---|
| r4k_we0 | 5 -> 3 | 140,624 -> 100,624 | 100,480 | same |
| r16k_we64 | 5 -> 3 | 144,786 -> 104,786 | | same |
| r64k_we64 | 5 -> 3 | 408,684 -> 368,684 | | same |
| disjoint64k_we64 | 5 -> 3 | 409,845 -> 369,845 | 402,042 | same |
| r64k_we255 / r128k_we64 | 5 -> 3 | -40,000 each | | same |

The resident configs are back at v2 (+144 cycles); the thrash configs are
now 8% under v2 because they keep step 1's lead and the MSHR overlap.

Monitor side (ISSUE-002, the J7 error bar, owner: leave as is): the
monbus tallies moved while every injector-side count stayed identical
(acc 15,880 -> 11,346, jmon_drop 1,456 -> 821 on disjoint64k). Not chased
here. One test lesson from it: the jet-g2 `tally_latch_bank` test cleared
the latch bank while the 3-beat AXIL record egress was still draining
end-of-run records, and the denser hit stream exposed it as a seed-
dependent "latch fill not re-armed"; the test now settles the monbus
(stable tally total across a gap) before every clear and decodes any stray
slot it finds. Test defect, not RTL.

Closed 2026-11-10. Every "Done when" line is met; the per-step table above
carries the bin 16 row.
