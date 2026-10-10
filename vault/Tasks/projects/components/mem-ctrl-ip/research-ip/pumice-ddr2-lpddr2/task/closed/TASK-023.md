# TASK-023: retire ALL hand-poking of valid/ready interfaces in pumice DV

> **Migrated from `PUMICE-014`** on 2026-09-27, when this area's flat
> `closed.md` was split into one file per item to match the rest of the vault.
> The legacy ID is cited throughout the repo -- RTL comments, DV code, handbook
> notes, commit messages and session memory -- so it is NOT rewritten at those
> call sites; `vault/Tasks/MIGRATION_MAP.md` and this line are how an old
> `PUMICE-014` reference resolves. Body below is verbatim from the flat page.
>
> Lane chosen by reading this item's own Status line and opening, not its title:
> a keyword pass over the 35 items misclassified 14 of them.


**Status:** CLOSED 2026-08-29 — COMPLETE. No hand-driven handshake
remains anywhere in pumice DV. The two remaining are deliberate
exclusions with reasons, not leftovers — see below. HARD RULE from Sean:
"None of the environments should EVER hand poke on any standard interface
or valid ready interface", and "If there are bfms you don't need to set any
signals" — the BFM drives the PAYLOAD too, not just the handshake.
See [[feedback-always-use-axi4-bfms]].

**DONE (0 handshake pokes remaining; residual counts are non-handshakes):**
top: `test_pumice_core_dfi` (50→0), `test_pumice_core` (33→0),
`test_pumice_top_csr` (22→0), `test_pumice_top` / `_geared` (2 ea→0).
fub/macro: `pumice_axi4_ifc_tb` (35→0), `pumice_wr_intake_tb` (34→0),
`pumice_rd_intake_tb` (32→0), `pumice_wr_data_cam_tb` (17→6),
`pumice_rd_cmd_cam_tb` (13→3), `pumice_dfi_cdc_tb` (12→0),
`test_pumice_dfi_cmd_path` (8→2), `pumice_cmd_arbiter_tb` (7→0),
`test_pumice_dfi_wr_serializer` (6→0), `pumice_mem_cmd_scheduler_tb` (3→0).

**Collateral to reuse, do not re-roll:**
* `dv/tbclasses/pumice_axi_bfm.py` — `PumiceAxiBfm`, the one place any
  pumice `s_axi_*` is driven. `write=`/`read=` for single-direction ports.
* `dv/tbclasses/pumice_fub_bfm.py` — `fub_consumer()` / `fub_producer()`
  over the GAXI BFMs for fub-internal valid/ready ports, with an explicit
  `signal_map` (pumice's `aw_push_bank_o` style names do not match GAXI
  auto-discovery, and explicit fails loudly on a rename).

**The two deferred files were FINISHED 2026-08-29**, not waived. Both had
the same root problem -- the MEASUREMENT, not the driver -- and the same fix:
rebase onto the OBSERVED handshake cycle instead of a fixed offset from when
the testbench presented. That is BFM-compatible and more honest (it measures
the DUT's latency, not latency-from-the-testbench).
  * `test_pumice_dfi_rd_aligner.py` — `_CycleObs` records op fires and
    rddata_en cycles; t_rddata_en checked as (en - fire), and the tCCD case
    asserts OUTPUT gaps track INPUT gaps rather than hardcoding 2. Pacing
    comes from the `fixed` valid_delay profile.
  * `dfi_cmd_formatter_tb.py` — `_watch_fire` counts accepts; the check
    samples once the accept is observed, with NO extra cycle (the outputs are
    registered from the accepted command, so an extra wait sampled after
    valid dropped -- that was why the first attempt failed).
  Both mutation-checked: firing a read a cycle early (the ILA-confirmed
  silicon bug) fails the aligner tests; corrupting the bank encoding fails
  9 of 10 formatter tests.

**Not handshakes — verified against the RTL port lists, leave hand-driven:**
CREDITS with no matching valid — `rd_op_ready_i` ("rd aligner has a free
slot"), `bank_act_ready_i` / `bank_rdwr_ready_i` / `bank_pre_ready_i`
(per-bank permission vectors). STROBES with no ready — `wr_done_valid_i`,
`dfi_rddata_valid_i` (DFI read data is unconditional per spec),
`init_cmd_valid_i`, `sched_lu_valid_i`, `snarf_probe_valid_i`,
`wr_fire_i`. Read-only MONITORS also stay (`_mon_b`, `_mon_r`): the AXI
master owns bready/rready but the sequence result carries no per-beat
rid/rlast/rresp/bresp. Observing is not poking.

**Two traps that cost real time — read before the next port:**
1. **Queue-and-go vs blocking send.** `send()` blocks until its packet is
   accepted, so awaiting per beat leaves a GAP between beats. A hand-rolled
   "present the head every cycle" source is always-valid; to match it use
   `_driver_send` (queues and returns). The wr-serializer tCCD test
   measures gaps between `wrdata_en` pulses and read 3 where 2 was
   required until this was fixed.
2. **`ready_policy` is not the `backtoback` profile.** GAXISlave's default
   `valid_first` waits for valid on a CLOCKED loop, so ready lands a cycle
   LATE even at ready_delay 0. Use `ready_policy='always'` to model a TB
   that used to tie ready to constant 1, and `'stall'` +
   `set_ready_policy()` for deterministic consumer backpressure.
   (RDS-DV c220c19 / aacb90d / 5fcf039.)

**Whenever GAXI changes, run all of val/amba** (Sean). Baseline for A/B:
739-741 passed / 2-4 failed at `-n 24` with SEED pinned, and the failing
set is NOT stable run to run — see [[AMBA-MONRATE-INTERMITTENT]]. Do not
read a single differing failure as a regression.

**Also outside pumice (same rule, flagged not owned):**
`projects/components/utility-ip/misc/dv/tbclasses/axi4_slave_wr_crc_check_tb.py`.

**Rule going forward:** no NEW test may hand-poke a valid/ready interface.
