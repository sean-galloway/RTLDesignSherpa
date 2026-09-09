# Set aside, not deleted

## pumice_rbl_table.sv, pumice_row_pred_table.sv -- RESTORED 2026-09-09

Back in `rtl/fub/` (modes 5/6/7 built again, timing re-gated on the
write-lead tree). Their history is in git; nothing of them stays here.

## pumice_bank_cmd_picker.sv, pumice_bank_sched_core.sv (2026-09-03)

The two-stage bank-partitioned command scheduler (per-bank pickers + a
tournament core) that replaced the flat arbiter behind `+define+PUMICE_BANK_SCHED`
and was briefly the sole arbiter. It is CORRECT and fully verified (FUB 16/16,
macro 12/12 incl. double-issue + tRTW, top 114/114) and shallow in mux-level
terms (81 -> 23), BUT it is ~2.3x the flat arbiter's LUTs (the 8 parallel
pickers), which fills the xc7a100t -1 to 97% slices and route-congests: the
100 MHz build failed at WNS -24 ns, and even 2-bank grouping (-28% arbiter LUTs)
only reached WNS -22 ns / 88% slices. The worst path (`w_bs_rd_head_wins`, the
cross-CAM global-oldest compare) is ~45 tech levels -- logic alone ~10 ns at a
10 ns period on the -1 grade, so it will not close 100 MHz on this part
regardless of area.

**Why set aside, not deleted.** The base returns to the flat single-stage
FR-FCFS arbiter (`rtl/fub/pumice_cmd_arbiter.sv`, restored from b7a43b9f^), which
fits (32% LUTs) and closes at 66.67 MHz. The two-stage is preserved as the
sophisticated tier for the planned codegen family -- enable it on a faster/roomier
part (e.g. the Genesys2 xc7k325t) where its shallow logic pays off without the
area penalty. See [[project_pumice_bank_scheduler]] and
[[feedback_mux_level_not_fpga_timing]] for the full timing story.

**Restoring:** these consume the CAM `sch_*` vectors + bank timers; re-instantiate
in place of the flat arbiter's pick logic (or wire as an alternate arbiter),
restore their filelist entries, and delete the two exempt lines in
bin/filelists.toml.
