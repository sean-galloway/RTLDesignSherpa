# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""pumice CSR reset-parity manifest (TASK-015 layer 0).

Gated by `bin/check_csr_reset_parity.py`. Every `sw=rw` field in
`pumice_csr.rdl` appears here exactly once, under exactly one of:

    ships=<v>     the reset value IS what we ship. The top suite runs resets, so
                  declaring this says "the suite is testing the shipping design".
                  The gate fails if the reset stops matching <v>.
    swept=(..)    the reset is deliberately NOT a single shipping value because
                  DV varies the field; needs by= (the artifact) and oracle=
                  (what fails if a value is wrong).
    waived="..."  neither, with a reason. Command strobes and counters live here.

`ships` and `swept` are not mutually exclusive in reality -- `policy_mode` both
resets to its shipping value and is swept 0..5. Where both are true this file
records `swept`, because that is the stronger statement: the field is exercised
at more than its reset. `ships` is for the fields where the reset is the ONLY
value anything runs, which is precisely the population pumice BUG-003 came from.

WHY THE FILE IS THIS LONG. It is 75 decisions. Before it existed they were
defaults nobody had read, and one of them (policy_mode resetting to the legacy
build default while the board programmed mode 3) is what BUG-003 was. The
population churns: 73 at TASK-015, 65 after BUG-020 retired the 27 undriven
OBS_* registers, +10 writable fields with the 2026-10-07 LPDDR2 calibration
block. DOCUMENTED_FIELD_COUNT below must always equal len(FIELDS) --
bin/tests/test_check_csr_reset_parity.py enforces it, because a count pinned
anywhere else went stale and red for ten days (BUG-023).
"""

# Paths are relative to THIS file.
REGMAP = "../regs/generated/pumice_csr_regmap.py"
RDL = "../rtl/macro/pumice_csr.rdl"

# Clock parity. TASK-015: the "54% in sim vs 3% on board" conversion comparison
# in TASK-013 compared a 100 MHz DUT against a 75 MHz one and blamed silicon.
# The board is 75 MHz; the sim default must be the same number.
CLOCK = {
    "hz": 75000000,
    "env": "PUMICE_MC_CLK_HZ",
    "declared_by": "projects/fpga-systems/NexysA7/mem-ctrl-ip/pumice/build-perf/host/pumice_char.py",
    "note": "board_ddr2_300 in dv/tbclasses/pumice_dram_configs.py carries the "
            "same 75 MHz; that table is what the sim layers run.",
}

_MATRIX = "projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/dv/tests/macro/test_pumice_sched_matrix.py"
_CONFIGS = "projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/dv/tbclasses/pumice_dram_configs.py"
_JEDEC = ("the JEDEC command-stream checker (dv/tbclasses/pumice_cmd_stream_checker.py) "
          "asserts on the emitted command stream, so a wrong value shows up as a "
          "state or timing violation rather than as a slow run")

# The authoritative population count. bin/tests/test_check_csr_reset_parity.py
# asserts len(FIELDS) == this number; the tripwire only works if the count
# moves in the SAME commit as the fields. BUG-023: the old floor (>= 70) lived
# in bin/tests, was never re-based at BUG-020, and was red for ten days.
DOCUMENTED_FIELD_COUNT = 75

FIELDS = {
    # ---- swept: DV runs more than the reset, with an oracle ------------------
    "PAGE_POLICY_CFG.policy_mode": dict(
        drives="page_mode_i",
        swept=(0, 1, 2, 3, 4, 5), by=_MATRIX, oracle=_JEDEC,
        note="PAGE_ARMS: build_default/static_open/static_close/fixed_open x2, plus "
             "the two retired encodings as a fallthrough regression. Resets to 3, "
             "the shipping default (board: +9.1% col_major, +35.1% col_major_interleaved).",
    ),
    "PAGE_TIMEOUT_CFG.tr_init": dict(
        drives="page_tr_init_i",
        swept=(0, 2, 8), by=_MATRIX, oracle=_JEDEC,
        note="Only meaningful for the background-close modes. Resets to 2, measured "
             "as the best default in TASK-013 and blocked by BUG-003 until it was fixed.",
    ),
    "DFI_PHASE.bl": dict(
        drives="BL",
        swept=(4, 8), by=_CONFIGS, oracle=_JEDEC,
        note="Six of the twelve named operating points are BL8. One BL per "
             "controller instance, fixed at init. NOTE the reset is 8 while this "
             "board build is BL4 (DDR2CharDriver.BOARD_DRAM_BL), re-written by "
             "program_geometry after every soft_reset -- same divergence as "
             "gear_ratio and MR0, recorded in pumice ISSUE-016. It is `swept` "
             "rather than `waived` because DV genuinely runs both widths.",
    ),

    # ---- ships: the reset is the only value anything runs --------------------
    "ADDR_MAP.bank_lsb": dict(ships=0x0A, note="bits [12:10] of the AXI address select the bank at the shipping geometry"),
    "ADDR_MAP.hash_en": dict(ships=0x0, note="address hashing OFF; measured inert on this workload and never enabled on the board"),
    "ADDR_MAP.hash_seed": dict(ships=0x00, note="unused while hash_en=0"),

    "DFI_PHASE.gear_ratio": dict(
        waived="RESET IS A DIFFERENT BUILD'S GEOMETRY, and the driver compensates. "
               "The reset 0x2 is log2(1:4); this board build is 1:2 and "
               "DDR2CharDriver.BOARD_GEAR_RATIO writes 0x1 after every soft_reset "
               "(program_geometry), because soft_reset reverts the CSRs to the RTL "
               "resets. Whether an RDL reset should track one build's geometry, in a "
               "controller parameterised for several, is a design decision and not a "
               "sweep -- pumice ISSUE-016. Not `ships`: I first declared ships=0x2 by "
               "reading the reset instead of the board, which is the vacuous "
               "declaration this file's header warns against."),
    "DFI_PHASE.rd_phase": dict(ships=0x0, note="board bring-up tuple, ILA-verified 2026-09-05"),
    "DFI_PHASE.wr_phase": dict(ships=0x0, note="board bring-up tuple, ILA-verified 2026-09-05"),

    "INIT_TIMING0.t_dll_wait": dict(ships=0x0100, note="DDR2 DLL lock, 200 CK at the shipping clock"),
    "INIT_TIMING0.t_init_wait": dict(ships=0x0200, note="power-on wait"),
    "INIT_TIMING1.t_mrd_wait": dict(ships=0x08, note="tMRD; asserted by the init JEDEC check (TASK-016)"),
    "INIT_TIMING1.t_rfc_wait": dict(ships=0x10, note="tRFC during init; asserted by the init JEDEC check"),
    "INIT_TIMING1.t_rp_wait": dict(ships=0x08, note="tRP during init; asserted by the init JEDEC check"),
    "INIT_TUNING.init_timeout_ms": dict(ships=0x0A, note="10 ms init watchdog"),
    "INIT_TUNING.zq_retries": dict(ships=0x3, note="LPDDR2 ZQ calibration retries; inert on DDR2"),

    "MR0.VAL": dict(
        waived="Same class as DFI_PHASE.gear_ratio: the reset 0x0433 is not what the "
               "board runs. DDR2CharDriver.BOARD_MR0 is 0x0432 (BL4/CL3/tWR3) and is "
               "re-written by program_geometry after every soft_reset, then the MRS "
               "chain is restarted (init_force_restart) so the DRAM takes it. "
               "pumice ISSUE-016."),
    "MR1.VAL": dict(ships=0x0000, note="MR1 all-zero is correct for this part"),
    "MR2.VAL": dict(ships=0x0000, note="MR2 is 0 on DDR2"),
    "MR3.VAL": dict(ships=0x0000, note="MR3 is 0 on DDR2"),

    "PASR_BANK_MASK_RANK0.pasr_banks": dict(ships=0x00, note="partial-array self-refresh off; all banks retained"),
    "PASR_SEG_MASK_RANK0.pasr_segs": dict(ships=0x00, note="PASR segment mask unused while PASR is off"),

    "PHY_TIMING.memtype": dict(ships=0x0, note="0 = DDR2, the only part on this board"),
    "PHY_TIMING.refresh_burst": dict(ships=0x1, note="one REF per interval; burst refresh unused"),
    "PHY_TIMING.t_phy_wrlat": dict(
        ships=0x1,
        note="BOTH board host paths program 1 -- pumice_master.SimpleTest (what "
             "`init` uses) and pumice_char.ControllerConfig. The reset was 0x00, "
             "agreeing with neither; this entry is what caught that, and the reset "
             "was changed to 1 rather than the divergence waived.",
    ),
    "PHY_TIMING.t_rddata_en": dict(
        ships=0x6,
        note="Follows `init`: pumice_master.SimpleTest programs t_rddata_en=6 with "
             "rddata_delay=7, the ILA-validated tuple. pumice_char.ControllerConfig "
             "programs 1 with rddata_delay=2 -- a different valid point on the "
             "measured diagonal rddata_delay = t_rddata_en + 1, because the "
             "a7ddrphy data-vs-valid offset is a fixed 1 cycle. Two host paths "
             "disagreeing is pumice ISSUE-015; the reset follows the bring-up "
             "authority. I briefly changed this reset to 1 on the strength of "
             "ControllerConfig alone, before reading what `init` actually programs "
             "-- one host default is not evidence of the shipping value.",
    ),

    "REFRESH_TUNING.page_policy_or": dict(ships=0x0, note="refresh does not override the page policy"),
    "REF_CTRL.mode": dict(ships=0x0, note="all-bank refresh; per-bank refresh is a DDR3/LPDDR3 path"),
    "REF_CTRL.postpone_limit": dict(ships=0x0, note="no refresh postponement; TASK-002 measured tREFI as the only tunable that pays"),
    "REF_CTRL.pullin_limit": dict(ships=0x0, note="no refresh pull-in, same measurement"),
    "REF_TIMING_PB.trefi_pb": dict(ships=0x0000, note="per-bank refresh interval; unused while REF_CTRL.mode=0"),
    "REF_TIMING_PB.trfc_pb": dict(ships=0x00, note="per-bank tRFC; unused while REF_CTRL.mode=0"),

    "SCHED_POLICY.order_mode": dict(ships=0x0, note="FR-FCFS. TASK-002 measured reordering worth 3.9x, so this is the shipping choice"),
    "SCHED_POLICY.prio_sub": dict(ships=0x0, note="no sub-priority within a pick"),
    "SCHED_POLICY.row_sel": dict(ships=0x0, note="default row selector"),
    "SCHED_POLICY.col_sel": dict(ships=0x0, note="default column selector"),
    "SCHED_POLICY.access_pref": dict(ships=0x0, note="no read/write preference"),
    "SCHED_POLICY.qos_en": dict(ships=0x0, note="QoS off; mechanisms complete (TASK-001) but not in the shipping config"),
    "SCHED_POLICY.age_thresh": dict(ships=0x00, note="unused while order_mode != age_threshold"),

    "SCHED_WR_WM.wr_batch_max": dict(ships=0x10, note="16-command write batch; TASK-007 measured +12.2% bus"),
    "SCHED_WR_WM.wr_high_wm": dict(ships=0x02, note="matches pumice_char TEST_WR_HIGH_WM default"),
    "SCHED_WR_WM.wr_low_wm": dict(ships=0x01, note="matches pumice_char TEST_WR_LOW_WM default"),

    # JEDEC timings. All twelve named operating points in pumice_dram_configs.py
    # derive these, so DV does run other values -- but the RESET set is the board
    # part (MT47H64M16 at DDR2-300 CL3) and that is what ships.
    "TIMINGS_CL_CWL_WR.CL": dict(ships=0x06, note="CL in MC cycles at 75 MHz, board part"),
    "TIMINGS_CL_CWL_WR.CWL": dict(ships=0x04, note="CWL in MC cycles, board part"),
    "TIMINGS_CL_CWL_WR.tWR": dict(ships=0x0F, note="tWR; anchor corrected in the timing-derivation fix"),
    "TIMINGS_CL_CWL_WR.tRFCpb": dict(ships=0x46, note="per-bank tRFC; unused while REF_CTRL.mode=0"),
    "TIMINGS_RC_RCD_RP_RAS.tRC": dict(ships=0x3C, note="board part at 75 MHz"),
    "TIMINGS_RC_RCD_RP_RAS.tRCD": dict(ships=0x0F, note="board part at 75 MHz"),
    "TIMINGS_RC_RCD_RP_RAS.tRP": dict(ships=0x0F, note="board part at 75 MHz"),
    "TIMINGS_RC_RCD_RP_RAS.tRAS": dict(ships=0x28, note="board part at 75 MHz"),
    "TIMINGS_RFC_REFI.tREFI": dict(ships=0x079E, note="7.8 us at 75 MHz; TASK-002: the only refresh tunable that pays"),
    "TIMINGS_RFC_REFI.tRFC": dict(ships=0x0010, note="board part at 75 MHz"),
    "TIMINGS_RRD_FAW_WTR_CCD.tRRD": dict(ships=0x06, note="board part"),
    "TIMINGS_RRD_FAW_WTR_CCD.tFAW": dict(ships=0x23, note="board part"),
    "TIMINGS_RRD_FAW_WTR_CCD.tWTR": dict(ships=0x04, note="board part"),
    "TIMINGS_RRD_FAW_WTR_CCD.tCCD": dict(
        ships=0x04,
        note="the board tCCD CSR was left unprogrammed once (pumice ISSUE-009 family) "
             "-- that is why this field is named here rather than left to a default.",
    ),
    "TIMINGS_RTP_RTW.tRTP": dict(ships=0x04, note="board part"),
    "TIMINGS_RTP_RTW.tRTW": dict(ships=0x06, note="derived from MEASURED DQ occupancy (BUG-014), not a formula"),

    # ---- LPDDR2 calibration / training --------------------------------------
    "CAL_CTRL.zq_en": dict(ships=0x0, note="ZQ periodic calibration disabled by default"),
    "CAL_CTRL.zq_defer_en": dict(ships=0x0, note="ZQ Mode-C deferral disabled by default"),
    "CAL_CTRL.zq_overdue_max": dict(ships=0x0, note="no ZQ overdue limit by default"),
    "CAL_ZQ_INTERVAL.VAL": dict(ships=0x0, note="ZQ interval 0 = disabled"),
    "CAL_ZQ_TIMING.t_zqcs": dict(ships=0x0, note="ZQCS hold disabled by default"),
    "CAL_ZQ_TIMING.t_zqcl": dict(ships=0x0, note="ZQCL hold disabled by default"),
    "CAL_TRAIN_TIMING.t_mrr": dict(ships=0x2, note="MRR-to-MRR spacing default = 2 MC cycles"),
    "CAL_TRAIN_TIMING.t_readout": dict(ships=0x0, note="MRR readout timeout disabled by default; programmed before cal_start"),

    # ---- waived: command strobes ---------------------------------------------
    "CTRL.init_start": dict(waived="write-1 command strobe, not configuration; reset 0 is the only correct reset"),
    "CAL_CTRL.cal_start": dict(waived="write-1 command strobe; self-clearing, not configuration"),
    "CAL_CTRL.cal_abort": dict(waived="write-1 command strobe; self-clearing, not configuration"),
    "CTRL.init_force_restart": dict(waived="write-1 command strobe"),
    "CTRL.soft_reset": dict(waived="write-1 command strobe; clears every instrument by design"),
    "CTRL.pwr_req_active": dict(waived="power-state request strobe"),
    "CTRL.pwr_req_low_power": dict(waived="power-state request strobe"),
    "CTRL.pwr_req_self_refresh": dict(waived="power-state request strobe"),
    "CTRL.pwr_req_dpd": dict(waived="power-state request strobe (deep power down)"),
}

# OBS_ROW_HIT[8] used to appear here as eight sw=rw waivers ("write clears").
# They are sw=r now: pumice BUG-020 wired them and made them free-running like
# every other counter, because onread=rclr could never have worked against a
# field the hardware drives every cycle. Not software-writable, so out of this
# gate's scope -- this gate is about configuration nobody decided about.
