# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Register definitions for the DDR2/LPDDR2 controller CSR slave.
# Mirrors rtl/macro/ddr2_lpddr2_csr.rdl.
#
# Format follows the HPET / stream pattern so it loads via
# bin/TBClasses/apb/register_map.RegisterMap:
#
#   reg_map = RegisterMap('ddr2_lpddr2_regmap.py',
#                         apb_data_width=32, apb_addr_width=12,
#                         start_address=0x0, log=logger)
#   reg_map.write('CTRL', 'pwr_req_low_power', 1)
#   cycles = reg_map.generate_apb_cycles()
#   for c in cycles:
#       await apb_master.busy_send(c)

"""Top-level RegisterMap dict for ddr2_lpddr2 CSR slave."""

top_block = {

    # ----- Control + Status -------------------------------------------------

    "CTRL": {
        "address": "0x000",
        "default": "0x00000000",
        "type": "reg", "size": 4, "sw": "rw",
        "name": "CTRL",
        "init_start":           {"offset": "0",     "default": "0x0", "sw": "rw", "type": "field"},
        "init_force_restart":   {"offset": "1",     "default": "0x0", "sw": "rw", "type": "field"},
        "pwr_req_low_power":    {"offset": "4",     "default": "0x0", "sw": "rw", "type": "field"},
        "pwr_req_dpd":          {"offset": "5",     "default": "0x0", "sw": "rw", "type": "field"},
        "pwr_req_active":       {"offset": "6",     "default": "0x0", "sw": "rw", "type": "field"},
        "pwr_req_self_refresh": {"offset": "7",     "default": "0x0", "sw": "rw", "type": "field"},
        "soft_reset":           {"offset": "31",    "default": "0x0", "sw": "rw", "type": "field"},
    },

    "STATUS": {
        "address": "0x004", "default": "0x00000000",
        "type": "reg", "size": 4, "sw": "ro",
        "name": "STATUS",
        "init_done":       {"offset": "0",     "default": "0x0", "sw": "ro", "type": "field"},
        "init_error":      {"offset": "1",     "default": "0x0", "sw": "ro", "type": "field"},
        "power_state":     {"offset": "7:4",   "default": "0x0", "sw": "ro", "type": "field"},
        "pasr_active":     {"offset": "8",     "default": "0x0", "sw": "ro", "type": "field"},
        "init_step_dbg":   {"offset": "23:16", "default": "0x0", "sw": "ro", "type": "field"},
        "version_match":   {"offset": "31",    "default": "0x0", "sw": "ro", "type": "field"},
    },

    "STATUS_HISTORY": {
        "address": "0x008", "default": "0x00000000",
        "type": "reg", "size": 4, "sw": "ro",
        "name": "STATUS_HISTORY",
        "history": {"offset": "31:0", "default": "0x0", "sw": "ro", "type": "field"},
    },

    # ----- Timing parameters ------------------------------------------------

    "TIMINGS_RC_RCD_RP_RAS": {
        "address": "0x010", "default": "0x281010_3C",
        "type": "reg", "size": 4, "sw": "rw",
        "name": "TIMINGS_RC_RCD_RP_RAS",
        "tRC":  {"offset": "7:0",   "default": "0x3C", "sw": "rw", "type": "field"},
        "tRCD": {"offset": "15:8",  "default": "0x0F", "sw": "rw", "type": "field"},
        "tRP":  {"offset": "23:16", "default": "0x0F", "sw": "rw", "type": "field"},
        "tRAS": {"offset": "31:24", "default": "0x28", "sw": "rw", "type": "field"},
    },

    "TIMINGS_RFC_REFI": {
        "address": "0x014", "default": "0x079E00C8",
        "type": "reg", "size": 4, "sw": "rw",
        "name": "TIMINGS_RFC_REFI",
        "tRFC":  {"offset": "15:0",  "default": "0x00C8", "sw": "rw", "type": "field"},
        "tREFI": {"offset": "31:16", "default": "0x079E", "sw": "rw", "type": "field"},
    },

    "TIMINGS_RRD_FAW_WTR_CCD": {
        "address": "0x018", "default": "0x04042306",
        "type": "reg", "size": 4, "sw": "rw",
        "name": "TIMINGS_RRD_FAW_WTR_CCD",
        "tRRD": {"offset": "7:0",   "default": "0x06", "sw": "rw", "type": "field"},
        "tFAW": {"offset": "15:8",  "default": "0x23", "sw": "rw", "type": "field"},
        "tWTR": {"offset": "23:16", "default": "0x04", "sw": "rw", "type": "field"},
        "tCCD": {"offset": "31:24", "default": "0x04", "sw": "rw", "type": "field"},
    },

    "TIMINGS_CL_CWL_WR": {
        "address": "0x01C", "default": "0x460F0406",
        "type": "reg", "size": 4, "sw": "rw",
        "name": "TIMINGS_CL_CWL_WR",
        "CL":     {"offset": "7:0",   "default": "0x06", "sw": "rw", "type": "field"},
        "CWL":    {"offset": "15:8",  "default": "0x04", "sw": "rw", "type": "field"},
        "tWR":    {"offset": "23:16", "default": "0x0F", "sw": "rw", "type": "field"},
        "tRFCpb": {"offset": "31:24", "default": "0x46", "sw": "rw", "type": "field"},
    },

    # ----- Mode registers ---------------------------------------------------

    "MR0": {
        "address": "0x020", "default": "0x00000000",
        "type": "reg", "size": 4, "sw": "rw",
        "name": "MR0",
        "VAL": {"offset": "15:0", "default": "0x0", "sw": "rw", "type": "field"},
    },
    "MR1": {
        "address": "0x024", "default": "0x00000000",
        "type": "reg", "size": 4, "sw": "rw",
        "name": "MR1",
        "VAL": {"offset": "15:0", "default": "0x0", "sw": "rw", "type": "field"},
    },
    "MR2": {
        "address": "0x028", "default": "0x00000000",
        "type": "reg", "size": 4, "sw": "rw",
        "name": "MR2",
        "VAL": {"offset": "15:0", "default": "0x0", "sw": "rw", "type": "field"},
    },
    "MR3": {
        "address": "0x02C", "default": "0x00000000",
        "type": "reg", "size": 4, "sw": "rw",
        "name": "MR3",
        "VAL": {"offset": "15:0", "default": "0x0", "sw": "rw", "type": "field"},
    },

    # ----- LPDDR2-specific --------------------------------------------------

    "PASR_BANK_MASK_RANK0": {
        "address": "0x030", "default": "0x00000000",
        "type": "reg", "size": 4, "sw": "rw",
        "name": "PASR_BANK_MASK_RANK0",
        "pasr_banks": {"offset": "7:0", "default": "0x0", "sw": "rw", "type": "field"},
    },
    "PASR_SEG_MASK_RANK0": {
        "address": "0x034", "default": "0x00000000",
        "type": "reg", "size": 4, "sw": "rw",
        "name": "PASR_SEG_MASK_RANK0",
        "pasr_segs": {"offset": "7:0", "default": "0x0", "sw": "rw", "type": "field"},
    },
    "TEMP_DERATE_RANK0": {
        "address": "0x038", "default": "0x00000000",
        "type": "reg", "size": 4, "sw": "ro",
        "name": "TEMP_DERATE_RANK0",
        "temp_class": {"offset": "1:0", "default": "0x0", "sw": "ro", "type": "field"},
    },

    # ----- Tuning -----------------------------------------------------------

    "SCHED_TUNING": {
        "address": "0x040", "default": "0x00000020",
        "type": "reg", "size": 4, "sw": "rw",
        "name": "SCHED_TUNING",
        "lookahead_active":     {"offset": "3:0",   "default": "0x0", "sw": "rw", "type": "field"},
        "force_inorder":        {"offset": "4",     "default": "0x0", "sw": "rw", "type": "field"},
        "happy_enable":         {"offset": "5",     "default": "0x1", "sw": "rw", "type": "field"},
        "age_max_runtime":      {"offset": "15:8",  "default": "0x0", "sw": "rw", "type": "field"},
        "txn_queue_high_water": {"offset": "23:16", "default": "0x0", "sw": "rw", "type": "field"},
        "lookahead_max_obs":    {"offset": "27:24", "default": "0x0", "sw": "ro", "type": "field"},
    },

    "PAGE_PRED_TUNING": {
        "address": "0x044", "default": "0x00020400",
        "type": "reg", "size": 4, "sw": "rw",
        "name": "PAGE_PRED_TUNING",
        "warmup_cycles": {"offset": "15:0",  "default": "0x0400", "sw": "rw", "type": "field"},
        "hysteresis":    {"offset": "23:16", "default": "0x02",   "sw": "rw", "type": "field"},
    },

    "REFRESH_TUNING": {
        "address": "0x048", "default": "0x00010010",
        "type": "reg", "size": 4, "sw": "rw",
        "name": "REFRESH_TUNING",
        "refpb_policy_or":      {"offset": "1:0",   "default": "0x0",    "sw": "rw", "type": "field"},
        "page_policy_or":       {"offset": "3:2",   "default": "0x0",    "sw": "rw", "type": "field"},
        "refresh_defer_active": {"offset": "7:4",   "default": "0x1",    "sw": "rw", "type": "field"},
        "zqcs_freq_hz":         {"offset": "31:16", "default": "0x0001", "sw": "rw", "type": "field"},
    },

    "ADDR_MAP_TUNING": {
        "address": "0x04C", "default": "0x00000000",
        "type": "reg", "size": 4, "sw": "rw",
        "name": "ADDR_MAP_TUNING",
        "scheme_or":      {"offset": "1:0", "default": "0x0", "sw": "rw", "type": "field"},
        "synth_mask_obs": {"offset": "7:4", "default": "0x0", "sw": "ro", "type": "field"},
    },

    "INIT_TUNING": {
        "address": "0x050", "default": "0x00000A03",
        "type": "reg", "size": 4, "sw": "rw",
        "name": "INIT_TUNING",
        "zq_retries":      {"offset": "3:0",  "default": "0x3",  "sw": "rw", "type": "field"},
        "init_timeout_ms": {"offset": "15:8", "default": "0x0A", "sw": "rw", "type": "field"},
    },

    # ----- Per-bank obs (rank 0, NUM_BANKS=8) -------------------------------
    #
    # NOTE: RegisterMap supports a 'count' attribute to expand an array. Each
    # OBS_ROW_HIT_BANK<N> register is at OBS_ROW_HIT_BASE + N * 4 = 0x080 + N*4.

    "OBS_ROW_HIT": {
        "address": "0x080", "default": "0x00000000",
        "type": "reg", "size": 4, "sw": "ro", "count": "8",
        "name": "OBS_ROW_HIT",
        "VAL": {"offset": "31:0", "default": "0x0", "sw": "ro", "type": "field"},
    },
    "OBS_REF_LATENCY": {
        "address": "0x0C0", "default": "0x00000000",
        "type": "reg", "size": 4, "sw": "ro", "count": "8",
        "name": "OBS_REF_LATENCY",
        "VAL": {"offset": "31:0", "default": "0x0", "sw": "ro", "type": "field"},
    },

    # ----- System obs -------------------------------------------------------

    "OBS_TXN_QUEUE_DEPTH_MAX": {
        "address": "0x100", "default": "0x00000000",
        "type": "reg", "size": 4, "sw": "ro", "name": "OBS_TXN_QUEUE_DEPTH_MAX",
        "VAL": {"offset": "31:0", "default": "0x0", "sw": "ro", "type": "field"},
    },
    "OBS_TXN_QUEUE_DEPTH_AVG": {
        "address": "0x104", "default": "0x00000000",
        "type": "reg", "size": 4, "sw": "ro", "name": "OBS_TXN_QUEUE_DEPTH_AVG",
        "VAL": {"offset": "31:0", "default": "0x0", "sw": "ro", "type": "field"},
    },
    "OBS_REFRESH_PENDING_MAX": {
        "address": "0x108", "default": "0x00000000",
        "type": "reg", "size": 4, "sw": "ro", "name": "OBS_REFRESH_PENDING_MAX",
        "VAL": {"offset": "31:0", "default": "0x0", "sw": "ro", "type": "field"},
    },

    # ----- obs_words harvest (9 RO words from #127) -------------------------

    "OBS_WORDS": {
        "address": "0x1C0", "default": "0x00000000",
        "type": "reg", "size": 4, "sw": "ro", "count": "9",
        "name": "OBS_WORDS",
        "VAL": {"offset": "31:0", "default": "0x0", "sw": "ro", "type": "field"},
    },

    # ----- ID / BUILD -------------------------------------------------------

    "ID": {
        "address": "0xFF0", "default": "0xD2020001",
        "type": "reg", "size": 4, "sw": "ro",
        "name": "ID",
        "version":   {"offset": "7:0",   "default": "0x01", "sw": "ro", "type": "field"},
        "memtype":   {"offset": "15:8",  "default": "0x00", "sw": "ro", "type": "field"},
        "n_phases":  {"offset": "23:16", "default": "0x02", "sw": "ro", "type": "field"},
        "module_id": {"offset": "31:24", "default": "0xD2", "sw": "ro", "type": "field"},
    },

    "BUILD": {
        "address": "0xFF4", "default": "0x00000000",
        "type": "reg", "size": 4, "sw": "ro",
        "name": "BUILD",
        "VAL": {"offset": "31:0", "default": "0x0", "sw": "ro", "type": "field"},
    },
}
