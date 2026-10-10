# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""pumice DDR2/LPDDR2 test-level DEPTH profile.

The grid (which cells a REG_LEVEL expands to) and the per-cell environment
live in ``TBClasses.shared.test_levels`` -- one implementation for every area,
and the one place that guarantees a wrapper's TEST_LEVEL beats a conftest
stamp (see that module for why cocotb_test makes that necessary). This file
holds only what is specific to pumice: how much work each depth does.

Before 2026-09-27 (tooling BUG-004, was TOOL-016) 23 pumice wrappers under
dv/tests/{fub,macro,phy,top} exported no level at all: they ran one cell per
test at a depth fixed by literals in the cocotb body, so ``make run-all-full``
and ``make run-all-gate`` did identical work there and reported the same green.
The numbers below route those literals through one table: each ``func`` entry
IS the literal the file used before, so gate and full bracket the old coverage
rather than redefining it. Knobs that sit at 1 for both gate and func are
single-scenario tests whose only scalable quantity is how many times the
self-checking scenario repeats; halving 1 is not possible, so only full grows.

Only PURE REPETITION is here -- counts where more iterations mean more
coverage and fewer mean less. Protocol and geometry constants (BL, DFI_RATE,
NUM_BANKS, widths, timing parameters, anything an RTL parameter or an exact
expectation is sized from) stay as literals in the tests.

Two of the four dv/tests areas that read this (phy, and macro's
test_pumice_cmd_stream_checker) are pure-python oracles with no simulator, so
there is no ``extra_env`` to carry the level; those wrappers put the same
``level_env()`` entries into the process environment via monkeypatch before
reading ``depth()``.
"""
import os

from TBClasses.shared.test_levels import LEVELS, current_level, level_env, reg_level_grid  # noqa: F401

PROFILE = {
    'gate': dict(
        # fub
        page_policy_acts=4,           # test_page_predictor: ACTs driven per mode before the AP verdict
        arbiter_issue_window=100,     # test_pumice_arbiter_issue_rate: cycles the fire rate is measured over
        bank_timers_col_reads=2,      # test_pumice_bank_timers: open-page column reads that must keep rdwr_ready
        cmd_arbiter_qos_repeats=1,    # test_pumice_cmd_arbiter: repeats of the QoS pick scenario (#16)
        dfi_cdc_items=12,             # test_pumice_dfi_cdc: items per stream across the async boundary
        dfi_cmd_path_seq_reps=1,      # test_pumice_dfi_cmd_path: repeats of the 6-op command sequence
        rd_aligner_paced_reads=2,     # test_pumice_dfi_rd_aligner: tCCD-paced reads (<= MAX_OUTSTANDING=8)
        wr_serializer_paced_writes=2, # test_pumice_dfi_wr_serializer: tCCD-paced single-word writes
        rd_cmd_cam_fill_rounds=1,     # test_pumice_rd_cmd_cam: fill-to-full / backpressure rounds
        rd_return_ring_wrap_mult=2,   # test_pumice_rd_return_ring: wrap run length as a multiple of DEPTH
        wr_data_cam_wave10_rounds=1,  # test_pumice_wr_data_cam: repeats of the WAVE10 pipelined drain
        wr_splitter_bursts=1,         # test_pumice_wr_splitter: host bursts per single/split scenario
        # macro
        axi4_ifc_rounds=1,            # test_pumice_axi4_layer: write/snarf/miss/commit rounds
        cmd_checker_legal_cols=1,     # test_pumice_cmd_stream_checker: columns in the legal open-page stream
        dfi_layer_roundtrips=1,       # test_pumice_dfi_layer: write-then-read round trips through the CDC
        sched_refresh_reads=40,       # test_pumice_scheduler_layer phase 5: reads under refresh pressure
        sched_mixed_pairs=15,         #   ... phase 6: concurrent wr+rd pairs
        sched_timeout_reps=2,         #   ... timeout_pre_vs_pending_column: reps per inter-read gap
        # phy (pure python)
        phy_bl4_txns=4,               # test_a7ddrphy_bl4_anchored: BL4 reads per proof (even)
        phy_gear_pairs=4,             # test_a7ddrphy_gear_mismatch: packed read pairs (file is skipped)
        phy_rdwin_offset_span=2,      # test_a7ddrphy_read_window: slot-offset sweep is range(-span, span+2)
        phy_wordcheck_clean_beats=1,  # test_axi_rd_device_word_check: clean beats in the all-clean stream
        # top
        core_roundtrips=1,            # test_pumice_core: AXI write -> DFI -> read-back rounds
        top_geared_bursts=2,          # test_pumice_top_geared: bursts per direction through the converters
    ),
    'func': dict(
        page_policy_acts=8, arbiter_issue_window=200, bank_timers_col_reads=4,
        cmd_arbiter_qos_repeats=1, dfi_cdc_items=24, dfi_cmd_path_seq_reps=1,
        rd_aligner_paced_reads=3, wr_serializer_paced_writes=3,
        rd_cmd_cam_fill_rounds=1, rd_return_ring_wrap_mult=3,
        wr_data_cam_wave10_rounds=1, wr_splitter_bursts=1,
        axi4_ifc_rounds=1, cmd_checker_legal_cols=2, dfi_layer_roundtrips=1,
        sched_refresh_reads=40, sched_mixed_pairs=30, sched_timeout_reps=3,
        phy_bl4_txns=8, phy_gear_pairs=8, phy_rdwin_offset_span=3, phy_wordcheck_clean_beats=2,
        core_roundtrips=1, top_geared_bursts=4,
    ),
    'full': dict(
        page_policy_acts=24, arbiter_issue_window=600, bank_timers_col_reads=12,
        cmd_arbiter_qos_repeats=3, dfi_cdc_items=72, dfi_cmd_path_seq_reps=3,
        rd_aligner_paced_reads=6, wr_serializer_paced_writes=6,
        rd_cmd_cam_fill_rounds=3, rd_return_ring_wrap_mult=6,
        wr_data_cam_wave10_rounds=3, wr_splitter_bursts=3,
        axi4_ifc_rounds=3, cmd_checker_legal_cols=6, dfi_layer_roundtrips=3,
        sched_refresh_reads=120, sched_mixed_pairs=90, sched_timeout_reps=8,
        phy_bl4_txns=24, phy_gear_pairs=24, phy_rdwin_offset_span=8, phy_wordcheck_clean_beats=6,
        core_roundtrips=3, top_geared_bursts=12,
    ),
}

assert PROFILE['gate'].keys() == PROFILE['func'].keys() == PROFILE['full'].keys(), \
    "every level must carry the same knob set"


def depth(knob):
    """The value of one PROFILE knob at the depth this cocotb process runs at.

    Reads TEST_LEVEL here rather than through current_level() so the level
    checker (bin/review/check_test_levels.py), which looks for the os.environ
    read, sees where the depth is consumed. Same semantics as current_level().
    """
    lvl = os.environ.get('TEST_LEVEL', 'gate').lower()
    return PROFILE[lvl if lvl in PROFILE else 'gate'][knob]
