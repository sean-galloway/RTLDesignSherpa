# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""RAPIDS test-level DEPTH profile.

The grid (which cells a REG_LEVEL expands to) and the per-cell environment
live in ``TBClasses.shared.test_levels`` -- one implementation for every area,
and the one place that guarantees a wrapper's TEST_LEVEL beats a conftest
stamp (see that module for why cocotb_test makes that necessary). This file
holds only what is specific to RAPIDS: how much work each depth does.

Before 2026-09-27 (tooling BUG-004, was TOOL-016) every rapids wrapper carried
its own ``_depth()`` table and exported the PROCESS TEST_LEVEL, which the five
conftests stamped to REG_LEVEL -- so every cell of a FULL run ran at full depth
and every cell of a GATE run at gate depth, and the per-file tables were seven
sources of truth. The numbers below are those tables, moved, not changed: each
``func`` entry is what the file used before, so gate and full bracket the old
coverage rather than redefining it.
"""
import os

from TBClasses.shared.test_levels import LEVELS, current_level, level_env, reg_level_grid  # noqa: F401

PROFILE = {
    'gate': dict(
        ctrlwr_ops=3,             # fub/test_ctrlwr_engine: back-to-back operations
        ctrlrd_ops=3,             # fub/test_ctrlrd_engine: back-to-back operations
        ctrlrd_retries=2,         #   ... and retries
        alloc_basic_ops=5,        # fub_beats/test_alloc_ctrl_beats
        alloc_stress_ops=25,
        drain_basic_ops=5,        # fub_beats/test_drain_ctrl_beats
        drain_stress_ops=25,
        sched_descriptors=3,      # fub_beats/test_scheduler_beats: basic flow
        sched_back_to_back=5,     #   ... back-to-back descriptors
        desceng_basic=3,          # fub_beats/test_descriptor_engine_beats: basic flow
        desceng_rapid=10,         #   ... rapid flow
        top_beats=4,              # top_beats/*: beats per transfer
        # macro_beats (func = the literal each test used before; gate/full bracket it)
        sg_descriptors=2,         # test_scheduler_group_beats: basic descriptor flow
        sga_arb_ops=4,            # test_scheduler_group_array_beats: AXI arbitration operations
        sga_desc_per_ch=1,        #   ... descriptors per channel, sequential sweep
        sga_stress_ops=5,         #   ... stress operations
        sram_fill_count=5,        # test_{snk,src}_sram_controller_beats: fill/drain count
        sram_ops_per_ch=2,        #   ... per-channel operations
        dp_descriptors=4,         # test_{snk,src}_data_path_axis_test_beats: basic descriptors
        dp_desc_per_ch=1,         #   ... descriptors per channel
        dp_packets=8,             #   ... AXIS packets
        dp_ops=6,                 #   ... AXI operations
        dp_transfers=4,           #   ... end-to-end transfers
        dp_stress_ops=16,         #   ... stress operations
        # fub_beats AXI engines (the TBs' own table, moved here): (small, large) beat counts
        axi_engine_beats=(16, 32),
    ),
    'func': dict(
        ctrlwr_ops=5, ctrlrd_ops=5, ctrlrd_retries=3,
        alloc_basic_ops=10, alloc_stress_ops=50,
        drain_basic_ops=10, drain_stress_ops=50,
        sched_descriptors=5, sched_back_to_back=10,
        desceng_basic=5, desceng_rapid=20,
        top_beats=16,
        sg_descriptors=3, sga_arb_ops=8, sga_desc_per_ch=1, sga_stress_ops=10,
        sram_fill_count=10, sram_ops_per_ch=3,
        dp_descriptors=8, dp_desc_per_ch=2, dp_packets=16, dp_ops=12, dp_transfers=8, dp_stress_ops=32,
        axi_engine_beats=(32, 96),
    ),
    'full': dict(
        ctrlwr_ops=12, ctrlrd_ops=12, ctrlrd_retries=5,
        alloc_basic_ops=25, alloc_stress_ops=200,
        drain_basic_ops=25, drain_stress_ops=200,
        sched_descriptors=12, sched_back_to_back=30,
        desceng_basic=12, desceng_rapid=60,
        top_beats=32,
        sg_descriptors=12, sga_arb_ops=16, sga_desc_per_ch=2, sga_stress_ops=30,
        sram_fill_count=25, sram_ops_per_ch=6,
        dp_descriptors=16, dp_desc_per_ch=4, dp_packets=32, dp_ops=24, dp_transfers=16, dp_stress_ops=64,
        axi_engine_beats=(64, 120),
    ),
}


def depth(knob):
    """The value of one PROFILE knob at the depth this cocotb process runs at.

    Reads TEST_LEVEL here rather than through current_level() so the level
    checker (bin/review/check_test_levels.py), which follows a test's own
    tbclasses imports one level deep and looks for the os.environ read, sees
    where the depth is consumed. Same semantics as current_level().
    """
    lvl = os.environ.get('TEST_LEVEL', 'gate').lower()
    return PROFILE[lvl if lvl in PROFILE else 'gate'][knob]
