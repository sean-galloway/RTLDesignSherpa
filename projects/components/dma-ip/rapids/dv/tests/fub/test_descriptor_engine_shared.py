# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_descriptor_engine_shared
# Purpose: descriptor_engine_shared single-channel equivalence
#
# Documentation: projects/components/dma-ip/rapids/docs/rapids_mas/
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2026-10-16
"""descriptor_engine_shared, built with one channel, against every cocotb test of
test_descriptor_engine.py unchanged.

A one-channel shared engine has the per-channel engine's port names and widths,
so the same DescriptorEngineTB drives it. Passing proves the shared engine
reproduces descriptor_engine for one channel: kick policy, range refusal,
chaining, prefetch, error pulse, channel reset and MonBus events. Multi-channel
behaviour (round-robin issue, RID routing, concurrent fetches) is exercised by
the scheduler_group_array, rapids_core and top suites, which build with
SHARED_ENGINES=1.
"""

import os
import sys

import pytest

from TBClasses.shared.test_levels import reg_level_grid

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from test_descriptor_engine import _run_descriptor_engine_test  # noqa: E402

DUT = "descriptor_engine_shared"


def generate_descriptor_engine_shared_params():
    """(channel_id, num_channels, axi_id_width, timing_profile) by REG_LEVEL."""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    sweep = ['constrained', 'slow_producer', 'gaxi_realistic', 'gaxi_backpressure', 'gaxi_stress']
    if reg_level == 'GATE':
        sweep = []
    elif reg_level == 'FUNC':
        sweep = sweep[:3]
    return [(0, 1, 8, 'default')] + [(0, 1, 8, p) for p in sweep]


params = generate_descriptor_engine_shared_params()
COCOTB_TESTS = [
    "basic_descriptor_flow", "control_descriptor_decode", "descriptor_chaining",
    "address_range_validation", "channel_reset", "invalid_descriptor",
    "monitor_bus_events", "rapid_descriptors", "long_chain",
    "inject_owed_beat",     # shared-only: the injection port (INJ_EN)
]


@pytest.mark.fub
@pytest.mark.descriptor_engine_shared
@pytest.mark.parametrize("cocotb_test", COCOTB_TESTS)
@pytest.mark.parametrize("channel_id, num_channels, axi_id_width, timing_profile", params)
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_descriptor_engine_shared(request, cocotb_test, channel_id, num_channels, axi_id_width,
                                  timing_profile, test_level):
    """descriptor_engine_shared (NUM_CHANNELS=1) through one descriptor_engine cocotb test."""
    _run_descriptor_engine_test(request, f"cocotb_test_{cocotb_test}",
                                channel_id, num_channels, axi_id_width, timing_profile,
                                test_level=test_level, dut_name=DUT)
