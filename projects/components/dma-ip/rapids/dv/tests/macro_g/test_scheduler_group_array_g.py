# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_scheduler_group_array_g
# Purpose: rapids-g (rapids TASK-034): the product scheduler_group_array tests,
#          unchanged, against scheduler_group_array_g -- the same ports, its
#          schedulers sequenced by one gatling.
#
# Documentation: projects/components/dma-ip/rapids/PRD.md (rapids-g)
# Subsystem: rapids macro_g
#
# Author: sean galloway
# Created: 2026-10-21

"""rapids-g scheduler array: the product macro suite on the -g module.

The cocotb tests are the product's (dv/tests/macro/test_scheduler_group_array.py),
loaded by module name; only the DUT, its filelist and the channel counts differ.
rapids-g runs 4 or 8 channels on one gatling, so every product configuration
also runs at 4 channels.
"""

import os
import sys

import pytest
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

repo_root = get_repo_root()
sys.path.insert(0, repo_root)
_PRODUCT_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', 'macro'))
sys.path.insert(0, _PRODUCT_DIR)

import test_scheduler_group_array as product  # noqa: E402

PRODUCT_MODULE = 'test_scheduler_group_array'
DUT = 'scheduler_group_array_g'
FILELIST = 'projects/components/dma-ip/rapids/rtl/filelists/macro_g/scheduler_group_array_g.f'

# The TB's floor on a wait for a scheduler reaction: firmware takes a few
# hundred cycles per step (scheduler_group_array_tb.SCHED_WAIT_FLOOR)
SCHED_WAIT_FLOOR = 4000

# Every cocotb test of the product suite
CASES = [
    'single_channel',
    'ctrl_multi_channel_doorbell',
    'ctrl_multi_channel_gate',
    'ctrl_error_handoff',
    'multi_channel_concurrent',
    'axi_arbitration',
    'all_channels_sequential',
    'monbus_aggregation',
    'stress',
]


def _g_params():
    params = list(product.scheduler_group_array_params)
    params += [(4,) + p[1:] for p in product.scheduler_group_array_params
               if p[0] == 8 and p[4] == 'default']
    return params


def _run(request, case, num_channels, addr_width, data_width, axi_id_width, timing_profile, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=FILELIST)

    name = (f"test_{DUT}_{case}_nc{TBBase.format_dec(num_channels, 2)}_aw{TBBase.format_dec(addr_width, 2)}"
            f"_dw{TBBase.format_dec(data_width, 3)}_id{TBBase.format_dec(axi_id_width, 2)}"
            f"_{timing_profile}_{test_level}")
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        name = f"{name}_{worker_id}"
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        'LOG_PATH': log_path,
        'TRACE_FILE': os.path.join(sim_build, 'dump.fst'),
        'VERILATOR_TRACE': '1',
        'DUT': DUT,
        'COCOTB_LOG_LEVEL': 'INFO',
        **level_env(test_level),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_AXI_ID_WIDTH': str(axi_id_width),
        **({'GAXI_TIMING_PROFILE': timing_profile} if timing_profile != 'default' else {}),
        'CHANNEL_COUNT': str(num_channels),
        'SCHED_WAIT_FLOOR': str(SCHED_WAIT_FLOOR),
    }
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, name)
    try:
        run(
            python_search=[_PRODUCT_DIR, tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=DUT,
            module=PRODUCT_MODULE,
            testcase=f"cocotb_test_{case}",
            parameters={'NUM_CHANNELS': num_channels, 'ADDR_WIDTH': addr_width,
                        'DATA_WIDTH': data_width, 'AXI_ID_WIDTH': axi_id_width},
            simulator="verilator",
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,
            keep_files=True,
            compile_args=["-Wno-TIMESCALEMOD", "-Wno-WIDTH", "-Wno-UNOPTFLAT", "-Wno-SELRANGE"],
            plus_args=['--trace'] if enable_waves else [],
        )
    except Exception:
        print(f"Logs: {log_path}")
        if os.path.exists(cmd_filename):
            print(f"View command: {cmd_filename}")
        raise


@pytest.mark.macro
@pytest.mark.rapids_g
@pytest.mark.scheduler_group_array
@pytest.mark.parametrize("case", CASES)
@pytest.mark.parametrize("num_channels, addr_width, data_width, axi_id_width, timing_profile", _g_params())
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_scheduler_group_array_g(request, case, num_channels, addr_width, data_width, axi_id_width,
                                 timing_profile, test_level):
    """The product scheduler_group_array test `case` on scheduler_group_array_g."""
    _run(request, case, num_channels, addr_width, data_width, axi_id_width, timing_profile, test_level)
