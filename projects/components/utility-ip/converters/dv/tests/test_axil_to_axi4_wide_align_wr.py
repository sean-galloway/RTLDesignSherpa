# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_axil_to_axi4_wide_align_wr
# Purpose: Test runner for axil_to_axi4_wide_align_wr
#
# Testbench: projects/components/utility-ip/converters/dv/tbclasses/axil_to_axi4_wide_align_wr_tb.py

"""
axil_to_axi4_wide_align_wr: lane alignment, and a B held by the master while
the next write's B arrives (bridge BUG-025). One test per cocotb function;
the module has no level-dependent behaviour, so gate is the whole check.
"""

import os
import random
import sys

import cocotb
import pytest
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_repo_root, get_paths, sim_build_path

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.utility_ip.converters.dv.tbclasses.axil_to_axi4_wide_align_wr_tb import \
    AxilToAxi4WideAlignWrTB
from TBClasses.shared.filelist_utils import get_sources_from_filelist


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_lane_alignment(dut):
    tb = AxilToAxi4WideAlignWrTB(dut)
    await tb.setup_clocks_and_reset()
    assert await tb.lane_alignment(), "a narrow write landed on the wrong lanes"


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_b_backpressure(dut):
    tb = AxilToAxi4WideAlignWrTB(dut)
    await tb.setup_clocks_and_reset()
    assert await tb.b_backpressure(), "a B response was lost while the master held BREADY low"


def _run(testcase, s_width=32, m_width=64, id_width=2):
    module, repo_root, tests_dir, log_dir, _ = get_paths({
        'rtl_converters': 'projects/components/utility-ip/converters/rtl',
    })
    dut_name = 'axil_to_axi4_wide_align_wr'
    name = f'test_{dut_name}_{testcase}_s{s_width}_m{m_width}'
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f'projects/components/utility-ip/converters/rtl/filelists/{dut_name}.f')
    waves = bool(int(os.environ.get('WAVES', '0')))
    trace = ['--trace', '--trace-structs', '--trace-depth', '99']
    run(
        python_search=[tests_dir, repo_root],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase=f'cocotb_test_{testcase}',
        parameters={'S_AXI_DATA_WIDTH': str(s_width), 'M_AXI_DATA_WIDTH': str(m_width),
                    'AXI_ID_WIDTH': str(id_width), 'AXI_ADDR_WIDTH': '32',
                    'AXI_USER_WIDTH': '1'},
        simulator='verilator',
        sim_build=sim_build,
        extra_env={
            'LOG_PATH': os.path.join(log_dir, f'{name}.log'),
            'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{name}.xml'),
            'SEED': os.environ.get('SEED', str(random.randint(0, 1000000))),
            'S_AXI_DATA_WIDTH': str(s_width),
            'M_AXI_DATA_WIDTH': str(m_width),
            'AXI_ID_WIDTH': str(id_width),
            **({'COCOTB_TRACE_FILE': os.path.join(sim_build, 'dump.vcd')} if waves else {}),
        },
        waves=waves,
        keep_files=True,
        compile_args=trace,
        sim_args=trace,
        plus_args=['--trace'] if waves else [],
    )


@pytest.mark.parametrize("s_width, m_width", [(32, 64), (32, 128)])
def test_axil_to_axi4_wide_align_wr_lane_alignment(s_width, m_width):
    _run('lane_alignment', s_width, m_width)


@pytest.mark.parametrize("s_width, m_width", [(32, 64), (32, 128)])
def test_axil_to_axi4_wide_align_wr_b_backpressure(s_width, m_width):
    _run('b_backpressure', s_width, m_width)
