# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_alu_infer
# Purpose: Test runner for the ALU-INFER bf16 inference ALU
# Documentation: projects/components/compute-eng-ip/alu-infer/docs/alu_infer_mas
# Subsystem: alu-infer
#
# Author: sean galloway
# Created: 2026-10-17
# Updated: 2026-10-20 - Refactored to the repository standard pattern (stream
#          area): single cocotb test dispatching on TEST_TYPE, all stimulus
#          and checking in the AluInferTB testbench class (GAXI BFMs on both
#          valid/ready interfaces), single parameter generator, single fully
#          parametrized pytest wrapper.

"""
Test runner for the alu_infer_top module.

STRUCTURE FOLLOWS REPOSITORY STANDARD:
  - Single CocoTB test function (dispatches based on TEST_TYPE)
  - Single parameter generator (includes test_type as first parameter)
  - Single pytest wrapper (fully parametrized)

All handshake traffic goes through the RDS-DV GAXI BFMs: a GAXIMaster owns the
issue interface (valid/ready + op/func fields), a GAXISlave owns the result
interface (result_valid/result_ready + line/flags), and passive GAXIMonitors
record completed transfers on both.  See dv/tbclasses/alu_infer_tb.py.

Test types (TEST_TYPE env): copy_timing, add_sub, mul, minmax, compare, relu,
mac, backpressure, error_opcode, special_grid, mixed_soak, sub_ulp_corner,
tag_join.
"""

import os
import sys
import random
import pytest
import cocotb

from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_repo_root, sim_build_path, create_view_cmd
from TBClasses.shared.test_levels import level_env, reg_level_grid
from TBClasses.shared.filelist_utils import get_sources_from_filelist

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)

# Import testbench (dashed area dirs resolve through the projects.components shim)
from projects.components.compute_eng_ip.alu_infer.dv.tbclasses.alu_infer_tb import AluInferTB

# Coverage integration (the cov_utils base every component area shares)
from cov_utils.conftest_coverage import get_coverage_compile_args


#===============================================================================
# COCOTB TEST FUNCTION - Single test that handles all variants
#
# All stimulus + checking lives in AluInferTB, which drives the issue/result
# interfaces through GAXI BFMs.  This runner only dispatches by TEST_TYPE.
#===============================================================================

@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_alu_infer(dut):
    """Unified ALU-INFER test - handles all test types via TEST_TYPE env var."""
    test_type = os.environ.get('TEST_TYPE', 'copy_timing')

    tb = AluInferTB(dut)
    await tb.setup_clocks_and_reset()

    scenarios = {
        'copy_timing': tb.test_copy_timing,
        'add_sub': tb.test_add_sub,
        'mul': tb.test_mul,
        'minmax': tb.test_minmax,
        'compare': tb.test_compare,
        'relu': tb.test_relu,
        'mac': tb.test_mac,
        'backpressure': tb.test_backpressure,
        'error_opcode': tb.test_error_opcode,
        'special_grid': tb.test_special_grid,
        'mixed_soak': tb.test_mixed_soak,
        'sub_ulp_corner': tb.test_sub_ulp_corner,
        'tag_join': tb.test_tag_join,
    }
    if test_type not in scenarios:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")

    await scenarios[test_type]()
    tb.log_monitor_stats()


#===============================================================================
# PARAMETER GENERATION
#===============================================================================

TEST_TYPES = [
    'copy_timing', 'add_sub', 'mul', 'minmax', 'compare', 'relu', 'mac',
    'backpressure', 'error_opcode', 'special_grid', 'mixed_soak',
    'sub_ulp_corner', 'tag_join',
]


def generate_params():
    """
    Generate parameters for ALU-INFER tests based on REG_LEVEL.

    GATE/FUNC/FULL: every test type at PIPE_DEPTH {4, 8} (default profile =
    'backtoback', zero-delay valid/ready).
    FUNC and FULL sweep the mixed soak across the standard delay profiles from
    GAXI_RANDOMIZER_CONFIGS (bin/TBClasses/amba/amba_random_configs.py) -- the
    elastic pipeline under randomized valid/ready timing:

      FUNC: fast, slow_producer, slow_consumer, gaxi_realistic,
            gaxi_backpressure
      FULL adds: constrained, burst_pause, high_throughput, gaxi_stress

    Returns:
        List of tuples: (test_type, pipe_depth, timing_profile)
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    pipe_depths = ['4', '8']
    params = [(t, pd, 'default') for t in TEST_TYPES for pd in pipe_depths]

    if reg_level in ('FUNC', 'FULL'):
        for profile in ['fast', 'slow_producer', 'slow_consumer',
                        'gaxi_realistic', 'gaxi_backpressure']:
            params.append(('mixed_soak', '8', profile))
    if reg_level == 'FULL':
        for profile in ['constrained', 'burst_pause', 'high_throughput',
                        'gaxi_stress']:
            params.append(('mixed_soak', '8', profile))

    return params


params = generate_params()


#===============================================================================
# PYTEST WRAPPER FUNCTION - Single wrapper for all test types
#===============================================================================

@pytest.mark.parametrize("test_type, pipe_depth, timing_profile", params)
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_alu_infer(request, test_type, test_level, pipe_depth, timing_profile):
    """Pytest wrapper for ALU-INFER tests - handles all test types."""
    enable_waves = bool(int(os.environ.get('WAVES', '0')))

    module = os.path.splitext(os.path.basename(__file__))[0]
    tests_dir = os.path.dirname(__file__)
    log_dir = os.path.join(tests_dir, 'logs')
    os.makedirs(log_dir, exist_ok=True)

    # Format parameters for a unique test name (xdist compatibility)
    test_name = f'{module}_{test_type}_{test_level}_pd{pipe_depth}_{timing_profile}'
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name = f'{test_name}_{worker_id}'

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/compute-eng-ip/alu-infer/rtl/filelists/alu_infer_top.f')

    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)

    log_path = os.path.join(log_dir, f'{test_name}.log')
    results_path = os.path.join(log_dir, f'results_{test_name}.xml')

    extra_env = {
        'TEST_TYPE': test_type,  # ← Pass test type to cocotb
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
        # Per-cell depth. REG_LEVEL already selects this file's grid; this is
        # the other half -- the depth the TB runs each cell at.
        **level_env(test_level),
    }
    if timing_profile != 'default':
        extra_env['GAXI_TIMING_PROFILE'] = timing_profile

    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
        "--no-timing",
        "-Wno-TIMESCALEMOD",
        "-Wno-WIDTHEXPAND",
        "-Wno-WIDTHTRUNC",
        "-Wno-PINCONNECTEMPTY",
        "-Wno-UNUSEDPARAM",
        "-Wno-UNUSEDSIGNAL",
    ]
    for inc in includes:
        compile_args.append(f"+incdir+{inc}")
    compile_args.extend(get_coverage_compile_args())

    # Create view command helper script
    create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    run(
        python_search=[tests_dir,
                       os.path.join(repo_root,
                                    'projects/components/compute-eng-ip/alu-infer/dv/tbclasses')],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel="alu_infer_top",
        module=module,
        testcase="cocotb_test_alu_infer",  # ← Single cocotb test
        simulator="verilator",
        compile_args=compile_args,
        sim_build=sim_build,
        work_dir=sim_build,
        results_xml=results_path,
        parameters={'PIPE_DEPTH': pipe_depth},
        extra_env=extra_env,
        waves=enable_waves,
        plus_args=['--trace'] if enable_waves else [],
    )

    print(f"ALU-INFER {test_type} [{test_level}, PIPE_DEPTH={pipe_depth}] completed! Logs: {log_path}")
