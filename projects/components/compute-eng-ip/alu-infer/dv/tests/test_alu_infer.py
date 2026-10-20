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
tag_join (v1 bf16 rows); fmt_int8, fmt_fp32, fmt_fp8, const, act, cvt,
reduce, mac_formats, mac_chain, pwl, latency, softmax (element formats and the
roadmap/growth rows).

Build configs (BUILD_CFG, the last parametrize axis): default (RTL
defaults), deep (ADDER/MUL/MAC latencies 4/2/2), flat (every latency 0) and
lean (every EN_* off: the v1 bf16 ALU, everything else illegal).
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

@cocotb.test(timeout_time=50, timeout_unit="ms")
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
        'fmt_int8': tb.test_fmt_int8,
        'fmt_fp32': tb.test_fmt_fp32,
        'fmt_fp8': tb.test_fmt_fp8,
        'const': tb.test_const,
        'act': tb.test_act,
        'cvt': tb.test_cvt,
        'reduce': tb.test_reduce,
        'mac_formats': tb.test_mac_formats,
        'mac_chain': tb.test_mac_chain,
        'pwl': tb.test_pwl,
        'latency': tb.test_latency,
        'softmax': tb.test_softmax,
    }
    if test_type not in scenarios:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")

    await scenarios[test_type]()
    tb.log_monitor_stats()


#===============================================================================
# PARAMETER GENERATION
#===============================================================================

V1_TYPES = [
    'copy_timing', 'add_sub', 'mul', 'minmax', 'compare', 'relu', 'mac',
    'backpressure', 'error_opcode', 'special_grid', 'mixed_soak',
    'sub_ulp_corner', 'tag_join',
]
EXT_TYPES = [
    'fmt_int8', 'fmt_fp32', 'fmt_fp8', 'const', 'act', 'cvt', 'reduce',
    'mac_formats', 'mac_chain', 'pwl', 'latency', 'softmax',
]
TEST_TYPES = V1_TYPES + EXT_TYPES

# Build configurations: RTL parameter overrides per config name.
BUILD_CFGS = {
    'default': {},
    'deep': {'ADDER_LATENCY': '4', 'MUL_LATENCY': '2', 'MAC_LATENCY': '2'},
    'flat': {'ADDER_LATENCY': '0', 'MUL_LATENCY': '0', 'MAC_LATENCY': '0'},
    'lean': {'EN_INT8': '0', 'EN_FP32': '0', 'EN_FP8': '0', 'EN_REDUCE': '0',
             'EN_PWL': '0', 'EN_ACT': '0', 'EN_CVT': '0'},
}
# What each non-default config re-runs: the timing-sensitive scenarios for
# the latency configs, the v1 suite plus the illegal sweep for lean.
CFG_TYPES = {
    'deep': ['copy_timing', 'tag_join', 'latency', 'add_sub', 'mul', 'mac',
             'mac_chain', 'reduce', 'mac_formats', 'fmt_fp32', 'mixed_soak'],
    'flat': ['copy_timing', 'tag_join', 'latency', 'add_sub', 'mul', 'mac',
             'mac_chain', 'reduce', 'fmt_fp32', 'mixed_soak'],
    'lean': ['copy_timing', 'add_sub', 'mul', 'minmax', 'compare', 'relu', 'mac',
             'error_opcode', 'mixed_soak', 'tag_join', 'latency'],
}


def generate_params():
    """
    Generate parameters for ALU-INFER tests based on REG_LEVEL.

    GATE/FUNC/FULL: every test type at PIPE_DEPTH {4, 8} on the default build
    (default profile = 'backtoback', zero-delay valid/ready), plus each
    non-default build config's scenario list at PIPE_DEPTH 8.
    FUNC and FULL sweep the mixed soak across the standard delay profiles from
    GAXI_RANDOMIZER_CONFIGS (bin/TBClasses/amba/amba_random_configs.py) -- the
    elastic pipeline under randomized valid/ready timing:

      FUNC: fast, slow_producer, slow_consumer, gaxi_realistic,
            gaxi_backpressure
      FULL adds: constrained, burst_pause, high_throughput, gaxi_stress

    Returns:
        List of tuples: (test_type, pipe_depth, timing_profile, build_cfg)
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    pipe_depths = ['4', '8']
    params = [(t, pd, 'default', 'default') for t in TEST_TYPES for pd in pipe_depths]
    for cfg, types in CFG_TYPES.items():
        params += [(t, '8', 'default', cfg) for t in types]

    if reg_level in ('FUNC', 'FULL'):
        for profile in ['fast', 'slow_producer', 'slow_consumer',
                        'gaxi_realistic', 'gaxi_backpressure']:
            params.append(('mixed_soak', '8', profile, 'default'))
            params.append(('mixed_soak', '8', profile, 'deep'))
    if reg_level == 'FULL':
        for profile in ['constrained', 'burst_pause', 'high_throughput',
                        'gaxi_stress']:
            params.append(('mixed_soak', '8', profile, 'default'))

    return params


params = generate_params()


#===============================================================================
# PYTEST WRAPPER FUNCTION - Single wrapper for all test types
#===============================================================================

@pytest.mark.parametrize("test_type, pipe_depth, timing_profile, build_cfg", params)
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_alu_infer(request, test_type, test_level, pipe_depth, timing_profile, build_cfg):
    """Pytest wrapper for ALU-INFER tests - handles all test types."""
    enable_waves = bool(int(os.environ.get('WAVES', '0')))

    module = os.path.splitext(os.path.basename(__file__))[0]
    tests_dir = os.path.dirname(__file__)
    log_dir = os.path.join(tests_dir, 'logs')
    os.makedirs(log_dir, exist_ok=True)

    # Format parameters for a unique test name (xdist compatibility)
    test_name = f'{module}_{test_type}_{test_level}_pd{pipe_depth}_{timing_profile}_{build_cfg}'
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
        parameters={'PIPE_DEPTH': pipe_depth, **BUILD_CFGS[build_cfg]},
        extra_env=extra_env,
        waves=enable_waves,
        plus_args=['--trace'] if enable_waves else [],
    )

    print(f"ALU-INFER {test_type} [{test_level}, PIPE_DEPTH={pipe_depth}, {build_cfg}] "
          f"completed! Logs: {log_path}")
