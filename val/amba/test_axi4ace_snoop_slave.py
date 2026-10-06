# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axi4ace_snoop_slave
# Purpose: ACE cache-side snoop transport validation
#
# Subsystem: tests

"""ACE cache-side snoop transport test runner.

Tests ``axi4ace_snoop_slave`` with a BFM master on the AXI side
(``m_axi_``) and a BFM responder on the FUB side (``fub_``).

TEST LEVELS (per-test depth):
    gate  - quick smoke (MESI matrix + short in-order sequence)
    func  - functional (full matrix, longer sequence, CR/CD backpressure)
    full  - regression stress (matrix×2, long sequence, deep backpressure, stress mix)

REG_LEVEL Control (parameter combinations):
    GATE: 1 test  - (addr 32, data 32, ac 2, cr 4, cd 4, 'gate')
    FUNC: 4 tests - depths (2,4,4) and (4,8,8) × levels gate/func
    FULL: 24 tests - addr {32,64} × data {32,64} × depths {(2,4,4),(4,8,8)}
                     × levels {gate,func,full}

Environment Variables:
    REG_LEVEL: GATE|FUNC|FULL - controls parameter combinations (default: FUNC)
    TEST_LEVEL: basic|medium|full - per-test depth (set by REG_LEVEL in grid)
    SEED: Set random seed for reproducibility
"""

import os
import random
from itertools import product

import cocotb
import pytest
from cocotb_test.simulator import run
from TBClasses.ace.ace_snoop_transport_tb import AXI4ACESnoopTransportTB
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import create_view_cmd, get_paths, sim_build_path


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def axi4ace_snoop_slave_test(dut):
    """ACE snoop slave transport test: master on m_axi_, responder on fub_."""

    test_level = os.environ.get('TEST_LEVEL', 'gate').lower()
    addr_width = int(os.environ.get('TEST_ADDR_WIDTH', '32'))
    data_width = int(os.environ.get('TEST_DATA_WIDTH', '32'))

    tb = AXI4ACESnoopTransportTB(
        dut,
        aclk=dut.aclk,
        aresetn=dut.aresetn,
        master_prefix="m_axi_",
        slave_prefix="fub_",
        addr_width=addr_width,
        data_width=data_width,
    )

    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f"ACE snoop slave transport test starting with SEED={seed}, level={test_level}")

    await tb.start_clock('aclk', tb.TEST_CLK_PERIOD, 'ns')
    await tb.assert_reset()
    await tb.wait_clocks('aclk', 10)
    await tb.deassert_reset()
    await tb.wait_clocks('aclk', 10)

    tb.log.info(f"Starting {test_level.upper()} ACE snoop slave transport test...")

    await tb.run_scenarios(test_level)

    tb.log.info(f"ALL {test_level.upper()} ACE SNOOP SLAVE TRANSPORT TESTS PASSED!")


def validate_params(params):
    """Validate generated parameter combinations."""
    for param in params:
        addr_w, data_w, ac_d, cr_d, cd_d, _level = param
        if addr_w > 64:
            raise ValueError(f"addr_width={addr_w} exceeds maximum of 64-bits: {param}")
        if data_w not in (32, 64):
            raise ValueError(f"data_width={data_w} not supported (use 32 or 64): {param}")
        if ac_d < 1 or cr_d < 1 or cd_d < 1:
            raise ValueError(f"skid depths must be positive: {param}")
    return params


def generate_params():
    """Generate parameter combinations based on REG_LEVEL.

    Returns:
        List of (addr_width, data_width, ac_depth, cr_depth, cd_depth, test_level).
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        params = [(32, 32, 2, 4, 4, 'gate')]
        return validate_params(params)

    if reg_level == 'FUNC':
        params = []
        for ac_d, cr_d, cd_d in [(2, 4, 4), (4, 8, 8)]:
            for level in ('gate', 'func'):
                params.append((32, 32, ac_d, cr_d, cd_d, level))
        return validate_params(params)

    # FULL
    params = []
    for addr_w, data_w, (ac_d, cr_d, cd_d), level in product(
        (32, 64), (32, 64), [(2, 4, 4), (4, 8, 8)], ('gate', 'func', 'full')
    ):
        params.append((addr_w, data_w, ac_d, cr_d, cd_d, level))
    return validate_params(params)


@pytest.mark.parametrize(
    "addr_width, data_width, ac_depth, cr_depth, cd_depth, test_level",
    generate_params()
)
def test_axi4ace_snoop_slave(request, addr_width, data_width, ac_depth, cr_depth,
                             cd_depth, test_level):
    """Run the ACE snoop slave transport across the REG_LEVEL parameter grid."""

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    dut_name = "axi4ace_snoop_slave"

    module, repo_root, tests_dir, log_dir, _rtl_dict = get_paths({
        'rtl_amba': 'rtl/amba',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 3)
    acd_str = TBBase.format_dec(ac_depth, 1)
    crd_str = TBBase.format_dec(cr_depth, 1)
    cdd_str = TBBase.format_dec(cd_depth, 1)
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()

    test_name_plus_params = (
        f"test_{worker_id}_{dut_name}_a{aw_str}_d{dw_str}_"
        f"ac{acd_str}_cr{crd_str}_cd{cdd_str}_{test_level}_{reg_level}"
    )

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f'rtl/amba/filelists/{dut_name}.f',
    )

    ac_size = addr_width + 4 + 3
    cr_size = 5
    cd_size = data_width + 1

    rtl_parameters = {
        'SKID_DEPTH_AC': str(ac_depth),
        'SKID_DEPTH_CR': str(cr_depth),
        'SKID_DEPTH_CD': str(cd_depth),
        'ADDR_WIDTH': str(addr_width),
        'DATA_WIDTH': str(data_width),
        'AW': str(addr_width),
        'DW': str(data_width),
        'ACSize': str(ac_size),
        'CRSize': str(cr_size),
        'CDSize': str(cd_size),
    }

    timeout_multipliers = {'gate': 1, 'func': 2, 'full': 4}
    complexity_factor = (data_width + addr_width) / 100.0
    timeout_ms = int(
        5000 * timeout_multipliers.get(test_level, 1) * max(1.0, complexity_factor)
    )

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
        'TEST_LEVEL': test_level,
        'COCOTB_TEST_TIMEOUT': str(timeout_ms),

        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_CLK_PERIOD': str(10),
        'ACE_COMPLIANCE_CHECK': '1',
    }

    compile_args = [
        "--trace",
        "--trace-depth", "99",
        "-Wall",
        "-Wno-SYNCASYNCNET",
        "-DUSE_ASYNC_RESET",
        "-Wno-UNUSED",
        "-Wno-DECLFILENAME",
    ]

    sim_args = ["--trace", "--trace-depth", "99"]
    plus_args = ["--trace"]

    cmd_filename = create_view_cmd(
        os.path.dirname(log_path), log_path, sim_build, module, test_name_plus_params
    )

    print(f"\n{'='*80}")
    print(f"Running {test_level.upper()} ACE snoop slave transport test: {dut_name}")
    print(f"Config: ADDR={addr_width}, DATA={data_width}, "
          f"AC={ac_depth}, CR={cr_depth}, CD={cd_depth}")
    print(f"Expected duration: {timeout_ms/1000:.1f}s")
    print(f"{'='*80}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plus_args=plus_args,
        )
        print(f"{test_level.upper()} ACE snoop slave transport test PASSED")
    except Exception as e:
        print(f"{test_level.upper()} ACE snoop slave transport test FAILED: {e!s}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
