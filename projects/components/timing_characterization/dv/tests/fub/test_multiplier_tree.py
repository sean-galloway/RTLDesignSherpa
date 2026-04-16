"""
Test runner for multiplier_tree timing characterization FUB.

Verifies multiplication correctness across different MULT_TYPE
implementations (inferred, Dadda, Wallace, Wallace CSA, Dadda 4:2).
"""

import os
import sys
import random
import pytest
import cocotb
from cocotb.triggers import ClockCycles
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root
from TBClasses.shared.filelist_utils import get_sources_from_filelist

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.timing_characterization.dv.tbclasses.timing_char_tb import TimingCharTB


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_multiplier_tree(dut):
    """Functional test for multiplier_tree FUB."""
    tb = TimingCharTB(dut)
    await tb.setup_clocks_and_reset()

    width = int(dut.WIDTH.value)
    mask = (1 << width) - 1
    rng = random.Random(42)
    mismatches = 0

    for i in range(50):
        a = rng.randint(0, mask)
        b = rng.randint(0, mask)
        dut.i_data_a.value = a
        dut.i_data_b.value = b
        await ClockCycles(dut.clk, 3)

        expected = a * b
        got = int(dut.o_data.value)
        if got != expected:
            mismatches += 1
            dut._log.warning(f"Mismatch: {a} * {b} = {expected}, got {got}")

    assert mismatches == 0, f"multiplier_tree had {mismatches} mismatches out of 50 tests"
    dut._log.info("multiplier_tree: all 50 multiplication checks passed")


def generate_multiplier_tree_params():
    """Generate (mult_type, width) combinations.

    MULT_TYPE: 0=inferred, 1=dadda, 2=wallace, 3=wallace_csa, 4=dadda_4to2
    Structural multipliers have fixed width support:
      Dadda tree:   8, 16, 32
      Wallace tree: 8, 16, 32
      Wallace CSA:  8, 16, 32
      Dadda 4:2:    8, 11, 24
    """
    return [
        # (mult_type, width)
        (0, 8),      # Inferred 8-bit
        (0, 16),     # Inferred 16-bit
        (1, 8),      # Dadda tree 8-bit
        (1, 16),     # Dadda tree 16-bit
        (2, 8),      # Wallace tree 8-bit
        (2, 16),     # Wallace tree 16-bit
        (3, 8),      # Wallace CSA 8-bit
        (3, 16),     # Wallace CSA 16-bit
        (4, 8),      # Dadda 4:2 8-bit
        (4, 11),     # Dadda 4:2 11-bit
    ]


multiplier_tree_params = generate_multiplier_tree_params()

MULT_TYPE_NAMES = {0: 'inferred', 1: 'dadda', 2: 'wallace', 3: 'wallace_csa', 4: 'dadda_4to2'}


@pytest.mark.parametrize("mult_type, width", multiplier_tree_params)
def test_multiplier_tree(request, mult_type, width, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    """Pytest wrapper for multiplier_tree FUB test."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_fub': '../../../../rtl/fub',
    })

    dut_name = "multiplier_tree"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/timing_characterization/rtl/filelists/char_top.f'
    )

    mt_name = MULT_TYPE_NAMES.get(mult_type, str(mult_type))
    w_str = TBBase.format_dec(width, 3)
    test_name_plus_params = f"test_{dut_name}_{mt_name}_w{w_str}"

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {'MULT_TYPE': mult_type, 'WIDTH': width}

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{test_name_plus_params}.xml'),
        'SEED': str(random.randint(0, 100000)),
        'TEST_LEVEL': test_level,
    }

    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    compile_args = [
        "--trace", "--trace-structs", "--trace-depth", "99",
        "-Wno-TIMESCALEMOD", "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND",
    ]

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase="cocotb_test_multiplier_tree",
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            simulator="verilator",
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
            plus_args=['--trace'] if enable_waves else [],
        )
    except Exception as e:
        print(f"multiplier_tree test failed: {e}")
        print(f"Logs: {log_path}")
        raise
