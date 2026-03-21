"""
Test runner for carry_chain timing characterization FUB.

Verifies that the ripple-carry adder produces correct sums and
that the output toggles with changing inputs.
"""

import os
import sys
import random
import pytest
import cocotb
from cocotb.triggers import ClockCycles
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd, get_repo_root
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.timing_characterization.dv.tbclasses.timing_char_tb import TimingCharTB


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_carry_chain(dut):
    """Functional test for carry_chain FUB."""
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

        expected = a + b
        got = int(dut.o_data.value)
        if got != expected:
            mismatches += 1
            dut._log.warning(f"Mismatch: {a} + {b} = {expected}, got {got}")

    assert mismatches == 0, f"carry_chain had {mismatches} mismatches out of 50 tests"
    dut._log.info("carry_chain: all 50 addition checks passed")


def generate_carry_chain_params():
    return [8, 16, 32, 64]


carry_chain_params = generate_carry_chain_params()


@pytest.mark.parametrize("width", carry_chain_params)
def test_carry_chain(request, width, test_level):
    """Pytest wrapper for carry_chain FUB test."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_fub': '../../../../rtl/fub',
    })

    dut_name = "carry_chain"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/timing_characterization/rtl/filelists/char_top.f'
    )

    w_str = TBBase.format_dec(width, 3)
    test_name_plus_params = f"test_{dut_name}_w{w_str}"

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {'WIDTH': width}

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
            testcase="cocotb_test_carry_chain",
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            simulator="verilator",
            waves=False,
            keep_files=True,
            compile_args=compile_args,
        )
    except Exception as e:
        print(f"carry_chain test failed: {e}")
        print(f"Logs: {log_path}")
        raise
