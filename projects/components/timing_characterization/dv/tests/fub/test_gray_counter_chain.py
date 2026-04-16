"""
Test runner for gray_counter_chain timing characterization FUB.

Verifies that the Gray counter produces incrementing binary output
and valid Gray code output.
"""

import os
import sys
import random
import pytest
import cocotb
from cocotb.triggers import RisingEdge, ClockCycles
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root
from TBClasses.shared.filelist_utils import get_sources_from_filelist

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.timing_characterization.dv.tbclasses.timing_char_tb import TimingCharTB


def bin_to_gray(n):
    """Convert binary to Gray code."""
    return n ^ (n >> 1)


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_gray_counter_chain(dut):
    """Functional test for gray_counter_chain FUB."""
    tb = TimingCharTB(dut)
    await tb.setup_clocks_and_reset()

    width = int(dut.WIDTH.value)
    mask = (1 << width) - 1

    # Enable counter
    dut.i_enable.value = 1
    await ClockCycles(dut.clk, 5)

    # Collect several output samples (allow pipeline latency)
    bin_values = set()
    gray_values = set()
    mismatches = 0

    for i in range(50):
        await ClockCycles(dut.clk, 2)
        bin_val = int(dut.o_counter_bin.value) & mask
        gray_val = int(dut.o_counter_gray.value) & mask
        bin_values.add(bin_val)
        gray_values.add(gray_val)

        # Verify Gray code matches expected
        expected_gray = bin_to_gray(bin_val)
        if gray_val != expected_gray:
            mismatches += 1
            dut._log.warning(f"Gray mismatch: bin={bin_val}, gray={gray_val}, expected={expected_gray}")

    assert len(bin_values) > 1, "gray_counter_chain: binary counter is stuck"
    assert len(gray_values) > 1, "gray_counter_chain: gray output is stuck"
    assert mismatches == 0, f"gray_counter_chain: {mismatches} Gray code mismatches"
    dut._log.info(f"gray_counter_chain: saw {len(bin_values)} distinct bin values, {len(gray_values)} gray values")


def generate_gray_counter_chain_params():
    return [8, 16, 32]


gray_counter_chain_params = generate_gray_counter_chain_params()


@pytest.mark.parametrize("width", gray_counter_chain_params)
def test_gray_counter_chain(request, width, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    """Pytest wrapper for gray_counter_chain FUB test."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_fub': '../../../../rtl/fub',
    })

    dut_name = "gray_counter_chain"

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
            testcase="cocotb_test_gray_counter_chain",
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
        print(f"gray_counter_chain test failed: {e}")
        print(f"Logs: {log_path}")
        raise
