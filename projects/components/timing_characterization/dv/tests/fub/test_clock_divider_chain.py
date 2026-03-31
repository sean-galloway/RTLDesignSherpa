"""
Test runner for clock_divider_chain timing characterization FUB.

Verifies that cascaded clock dividers produce divided clock outputs.
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
async def cocotb_test_clock_divider_chain(dut):
    """Functional test for clock_divider_chain FUB."""
    tb = TimingCharTB(dut)
    await tb.setup_clocks_and_reset()

    num_stages = int(dut.NUM_STAGES.value)

    # Let the dividers run for many cycles
    initial_val = int(dut.o_divided_clks.value)
    seen_values = {initial_val}

    for _ in range(200):
        await ClockCycles(dut.clk, 5)
        val = int(dut.o_divided_clks.value)
        seen_values.add(val)

    # At least the first stage should have toggled
    assert len(seen_values) > 1, "clock_divider_chain: no stage toggled after 1000 clock cycles"
    dut._log.info(f"clock_divider_chain: saw {len(seen_values)} distinct output patterns")


def generate_clock_divider_chain_params():
    return [
        (2, 8, 1),
        (4, 16, 1),
    ]


clock_divider_chain_params = generate_clock_divider_chain_params()


@pytest.mark.parametrize("num_stages, counter_width, pickoff", clock_divider_chain_params)
def test_clock_divider_chain(request, num_stages, counter_width, pickoff, test_level):
    """Pytest wrapper for clock_divider_chain FUB test."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_fub': '../../../../rtl/fub',
    })

    dut_name = "clock_divider_chain"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/timing_characterization/rtl/filelists/char_top.f'
    )

    ns_str = TBBase.format_dec(num_stages, 2)
    cw_str = TBBase.format_dec(counter_width, 3)
    pk_str = TBBase.format_dec(pickoff, 2)
    test_name_plus_params = f"test_{dut_name}_ns{ns_str}_cw{cw_str}_pk{pk_str}"

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'NUM_STAGES': num_stages,
        'COUNTER_WIDTH': counter_width,
        'PICKOFF': pickoff,
    }

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
            testcase="cocotb_test_clock_divider_chain",
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            simulator="verilator",
            waves=False,
            keep_files=True,
            compile_args=compile_args,
        )
    except Exception as e:
        print(f"clock_divider_chain test failed: {e}")
        print(f"Logs: {log_path}")
        raise
