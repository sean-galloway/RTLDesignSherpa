"""
Test runner for xor_tree timing characterization FUB.

Verifies that the XOR binary tree produces toggling output.
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


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_xor_tree(dut):
    """Functional test for xor_tree FUB."""
    tb = TimingCharTB(dut)
    await tb.setup_clocks_and_reset()

    num_flops = int(dut.ACTUAL_FLOPS.value)
    seen_values = set()
    rng = random.Random(42)

    for i in range(50):
        val = rng.getrandbits(num_flops)
        dut.i_data.value = val
        await ClockCycles(dut.clk, 3)
        out = int(dut.o_data.value)
        seen_values.add(out)

    assert len(seen_values) > 1, "xor_tree output is stuck"
    dut._log.info(f"xor_tree: saw {len(seen_values)} distinct output values")


def generate_xor_tree_params():
    return [
        (3, 256),
        (4, 256),
        (6, 64),
    ]


xor_tree_params = generate_xor_tree_params()


@pytest.mark.parametrize("levels, num_flops", xor_tree_params)
def test_xor_tree(request, levels, num_flops, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    """Pytest wrapper for xor_tree FUB test."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_fub': '../../../../rtl/fub',
    })

    dut_name = "xor_tree"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/timing_characterization/rtl/filelists/char_top.f'
    )

    lv_str = TBBase.format_dec(levels, 2)
    nf_str = TBBase.format_dec(num_flops, 3)
    test_name_plus_params = f"test_{dut_name}_lv{lv_str}_nf{nf_str}"

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {'LEVELS': levels, 'NUM_FLOPS': num_flops}

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
            testcase="cocotb_test_xor_tree",
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
        print(f"xor_tree test failed: {e}")
        print(f"Logs: {log_path}")
        raise
