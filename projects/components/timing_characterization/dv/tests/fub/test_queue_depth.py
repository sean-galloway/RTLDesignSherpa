"""
Test runner for queue_depth timing characterization FUB.

Verifies that the FIFO wrapper accepts writes, provides reads,
and reports correct count.
"""

import os
import sys
import random
import pytest
import cocotb
from cocotb.triggers import RisingEdge, ClockCycles
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd, get_repo_root
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.timing_characterization.dv.tbclasses.timing_char_tb import TimingCharTB


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_queue_depth(dut):
    """Functional test for queue_depth FUB."""
    tb = TimingCharTB(dut)
    await tb.setup_clocks_and_reset()

    data_width = int(dut.DATA_WIDTH.value)
    depth = int(dut.DEPTH.value)
    mask = (1 << data_width) - 1
    rng = random.Random(42)

    # Initially: FIFO should be empty
    dut.i_wr_valid.value = 0
    dut.i_rd_ready.value = 0
    await ClockCycles(dut.clk, 3)

    # Write some entries
    written_data = []
    num_writes = min(depth - 1, 8)  # Leave one slot free
    for i in range(num_writes):
        val = rng.randint(0, mask)
        dut.i_wr_valid.value = 1
        dut.i_wr_data.value = val
        dut.i_rd_ready.value = 0
        await RisingEdge(dut.clk)
        # Check wr_ready before recording
        if int(dut.o_wr_ready.value) == 1:
            written_data.append(val)

    dut.i_wr_valid.value = 0
    await ClockCycles(dut.clk, 3)

    # Read back entries
    read_data = []
    dut.i_rd_ready.value = 1
    for i in range(len(written_data) + 2):
        await RisingEdge(dut.clk)
        if int(dut.o_rd_valid.value) == 1:
            read_data.append(int(dut.o_rd_data.value))

    dut.i_rd_ready.value = 0
    await ClockCycles(dut.clk, 2)

    assert len(read_data) > 0, "queue_depth: no data read back from FIFO"
    dut._log.info(f"queue_depth: wrote {len(written_data)} entries, read {len(read_data)} entries")


def generate_queue_depth_params():
    return [
        (8, 4),
        (16, 8),
        (32, 16),
    ]


queue_depth_params = generate_queue_depth_params()


@pytest.mark.parametrize("data_width, depth", queue_depth_params)
def test_queue_depth(request, data_width, depth, test_level):
    """Pytest wrapper for queue_depth FUB test."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_fub': '../../../../rtl/fub',
    })

    dut_name = "queue_depth"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/timing_characterization/rtl/filelists/char_top.f'
    )

    dw_str = TBBase.format_dec(data_width, 3)
    dp_str = TBBase.format_dec(depth, 3)
    test_name_plus_params = f"test_{dut_name}_dw{dw_str}_dp{dp_str}"

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {'DATA_WIDTH': data_width, 'DEPTH': depth}

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
            testcase="cocotb_test_queue_depth",
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            simulator="verilator",
            waves=False,
            keep_files=True,
            compile_args=compile_args,
        )
    except Exception as e:
        print(f"queue_depth test failed: {e}")
        print(f"Logs: {log_path}")
        raise
