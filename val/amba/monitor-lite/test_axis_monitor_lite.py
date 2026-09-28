"""axis_monitor_lite through the tb_axis_monitor_lite fixture (amba/monitor-lite TASK-003).
Exact packets for stream start/end, TID/TDEST changes, source bubbles, a held
tready (backpressure credit + handshake timeout), an in-packet gap timeout, a
zero-strobe beat, a withdrawn TVALID, the type mask, a held monbus, and clear.
See bin/TBClasses/amba/monitor_lite/axis_monitor_lite_tb.py."""
import os
import random
import cocotb
import pytest
from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid
from TBClasses.amba.monitor_lite.axis_monitor_lite_tb import AxisMonitorLiteTB


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def axis_monitor_lite_test(dut):
    tb = AxisMonitorLiteTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run_suite()
    assert ok, f"{len(tb.errors)} violation(s):\n  " + "\n  ".join(tb.errors[:20])


def generate_test_params():
    """(data_width, id_width, dest_width) x test_level"""
    reg = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg == 'GATE':
        shapes = [(32, 8, 4)]
    elif reg == 'FUNC':
        shapes = [(32, 8, 4), (64, 4, 4)]
    else:
        shapes = [(32, 8, 4), (64, 4, 4), (512, 8, 1), (32, 2, 2)]
    return [(dw, iw, destw, lvl) for (dw, iw, destw) in shapes for lvl in reg_level_grid()]


@pytest.mark.parametrize("data_width, id_width, dest_width, test_level", generate_test_params())
def test_axis_monitor_lite(request, data_width, id_width, dest_width, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba': 'rtl/amba', 'rtl_amba_includes': 'rtl/amba/includes',
    })
    dut_name = "tb_axis_monitor_lite"
    test_name_plus_params = f"test_axis_monitor_lite_dw{data_width}_iw{id_width}_destw{dest_width}_{test_level}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, module='axis_monitor_lite')
    verilog_sources = list(verilog_sources) + [os.path.join(tests_dir, f"{dut_name}.sv")]
    rtl_parameters = {
        'AXIS_DATA_WIDTH': str(data_width), 'AXIS_ID_WIDTH': str(id_width),
        'AXIS_DEST_WIDTH': str(dest_width), 'AXIS_USER_WIDTH': '1', 'ACLK_MHZ': '100',
    }
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst", 'VERILATOR_TRACE': '1', 'DUT': dut_name,
        'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO', 'COCOTB_RESULTS_FILE': results_path,
        **level_env(test_level),
        'TEST_DATA_WIDTH': str(data_width), 'TEST_ID_WIDTH': str(id_width),
        'TEST_DEST_WIDTH': str(dest_width), 'TEST_USER_WIDTH': '1', 'TEST_CLK_PERIOD': '10',
    }
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)
    print(f"\n{'='*80}\naxis_monitor_lite: {test_level.upper()} DW={data_width} IW={id_width} DESTW={dest_width}\n{'='*80}")
    try:
        run(
            python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
            toplevel=dut_name, module=module, parameters=rtl_parameters, simulator='verilator',
            sim_build=sim_build, extra_env=extra_env, waves=False, keep_files=True,
            compile_args=['--trace-fst', '--trace-structs', '-Wno-fatal'],
            sim_args=['--trace-fst', '--trace-structs'],
            plus_args=[],
        )
    except Exception as e:
        print(f"Test failed: {e}\nLogs: {log_path}\nView: {cmd_filename}")
        raise
