"""axi_monitor_lite through axi4_slave_{rd,wr}_mon with MONITOR_LITE=1 (amba/monitor-lite TASK-001).
Exact packets for completions, a SLVERR, a stalled slave, an active-count
threshold and a held monbus. See bin/TBClasses/amba/monitor_lite/axi_monitor_lite_tb.py."""
import os
import random
import cocotb
import pytest
from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.amba.monitor_lite.axi_monitor_lite_tb import AxiMonitorLiteTB


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def axi_monitor_lite_test(dut):
    tb = AxiMonitorLiteTB(dut, is_write=(os.environ.get('MON_CHANNEL', 'rd') == 'wr'))
    await tb.setup_clocks_and_reset()
    ok = await tb.run_suite()
    assert ok, f"{len(tb.errors)} violation(s):\n  " + "\n  ".join(tb.errors[:20])


def generate_test_params():
    """(channel, id_width, max_trans, test_level)"""
    reg = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg == 'GATE':
        return [(ch, 4, 8, 'gate') for ch in ('rd', 'wr')]
    if reg == 'FUNC':
        return [(ch, iw, 8, 'func') for ch in ('rd', 'wr') for iw in (4, 8)]
    return [(ch, iw, mt, 'full') for ch in ('rd', 'wr') for iw in (4, 8) for mt in (8, 16)]


@pytest.mark.parametrize("channel, id_width, max_trans, test_level", generate_test_params())
def test_axi_monitor_lite(request, channel, id_width, max_trans, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba': 'rtl/amba', 'rtl_amba_includes': 'rtl/amba/includes',
    })
    dut_name = f"axi4_slave_{channel}_mon"
    test_name_plus_params = f"test_axi_monitor_lite_{channel}_iw{id_width}_mt{max_trans}_{test_level}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=f'rtl/amba/filelists/{dut_name}.f')
    rtl_parameters = {
        'AXI_ID_WIDTH': str(id_width), 'AXI_ADDR_WIDTH': '32', 'AXI_DATA_WIDTH': '32', 'AXI_USER_WIDTH': '1',
        'MAX_TRANSACTIONS': str(max_trans), 'MONITOR_LITE': '1',
    }
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst", 'VERILATOR_TRACE': '1', 'DUT': dut_name,
        'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO', 'COCOTB_RESULTS_FILE': results_path,
        'SEED': os.environ.get('SEED', str(random.randint(0, 1000000))),
        'TEST_LEVEL': test_level, 'MON_CHANNEL': channel, 'MAX_TRANSACTIONS': str(max_trans),
        'TEST_ID_WIDTH': str(id_width), 'TEST_ADDR_WIDTH': '32', 'TEST_DATA_WIDTH': '32', 'TEST_USER_WIDTH': '1',
        'TEST_CLK_PERIOD': '10',
    }
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)
    print(f"\n{'='*80}\n{dut_name} MONITOR_LITE=1: {test_level.upper()} IW={id_width} MAX={max_trans}\n{'='*80}")
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
