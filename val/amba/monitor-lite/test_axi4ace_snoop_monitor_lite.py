"""axi4ace_snoop_monitor_lite through the tb_axi4ace_snoop_monitor_lite fixture.

Standalone ACE snoop-channel lite monitor validation.  Uses the reusable
AXI4ACESnoopMonitorLiteTB class and checks completion/error/timeout packets
against the documented event_code/channel_id encodings.
"""
import os
import random
import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.ace.ace_snoop_monitor_lite_tb import AXI4ACESnoopMonitorLiteTB
from TBClasses.shared.utilities import get_paths, sim_build_path, create_view_cmd
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid


@cocotb.test(timeout_time=30, timeout_unit="sec")
async def axi4ace_snoop_monitor_lite_test(dut):
    tb = AXI4ACESnoopMonitorLiteTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run_suite()
    assert ok, f"{len(tb.errors)} violation(s):\n  " + "\n  ".join(tb.errors[:20])


def generate_test_params():
    """Parameter tuple: (unit_id, agent_id, max_snoops, out_depth, addr_width,
    data_width, aclk_mhz, test_level).  Grids: GATE 1 / FUNC 3 / FULL 9."""
    reg = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg == 'GATE':
        configs = [
            (1, 10, 8, 4, 32, 32, 100),
        ]
    elif reg == 'FUNC':
        configs = [
            (1, 10, 8, 4, 32, 32, 100),
            (2, 20, 16, 4, 32, 32, 100),
            (1, 10, 8, 4, 64, 64, 100),
        ]
    else:  # FULL
        configs = [
            (1, 10, 8, 4, 32, 32, 100),
            (2, 20, 16, 4, 32, 32, 100),
            (1, 10, 8, 4, 64, 64, 100),
        ]
    return [(c + (lvl,)) for c in configs for lvl in reg_level_grid(reg)]


@pytest.mark.parametrize(
    "unit_id, agent_id, max_snoops, out_depth, addr_width, data_width, aclk_mhz, test_level",
    generate_test_params()
)
def test_axi4ace_snoop_monitor_lite(
    request, unit_id, agent_id, max_snoops, out_depth, addr_width, data_width,
    aclk_mhz, test_level
):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba': 'rtl/amba',
        'rtl_amba_includes': 'rtl/amba/includes',
        'rtl_common': 'rtl/common',
    })

    dut_name = "tb_axi4ace_snoop_monitor_lite"
    test_name = (
        f"test_axi4ace_snoop_monitor_lite_uid{unit_id}_aid{agent_id}_"
        f"ms{max_snoops}_od{out_depth}_aw{addr_width}_dw{data_width}_"
        f"mhz{aclk_mhz}_{test_level}"
    )
    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = sim_build_path(tests_dir, test_name)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name}.xml')

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, module='axi4ace_snoop_monitor_lite')
    verilog_sources = list(verilog_sources) + [os.path.join(tests_dir, f"{dut_name}.sv")]

    rtl_parameters = {
        'UNIT_ID': str(unit_id),
        'AGENT_ID': str(agent_id),
        'MAX_SNOOPS': str(max_snoops),
        'OUT_DEPTH': str(out_depth),
        'ADDR_WIDTH': str(addr_width),
        'DATA_WIDTH': str(data_width),
        'ACLK_MHZ': str(aclk_mhz),
    }

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        **level_env(test_level),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_MAX_SNOOPS': str(max_snoops),
        'TEST_CLK_PERIOD': str(int(1000 / aclk_mhz)),
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
    }

    compile_args = [
        "--trace-fst",
        "--trace-structs",
        "-Wall", "-Wno-SYNCASYNCNET", "-Wno-UNUSED", "-Wno-DECLFILENAME",
        "-Wno-PINMISSING", "-Wno-UNDRIVEN", "-Wno-WIDTHEXPAND",
        "-Wno-WIDTHTRUNC", "-Wno-SELRANGE", "-Wno-CASEINCOMPLETE",
        "-Wno-TIMESCALEMOD",
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    print(f"\n{'='*80}")
    print(f"AXI4-ACE Snoop Monitor Lite: {test_level.upper()} "
          f"AW={addr_width} DW={data_width} MAX_SNOOPS={max_snoops}")
    print(f"{'='*80}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes + [rtl_dict['rtl_common'], sim_build],
            toplevel=dut_name,
            module=module,
            parameters=rtl_parameters,
            simulator='verilator',
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
            plus_args=(['--trace'] if enable_waves else []),
        )
        print(f"PASSED: {test_name}")
    except Exception as e:
        print(f"FAILED: {test_name}")
        print(f"Error: {str(e)}")
        print(f"Logs: {log_path}")
        print(f"View: {cmd_filename}")
        raise
