"""
Test runner for axi_write_engine_beats (FUB level).

Thin dispatcher: parametrizes (test_type, num_channels, data_width, pipeline,
timing_profile) from REG_LEVEL and hands them to AxiWriteEngineBeatsTB, which
holds all stimulus and checking (AXI4 write slave BFM + memory model on the
m_axi side, a level model for the ID-select SRAM drain port and the
scheduler request port).

Test types:
- 'single':   one channel, random beat count
- 'all':      every channel active with random beat counts
- 'odd':      beat counts that do not divide by the burst length (incl. 1)
- 'trickle':  SRAM data arrives slower than the bus drains it
"""
import os
import random
import sys

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root, sim_build_path, get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.dmas.rapids.dv.tbclasses.axi_write_engine_beats_tb import AxiWriteEngineBeatsTB


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_axi_write_engine_beats(dut):
    """Dispatch to the TB method named by TEST_TYPE."""
    test_type = os.environ.get('TEST_TYPE', 'single')
    tb = AxiWriteEngineBeatsTB(dut)
    await tb.setup_clocks_and_reset()
    dispatch = {
        'single': tb.test_single_channel,
        'all': tb.test_all_channels,
        'odd': tb.test_odd_sizes,
        'trickle': tb.test_trickle,
    }
    if test_type not in dispatch:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")
    await dispatch[test_type]()


def generate_params():
    """(test_type, num_channels, data_width, pipeline, xfer_cfg, timing_profile) by REG_LEVEL.

    GATE: 4 ch x 256 b, PIPELINE=0, 8-beat bursts, back-to-back consumer
    FUNC: + 8 ch x 512 b, PIPELINE=1, 16-beat bursts, two consumer profiles
    FULL: + 32-beat bursts and the full consumer profile sweep
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    test_types = ['single', 'all', 'odd', 'trickle']
    if reg_level == 'GATE':
        shapes = [(4, 256, 0, 7)]
        profiles = ['default']
    elif reg_level == 'FUNC':
        shapes = [(4, 256, 0, 7), (8, 512, 1, 15)]
        profiles = ['default', 'gaxi_backpressure']
    else:
        shapes = [(4, 256, 0, 7), (8, 512, 0, 15), (8, 512, 1, 31)]
        profiles = ['default', 'slow_producer', 'gaxi_backpressure', 'gaxi_stress', 'gaxi_realistic']
    params = []
    for tt in test_types:
        for (nc, dw, pipe, cfg) in shapes:
            for prof in profiles:
                params.append((tt, nc, dw, pipe, cfg, prof))
    return params


params = generate_params()


@pytest.mark.fub
@pytest.mark.parametrize("test_type, num_channels, data_width, pipeline, xfer_cfg, timing_profile", params)
def test_axi_write_engine_beats(request, test_type, num_channels, data_width, pipeline, xfer_cfg, timing_profile):
    """Pytest wrapper for axi_write_engine_beats."""
    coverage_enabled = os.environ.get('COVERAGE', '0') == '1'
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_fub_beats': '../../rtl/fub_beats',
    })
    dut_name = "axi_write_engine_beats"
    test_name = (f"test_axi_write_engine_beats_{test_type}_nc{num_channels}_dw{data_width:04d}"
                 f"_p{pipeline}_x{xfer_cfg}_{timing_profile}")
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name = f"{test_name}_{worker_id}"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/dmas/rapids/rtl/filelists/fub_beats/axi_write_engine_beats.f'
    )
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f'{test_name}.log')
    results_path = os.path.join(log_dir, f'results_{test_name}.xml')

    parameters = {
        'NUM_CHANNELS': str(num_channels),
        'DATA_WIDTH': str(data_width),
        'ID_WIDTH': '8',
        'SEG_COUNT_WIDTH': '10',       # $clog2(512) + 1, as the data path instantiates it
        'PIPELINE': str(pipeline),
        'AW_MAX_OUTSTANDING': '4',
        'USER_WIDTH': '8',
    }
    extra_env = {
        'TEST_TYPE': test_type,
        'TEST_XFER_CFG': str(xfer_cfg),
        'TEST_LEVEL': os.environ.get('TEST_LEVEL', 'gate'),
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
    }
    if timing_profile != 'default':
        extra_env['GAXI_TIMING_PROFILE'] = timing_profile

    compile_args = ['-Wno-TIMESCALEMOD', '-Wno-WIDTHEXPAND', '-Wno-WIDTHTRUNC', '-Wno-UNOPTFLAT']
    if coverage_enabled:
        compile_args.extend(["--coverage-line", "--coverage-toggle", "--coverage-underscore"])
    waves = get_wave_config(sim_build)          # WAVES=1 -> {sim_build}/dump.fst (WAVES_TYPE=vcd for a VCD)
    compile_args.extend(waves['extra_args'])
    extra_env.update(waves['extra_env'])
    extra_env['TRACE_FILE'] = waves['trace_file']

    create_view_cmd(log_dir, log_path, sim_build, module, test_name)
    try:
        run(
            python_search=[tests_dir, os.path.join(repo_root, 'projects/components/dmas/rapids/dv/tbclasses')],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase="cocotb_test_axi_write_engine_beats",
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=waves['enable'],
            plus_args=waves['sim_args'],
            keep_files=True,
            compile_args=compile_args,
        )
    except Exception as e:
        print(f"Test failed: {test_name}: {e}")
        print(f"Logs: {log_path}")
        raise
