# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""build-mon pytest wrappers for the IN-CORE monitor perf windows.

These three cases -- desc_perf, rw_perf, obs_equiv -- read perf CSRs that exist
only when the monitor cones are compiled in, so they belong to the monitors-ON
build. They used to live in the perf flow, which forced USE_AXI_MONITORS=1 for
them; that was tolerable when the perf flow owned its own harness, and became
wrong the moment there was ONE harness whose monitors-on/off state IS the
difference between the two builds.

The cocotb code is unchanged and unduplicated: `dv/cocotb_stream_harness.py` at
component level, the same module build-perf runs. Only the parameters differ,
and they come in as -G overrides on the compile line.

  obs_equiv is the one that matters most: it runs the in-core monitors and the
  external axi4_intf_master_observer SIMULTANEOUSLY over the same traffic and checks
  they agree. That cross-check is only possible in this build -- with monitors
  off there is nothing to compare the observer against.
"""

import os
import sys

import pytest
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

_AREA = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                     '..', '..', '..'))
for _p in (os.path.join(_AREA, 'dv'), os.path.join(_AREA, 'bin')):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from stream_cfg import num_channels, verilator_unroll_args  # noqa: E402  (reads rtl/stream_cfg_pkg.sv)

COCOTB_MODULE = 'cocotb_stream_harness'

_BUILD_HOST = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                           '..', '..', 'host'))

SIM_FPGA_CLK_HZ = 100_000_000
SIM_UART_BAUD   = 12_500_000

# Geometry comes from stream_char_cfg_pkg via stream_harness's defaults -- the
# SAME source stream_genesys2_top builds from. Only deviations are listed.
#
# AR/AW is the package's 8 and is no longer restated here. The old note said 2
# "MATCHES THE BOARD BUILD"; it matched a board top that hardcoded 2, which was
# itself the divergence from this package. The Verilator objection was real but
# is a tooling limit, not a design one: the monitor transaction table is sized
# NUM_CHANNELS*AR_MAX+4, and the deeper loops need a bigger unroll budget --
# 16384/200000 elaborates clean at AR/AW=8 with monitors ON (measured
# 2026-08-25), where 4096/20000 leaves 6 BLKLOOPINIT errors. The budget is set
# in the run() compile_args below.
MON_RTL_PARAMS = {
    'FPGA_CLK_HZ': str(SIM_FPGA_CLK_HZ),
    'UART_BAUD':   str(SIM_UART_BAUD),
    # Per-BUILD flavor, not common geometry.
    'USE_AXI_MONITORS': '1',
    # SRAM_DEPTH is NOT set here -- it is CFG_SRAM_DEPTH (256), the same depth
    # the board builds. The old 512 was AR/AW=16 sizing; at the package's 8 the
    # arithmetic gives 256, so board and sim want the same number.
    # From the package, so RTL and TB cannot disagree (see stream_cfg.py).
    'NUM_CHANNELS': str(num_channels()),
}


# 'dma_8ch' is the corner the board perf sweep failed on (7-8 active channels x
# >=4 descriptors) and that nothing else here covers: obs_equiv drives 4 active
# channels, everything else drives 1. It needs monitors ON -- the descriptor-fetch
# master is shared by every channel, so its monitor transaction table is the one
# structure that scales with channel count. Drive depth with DMA_DESC_PER_CH.
@pytest.mark.parametrize("test_type", ['desc_perf', 'rw_perf', 'obs_equiv', 'dma_8ch'])
def test_stream_mon_perf(request, test_type):
    # 'desc_perf' measures the DESCRIPTOR monitor's perf window. That monitor
    # (scheduler_group_array u_desc_axi_monitor) existed to instrument the
    # descriptor bus while chasing a STREAM bug and is now built only on demand
    # -- USE_DESC_AXI_MONITOR defaults to 0 -- so its perf CSRs read a
    # structural zero and this case cannot pass. Skipped in lockstep with the
    # parameter rather than deleted: re-arm the monitor and set
    # DESC_AXI_MON=1 to run it again. The data-path perf cases (rw_perf) use
    # stream_core's u_rd_axi_skid / write counterpart and are unaffected.
    if test_type == 'desc_perf' and os.environ.get('DESC_AXI_MON', '0') != '1':
        pytest.skip("descriptor-AXI monitor not built "
                    "(USE_DESC_AXI_MONITOR=0); set DESC_AXI_MON=1 to run")
    """In-core monitor perf windows (monitors ON, board-matched depth)."""
    module, repo_root_path, tests_dir, log_dir, rtl_dict = get_paths({
        'stream_harness': 'projects/fpga-systems/Genesys2/stream',
    })
    dut_name = "stream_harness"

    # Every root the filelist closure uses -- $FRAMEWORK_ROOT for the harness,
    # $STREAM_CHAR_FRAMEWORK_ROOT for instrumentation.f and the generated
    # bridges. env_python exports the latter pointing at the pre-migration tree,
    # so omitting it silently compiles this harness against the OLD bridge.
    area = os.path.join(repo_root_path, 'projects/fpga-systems/Genesys2/stream')
    os.environ['STREAM_ROOT'] = os.path.join(repo_root_path, 'projects/components/dmas/stream')
    os.environ['CONVERTERS_ROOT'] = os.path.join(repo_root_path, 'projects/components/converters')
    os.environ['MISC_ROOT'] = os.path.join(repo_root_path, 'projects/components/misc')
    os.environ['STREAM_CHAR_ROOT'] = area
    os.environ['STREAM_CHAR_FRAMEWORK_ROOT'] = area
    os.environ['FRAMEWORK_ROOT'] = area

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_path,
        filelist_path='projects/fpga-systems/Genesys2/stream/rtl/filelists/stream_harness.f')

    test_name = f"test_stream_mon_perf_{test_type}"
    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        'DUT': dut_name,
        'NUM_CHANNELS': MON_RTL_PARAMS['NUM_CHANNELS'],
        'TEST_TYPE': test_type,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{test_name}.xml'),
        'FPGA_CLK_HZ': str(SIM_FPGA_CLK_HZ),
        'UART_BAUD': str(SIM_UART_BAUD),
        'TEST_LEVEL': os.environ.get('TEST_LEVEL', 'gate'),
        'SEED': os.environ.get('SEED', '12345'),
    }
    waves = bool(int(os.environ.get('WAVES', '0')))

    compile_args = [
        "--public-flat-rw",
        "-Wno-TIMESCALEMOD", "-Wno-MULTIDRIVEN", "-Wno-WIDTHEXPAND",
        "-Wno-WIDTHTRUNC", "-Wno-SELRANGE", "-Wno-UNOPTFLAT",
        "-Wno-PINMISSING", "-Wno-PINCONNECTEMPTY",
        # Monitor trans-table loops are per-slot; raise the unroll budget.
        # 16384/200000, not 4096/20000: the package's AR/AW=8 deepens the
        # trans_mgr / axi_monitor_timeout / monitor_trans_cam loops past what
        # the smaller budget can unroll (6 BLKLOOPINIT errors). Do not lower
        # without re-checking at AR/AW=8 with monitors ON.
        *verilator_unroll_args(),   # shared budget -- see dv/stream_cfg.py
    ]
    if bool(int(os.environ.get('WAVES', '0'))):
        compile_args += ["--trace-fst", "--trace-structs", "--trace-depth", "99"]

    run(
        python_search=[tests_dir, os.path.join(_AREA, 'dv'), os.path.join(_AREA, 'bin'), _BUILD_HOST],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=COCOTB_MODULE,
        testcase="cocotb_test_stream_perf",
        parameters=MON_RTL_PARAMS,
        sim_build=sim_build,
        extra_env=extra_env,
        keep_files=True,
        compile_args=compile_args,
        waves=waves,
        plus_args=['--trace'] if waves else [],
    )
