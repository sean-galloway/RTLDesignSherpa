# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""build-perf pytest wrappers for the stream_harness cosim.

The cocotb tests themselves are COMPONENT level in
`dv/cocotb_stream_harness.py`, shared with build-mon -- one harness, one set of
cocotb behaviours. This file only decides, for the MONITORS-OFF build: which
cases to run, at which parameters.

USE_AXI_MONITORS is fixed at 0 here. It is what makes this build-perf.
"""

import hashlib
import json
import os
import sys
import random
import pytest
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root
from TBClasses.shared.filelist_utils import get_sources_from_filelist

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

# Component-level layers: dv/ holds the shared dispatcher + tbclasses, bin/ the
# host libraries both import.
_AREA = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                     '..', '..', '..'))
for _p in (os.path.join(_AREA, 'dv'), os.path.join(_AREA, 'bin')):
    if _p not in sys.path:
        sys.path.insert(0, _p)

# cocotb loads the dispatcher by module NAME; every run() below passes this.
COCOTB_MODULE = 'cocotb_stream_harness'

def elab_sim_build(tests_dir, rtl_parameters, compile_args):
    """A sim_build directory keyed by what actually gets COMPILED.

    Every case in this build elaborates the SAME harness at the SAME parameters
    -- USE_AXI_MONITORS is fixed by the build, not the test -- so keying the
    build directory on the test NAME made each case recompile an identical
    model. Measured: ~220 s cold vs ~35 s warm, about 185 s of pure duplicate
    compile per case, ~30 min across a suite whose actual simulation is minutes.

    Keying on (parameters, compile_args) instead means the first case compiles
    and the rest reuse it. Two cases share a directory only when their
    elaboration inputs are byte-identical, so this cannot silently run a case
    against the wrong model -- change a parameter and the key changes with it.

    The xdist worker id stays in the key: parallel workers must not share a
    build tree.
    """
    key = json.dumps({'p': rtl_parameters, 'c': compile_args}, sort_keys=True)
    digest = hashlib.sha1(key.encode()).hexdigest()[:12]
    worker = os.environ.get('PYTEST_XDIST_WORKER', '')
    name = f"elab_{digest}" + (f"_{worker}" if worker else "")
    return os.path.join(tests_dir, 'local_sim_build', name)


# This build's host programs. On python_search because the shared TB imports
# host_ext_char to drive the ext_char sweep -- one implementation, sim and board.
_BUILD_HOST = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                           '..', '..', 'host'))

# ==========================================================================
# Parameter generation
# ==========================================================================

# Simulation-fast UART baud. Push it as close to the 100 MHz sim clock as the
# UART tolerates so sims aren't dominated by serial time. CLKS_PER_BIT=4 (25 MHz)
# is the practical floor: uart_rx has a 2-flop rx synchronizer (~2-clock latency),
# so the bit period must exceed that -- CLKS_PER_BIT=2 samples before the sync
# settles. 4 halves the serial time vs the old 8 (12.5 MHz).
SIM_FPGA_CLK_HZ = 100_000_000
SIM_UART_BAUD   = 25_000_000   # CLKS_PER_BIT = 100 MHz / 25 MHz = 4

# RTL parameters for the harness
BASE_RTL_PARAMS = {
    'DATA_WIDTH': 128,
    'ADDR_WIDTH': 32,
    # Bandwidth-delay-product sizing for the read datapath. The rw_perf bubble
    # study showed the residual ~6% is 100% RD starvation (bp=0): with 16-beat
    # (256 B) bursts and a measured AR->firstR latency of 64-127 cyc, the old
    # AR_MAX_OUTSTANDING=8 (8 x 16 = 128 cyc coverage) sat right at the latency
    # knife-edge, costing ~1 dead cycle per burst boundary.
    #
    # Sizing target = 16: the per-channel SRAM that buffers in-flight read data
    # is BRAM, and 7-series BRAM is power-of-2 deep (512x72 / 1Kx36 / ... per
    # primitive). A 128-bit-wide buffer packs onto 512-deep tiles, so any depth
    # in (256, 512] costs the SAME BRAM as 512 -- a 384-deep SRAM just wastes
    # entries 384-511. So size outstanding to fill the pow-2 tile: AR=AW=16 ->
    # 16 x 16-beat = 256 beats in flight, x2 headroom = SRAM_DEPTH 512 (fully
    # justified, no dead space) and 256 cyc of latency coverage (>> the 127 cyc
    # worst case). Keeps bursts <= 1024 B (real-system QoS limit -- no long-burst
    # masking). The R/B response-delay models scale with the in-flight count so
    # the modeled memory never back-pressures and masks the engine. All
    # env-overridable to A/B the old 8/256/256 baseline: SIM_AR_OUTSTANDING /
    # SIM_AW_OUTSTANDING / SIM_SRAM_DEPTH / SIM_RESP_DELAY_R_CAP / _B_CAP.
    'SRAM_DEPTH': int(os.environ.get('SIM_SRAM_DEPTH', '512')),
    'AR_MAX_OUTSTANDING': int(os.environ.get('SIM_AR_OUTSTANDING', '16')),
    'AW_MAX_OUTSTANDING': int(os.environ.get('SIM_AW_OUTSTANDING', '16')),
    'RESP_DELAY_R_CAPACITY': int(os.environ.get('SIM_RESP_DELAY_R_CAP', '512')),
    'RESP_DELAY_B_CAPACITY': int(os.environ.get('SIM_RESP_DELAY_B_CAP', '32')),
    # NUM_CHANNELS shrunk from 8 to 4 to fit the Artix-7 100T BRAM budget.
    # Keep in lockstep with rtl/stream_harness.sv. Override via
    # SIM_NUM_CHANNELS env var when investigating bugs that may be tied
    # to the 8-channel elab (e.g. the deep-chain hang first seen on the
    # NUM_CHANNELS=8 FPGA build); Verilator doesn't care about BRAM
    # tiles so bumping this for an investigation run is cheap.
    'NUM_CHANNELS': int(os.environ.get('SIM_NUM_CHANNELS', '4')),
    # Harness memories were the dominant BRAM consumers. Mirror the FPGA
    # values so sim exercises the same sizes as silicon. Bump either when a
    # test needs deeper descriptor chains or longer trace captures.
    'DESC_RAM_ENTRIES': 128,    # 128 × 256 b =  4 KB
    'DEBUG_SRAM_WORDS': 4096,   # 4K × 32 b   = 16 KB
    # MonBus bulk-trace compression. Project default is 1 (compressor in
    # path). Override with USE_MON_COMPRESSION=0 to build the uncompressed
    # baseline for the with/without compression characterization.
    'USE_MON_COMPRESSION': int(os.environ.get('USE_MON_COMPRESSION', '1')),
    # NOTE: the CAM pipeline is no longer a parameter -- the monbus compressor
    # CAM and the AXI monitor transaction CAM are ALWAYS pipelined in RTL.
}


def generate_stream_perf_params():
    """
    Generate (test_type,) tuples.  Each level is CUMULATIVE:

    gate: ping                                               (1 test)
    func: gate + desc_load + csr_read + apb_config +
          dma_1ch + dma_2ch                                  (6 tests)
    full: func + dma_3ch + dma_4ch + ... + dma_<NCH>ch

    DMA tests: 2 descriptors/channel, 8 KB each = 16 KB moved per channel.
    The FULL set is capped at BASE_RTL_PARAMS['NUM_CHANNELS'] so we don't
    ask the harness to kick channels it doesn't have (FPGA build is 4-ch).
    """
    max_channels = BASE_RTL_PARAMS.get('NUM_CHANNELS', 8)
    gate_types = ['ping']
    # desc_perf / rw_perf / obs_equiv are NOT here: they read in-core monitor
    # windows, which exist only when USE_AXI_MONITORS=1 -- i.e. in build-mon.
    # This build's datapath utilisation comes from the always-on observer bus
    # meters, which need no monitors (obs_window / dma_* cover that).
    func_types = ['desc_load', 'csr_read', 'apb_config', 'dma_1ch', 'dma_2ch']
    full_types = [f'dma_{n}ch' for n in range(3, max_channels + 1)]
    full_types += ['compress_char']   # compression characterization run

    # Accept both TEST_LEVEL (Makefile convention) and REG_LEVEL (legacy)
    level = os.environ.get('TEST_LEVEL',
                os.environ.get('REG_LEVEL', 'FUNC')).upper()

    types = list(gate_types)                  # gate always included
    if level in ('FUNC', 'FULL'):
        types += func_types
    if level == 'FULL':
        types += full_types

    return [(t,) for t in types]


stream_perf_params = generate_stream_perf_params()


# ==========================================================================
# Pytest wrapper
# ==========================================================================

@pytest.mark.parametrize("test_type", [p[0] for p in stream_perf_params])
def test_stream_perf(request, test_type, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    """Pytest wrapper for stream characterization harness tests."""
    module, repo_root_path, tests_dir, log_dir, rtl_dict = get_paths({
        'stream_harness': 'projects/fpga-systems/Genesys2/stream',
    })

    dut_name = "stream_harness"

    # Build source list via filelist.
    # Environment variables needed by the filelist:
    os.environ['STREAM_ROOT'] = os.path.join(repo_root_path, 'projects/components/dmas/stream')
    os.environ['CONVERTERS_ROOT'] = os.path.join(repo_root_path, 'projects/components/converters')
    os.environ['MISC_ROOT'] = os.path.join(repo_root_path, 'projects/components/misc')
    os.environ['STREAM_CHAR_ROOT'] = os.path.join(repo_root_path, 'projects/fpga-systems/Genesys2/stream')
    # BOTH names. The harness filelist uses $FRAMEWORK_ROOT; instrumentation.f
    # (harness_csr, axi_response_delay, the GENERATED BRIDGES) uses
    # $STREAM_CHAR_FRAMEWORK_ROOT. env_python exports the latter pointing at
    # the pre-migration tree, so setting only FRAMEWORK_ROOT compiles this
    # area's harness against the OLD tree's bridge -- which is a real build,
    # just of a stale design (it predates the observer's APB slave).
    os.environ['STREAM_CHAR_FRAMEWORK_ROOT'] = os.path.join(repo_root_path, 'projects/fpga-systems/Genesys2/stream')
    os.environ['FRAMEWORK_ROOT'] = os.environ['STREAM_CHAR_FRAMEWORK_ROOT']

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_path,
        filelist_path='projects/fpga-systems/Genesys2/stream/rtl/filelists/stream_harness.f',
    )

    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_{test_type}_{reg_level}"

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    # sim_build is keyed by ELABORATION INPUTS, not the test name -- assigned
    # just before run(), once rtl_parameters and compile_args exist.
    os.makedirs(log_dir, exist_ok=True)

    # USE_AXI_MONITORS is the BUILD's identity, not a per-test knob.
    #
    # There is ONE harness (rtl/stream_harness.sv); build-mon and build-perf are
    # that same design at different parameters, and monitors-on/off IS the
    # difference. A test in build-perf that flips it to 1 is not testing this
    # build -- it is building build-mon's design inside build-perf's directory,
    # at build-perf's parameters (AR_MAX_OUTSTANDING=16), a combination no
    # bitstream uses and which Verilator cannot even elaborate (BLKLOOPINIT in
    # axi_monitor_timeout).
    #
    # That override is a leftover from when the perf flow had its OWN harness
    # and could parameterize it freely. The three monitors-on test types it
    # served -- rw_perf, desc_perf, obs_equiv -- read IN-CORE monitor windows,
    # so they belong to the monitors-on build. See build-mon.
    rtl_parameters = {
        'FPGA_CLK_HZ': str(SIM_FPGA_CLK_HZ),
        'UART_BAUD':   str(SIM_UART_BAUD),
        'USE_AXI_MONITORS': '0',
        **{k: str(v) for k, v in BASE_RTL_PARAMS.items()},
    }

    extra_env = {
        'TEST_TYPE':        test_type,
        'FPGA_CLK_HZ':     str(SIM_FPGA_CLK_HZ),
        'UART_BAUD':        str(SIM_UART_BAUD),
        'TEST_LEVEL':       test_level,
        'DUT':              dut_name,
        'NUM_CHANNELS': str(BASE_RTL_PARAMS['NUM_CHANNELS']),
        'LOG_PATH':         log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED':             os.environ.get('SEED', str(random.randint(0, 100000))),
        # DMA test parameters: default 2 descriptors/ch x 8KB = 16KB per
        # channel. Overridable so a run can be shrunk to the smallest thing
        # that still exercises the path -- one descriptor per channel is the
        # useful case for reading waves, where 2x the traffic is 2x the trace
        # to scroll through for no extra coverage.
        'DMA_DESC_PER_CH':  os.environ.get('DMA_DESC_PER_CH', '2'),
        'DMA_XFER_BYTES':   os.environ.get('DMA_XFER_BYTES', '8192'),
    }

    # Use Verilator by default
    simulator = os.environ.get('SIM', 'verilator').lower()

    # WAVES support - conditionally set COCOTB_TRACE_FILE for VCD generation
    compile_args = [
        "--trace-fst",
        "--trace-structs",
        "--trace-depth", "99",
        # --public-flat-rw exposes every internal signal/instance to VPI so
        # cocotb can probe deep state (e.g., axi_write_engine internals)
        # without needing top-level pass-through ports. Slight sim-perf cost.
        "--public-flat-rw",
        "-Wno-TIMESCALEMOD",
        "-Wno-MULTIDRIVEN",    # PeakRDL stream_regs.sv
        "-Wno-WIDTHEXPAND",    # minor width warnings in STREAM hierarchy
        "-Wno-WIDTHTRUNC",
        "-Wno-SELRANGE",       # descriptor_engine pre-existing slice warning
        "-Wno-UNOPTFLAT",      # dataint_crc combinational cascade (structural CRC)
        # monitors-on builds size RD/WR_MON_MAX_TRANS = NUM_CHANNELS*AR_MAX+4
        # (e.g. 4*16+4=68 > Verilator's default --unroll-count 64), so the
        # per-slot trans-table/reporter loops fail BLKLOOPINIT without this.
        # Same flags the sibling monitors-on sims use (test_stream_mon,
        # test_stream_top_monbus, macro test_stream_core).
        # The harness is SHARED with build-mon now, so its compile closure
        # includes dma_slave_monitors -> monbus_group, whose optional status
        # pins are intentionally unconnected here. Verilator promotes the
        # resulting warnings to an error ("Exiting due to N warnings"), which
        # reads as a compile failure rather than an unused-feature notice.
        "-Wno-PINMISSING", "-Wno-PINCONNECTEMPTY",
        "--unroll-count", "4096", "--unroll-stmts", "20000",
    ]


    # Keyed by elaboration inputs so cases sharing a model compile ONCE.
    sim_build = elab_sim_build(tests_dir, rtl_parameters, compile_args)
    os.makedirs(sim_build, exist_ok=True)

    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.fst')

    cmd_filename = create_view_cmd(
        log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir, _AREA + "/dv", _AREA + "/bin", _BUILD_HOST],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=COCOTB_MODULE,
            testcase="cocotb_test_stream_perf",
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            simulator=simulator,
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
            sim_args=[
                "--trace",
                "--trace-structs",
                "--trace-depth", "99",
            ],
            plus_args=['--trace'] if enable_waves else [],
        )
        print(f"PASS {test_type}! Logs: {log_path}")
    except Exception as e:
        print(f"FAIL {test_type}: {e}")
        print(f"Logs: {log_path}")
        print(f"Waveforms: {cmd_filename}")
        raise


def test_stream_perf_ext_suite(request):
    """TASK-101 pre-validation: build the char harness with
    USE_ROW_COL_MAJOR_ADDRESSING=1 and run the named Stream extended-addressing
    suite (row/row, row/col, col/row, col/col) over the real bridge RTL — the
    same host program that runs on the FPGA. Separate build from the existing
    param=0 tests."""
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root_path, tests_dir, log_dir, rtl_dict = get_paths({
        'stream_harness': 'projects/fpga-systems/Genesys2/stream',
    })
    dut_name = "stream_harness"

    os.environ['STREAM_ROOT'] = os.path.join(repo_root_path, 'projects/components/dmas/stream')
    os.environ['CONVERTERS_ROOT'] = os.path.join(repo_root_path, 'projects/components/converters')
    os.environ['MISC_ROOT'] = os.path.join(repo_root_path, 'projects/components/misc')
    os.environ['STREAM_CHAR_ROOT'] = os.path.join(repo_root_path, 'projects/fpga-systems/Genesys2/stream')
    # BOTH names. The harness filelist uses $FRAMEWORK_ROOT; instrumentation.f
    # (harness_csr, axi_response_delay, the GENERATED BRIDGES) uses
    # $STREAM_CHAR_FRAMEWORK_ROOT. env_python exports the latter pointing at
    # the pre-migration tree, so setting only FRAMEWORK_ROOT compiles this
    # area's harness against the OLD tree's bridge -- which is a real build,
    # just of a stale design (it predates the observer's APB slave).
    os.environ['STREAM_CHAR_FRAMEWORK_ROOT'] = os.path.join(repo_root_path, 'projects/fpga-systems/Genesys2/stream')
    os.environ['FRAMEWORK_ROOT'] = os.environ['STREAM_CHAR_FRAMEWORK_ROOT']

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_path,
        filelist_path='projects/fpga-systems/Genesys2/stream/rtl/filelists/stream_harness.f',
    )

    test_name_plus_params = f"test_{dut_name}_ext_suite_rowcol"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    # sim_build is keyed by ELABORATION INPUTS, not the test name -- assigned
    # just before run(), once rtl_parameters and compile_args exist.
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'FPGA_CLK_HZ': str(SIM_FPGA_CLK_HZ),
        'UART_BAUD':   str(SIM_UART_BAUD),
        'USE_ROW_COL_MAJOR_ADDRESSING': '1',   # ← extended addressing enabled
        **{k: str(v) for k, v in BASE_RTL_PARAMS.items()},
    }
    extra_env = {
        'TEST_TYPE':        'ext_suite',
        'FPGA_CLK_HZ':     str(SIM_FPGA_CLK_HZ),
        'UART_BAUD':        str(SIM_UART_BAUD),
        'TEST_LEVEL':       'gate',
        'DUT':              dut_name,
        'NUM_CHANNELS': str(BASE_RTL_PARAMS['NUM_CHANNELS']),
        'LOG_PATH':         log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED':             os.environ.get('SEED', str(random.randint(0, 100000))),
    }
    simulator = os.environ.get('SIM', 'verilator').lower()
    compile_args = [
        "--trace-fst", "--trace-structs", "--trace-depth", "99",
        "--public-flat-rw",
        "-Wno-TIMESCALEMOD", "-Wno-MULTIDRIVEN", "-Wno-WIDTHEXPAND",
        "-Wno-WIDTHTRUNC", "-Wno-SELRANGE", "-Wno-UNOPTFLAT",
        # deep monitor trans-table loops (RD_MON_MAX_TRANS>64) need unroll raised
        # The harness is SHARED with build-mon now, so its compile closure
        # includes dma_slave_monitors -> monbus_group, whose optional status
        # pins are intentionally unconnected here. Verilator promotes the
        # resulting warnings to an error ("Exiting due to N warnings"), which
        # reads as a compile failure rather than an unused-feature notice.
        "-Wno-PINMISSING", "-Wno-PINCONNECTEMPTY",
        "--unroll-count", "4096", "--unroll-stmts", "20000",
    ]

    # Keyed by elaboration inputs so cases sharing a model compile ONCE.
    sim_build = elab_sim_build(tests_dir, rtl_parameters, compile_args)
    create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    run(
        python_search=[tests_dir, _AREA + "/dv", _AREA + "/bin", _BUILD_HOST],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=COCOTB_MODULE,
        testcase="cocotb_test_stream_perf",
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        simulator=simulator,
        waves=enable_waves,
        keep_files=True,
        compile_args=compile_args,
        sim_args=["--trace", "--trace-structs", "--trace-depth", "99"],
        plus_args=['--trace'] if enable_waves else [],
    )
    print(f"PASS ext_suite! Logs: {log_path}")


def test_stream_perf_ext_chain(request):
    """TASK-059 aggressive regression: build the char harness param=1 and CHAIN
    strided/transpose extended descriptors via next_ptr (the pre-si failure
    shape). Same RTL build as ext_suite (reuses its sim_build), TEST_TYPE only
    differs. Verifies the sink slave saw ALL expected beats (no dropped "holes")
    + no CH_ERROR."""
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root_path, tests_dir, log_dir, rtl_dict = get_paths({
        'stream_harness': 'projects/fpga-systems/Genesys2/stream',
    })
    dut_name = "stream_harness"

    os.environ['STREAM_ROOT'] = os.path.join(repo_root_path, 'projects/components/dmas/stream')
    os.environ['CONVERTERS_ROOT'] = os.path.join(repo_root_path, 'projects/components/converters')
    os.environ['MISC_ROOT'] = os.path.join(repo_root_path, 'projects/components/misc')
    os.environ['STREAM_CHAR_ROOT'] = os.path.join(repo_root_path, 'projects/fpga-systems/Genesys2/stream')
    # BOTH names. The harness filelist uses $FRAMEWORK_ROOT; instrumentation.f
    # (harness_csr, axi_response_delay, the GENERATED BRIDGES) uses
    # $STREAM_CHAR_FRAMEWORK_ROOT. env_python exports the latter pointing at
    # the pre-migration tree, so setting only FRAMEWORK_ROOT compiles this
    # area's harness against the OLD tree's bridge -- which is a real build,
    # just of a stale design (it predates the observer's APB slave).
    os.environ['STREAM_CHAR_FRAMEWORK_ROOT'] = os.path.join(repo_root_path, 'projects/fpga-systems/Genesys2/stream')
    os.environ['FRAMEWORK_ROOT'] = os.environ['STREAM_CHAR_FRAMEWORK_ROOT']

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_path,
        filelist_path='projects/fpga-systems/Genesys2/stream/rtl/filelists/stream_harness.f',
    )

    # Reuse the ext_suite build (identical RTL params; only TEST_TYPE differs) so
    # this does not trigger a second ~11-min monitors-on elaboration.
    test_name_plus_params = f"test_{dut_name}_ext_suite_rowcol"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"
    log_path = os.path.join(log_dir, f'test_{dut_name}_ext_chain.log')
    results_path = os.path.join(log_dir, f'results_test_{dut_name}_ext_chain.xml')
    # sim_build is keyed by ELABORATION INPUTS, not the test name -- assigned
    # just before run(), once rtl_parameters and compile_args exist.
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'FPGA_CLK_HZ': str(SIM_FPGA_CLK_HZ),
        'UART_BAUD':   str(SIM_UART_BAUD),
        'USE_ROW_COL_MAJOR_ADDRESSING': '1',   # ← extended addressing enabled
        **{k: str(v) for k, v in BASE_RTL_PARAMS.items()},
    }
    extra_env = {
        'TEST_TYPE':        'ext_chain',
        'FPGA_CLK_HZ':      str(SIM_FPGA_CLK_HZ),
        'UART_BAUD':        str(SIM_UART_BAUD),
        'TEST_LEVEL':       'gate',
        'DUT':              dut_name,
        'NUM_CHANNELS': str(BASE_RTL_PARAMS['NUM_CHANNELS']),
        'LOG_PATH':         log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED':             str(random.randint(0, 100000)),
    }
    simulator = os.environ.get('SIM', 'verilator').lower()
    compile_args = [
        "--trace-fst", "--trace-structs", "--trace-depth", "99",
        "--public-flat-rw",
        "-Wno-TIMESCALEMOD", "-Wno-MULTIDRIVEN", "-Wno-WIDTHEXPAND",
        "-Wno-WIDTHTRUNC", "-Wno-SELRANGE", "-Wno-UNOPTFLAT",
        # The harness is SHARED with build-mon now, so its compile closure
        # includes dma_slave_monitors -> monbus_group, whose optional status
        # pins are intentionally unconnected here. Verilator promotes the
        # resulting warnings to an error ("Exiting due to N warnings"), which
        # reads as a compile failure rather than an unused-feature notice.
        "-Wno-PINMISSING", "-Wno-PINCONNECTEMPTY",
        "--unroll-count", "4096", "--unroll-stmts", "20000",
    ]

    # Keyed by elaboration inputs so cases sharing a model compile ONCE.
    sim_build = elab_sim_build(tests_dir, rtl_parameters, compile_args)
    create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    run(
        python_search=[tests_dir, _AREA + "/dv", _AREA + "/bin", _BUILD_HOST],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=COCOTB_MODULE,
        testcase="cocotb_test_stream_perf",
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        simulator=simulator,
        waves=enable_waves,
        keep_files=True,
        compile_args=compile_args,
        sim_args=["--trace", "--trace-structs", "--trace-depth", "99"],
        plus_args=['--trace'] if enable_waves else [],
    )
    print(f"PASS ext_chain! Logs: {log_path}")


def test_stream_perf_ext_chain_soak(request):
    """TASK-059 aggressive SOAK: build param=1 and loop randomized MIXED chained
    strided/transpose descriptors. Reuses the ext_suite build; TEST_TYPE differs.
    Scale via EXT_SOAK_ITERS (sim default 15; set high for a 10-min hardware run
    through host/stream_ext_soak.py on the board)."""
    module, repo_root_path, tests_dir, log_dir, rtl_dict = get_paths({
        'stream_harness': 'projects/fpga-systems/Genesys2/stream',
    })
    dut_name = "stream_harness"
    os.environ['STREAM_ROOT'] = os.path.join(repo_root_path, 'projects/components/dmas/stream')
    os.environ['CONVERTERS_ROOT'] = os.path.join(repo_root_path, 'projects/components/converters')
    os.environ['MISC_ROOT'] = os.path.join(repo_root_path, 'projects/components/misc')
    os.environ['STREAM_CHAR_ROOT'] = os.path.join(repo_root_path, 'projects/fpga-systems/Genesys2/stream')
    # BOTH names. The harness filelist uses $FRAMEWORK_ROOT; instrumentation.f
    # (harness_csr, axi_response_delay, the GENERATED BRIDGES) uses
    # $STREAM_CHAR_FRAMEWORK_ROOT. env_python exports the latter pointing at
    # the pre-migration tree, so setting only FRAMEWORK_ROOT compiles this
    # area's harness against the OLD tree's bridge -- which is a real build,
    # just of a stale design (it predates the observer's APB slave).
    os.environ['STREAM_CHAR_FRAMEWORK_ROOT'] = os.path.join(repo_root_path, 'projects/fpga-systems/Genesys2/stream')
    os.environ['FRAMEWORK_ROOT'] = os.environ['STREAM_CHAR_FRAMEWORK_ROOT']
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_path,
        filelist_path='projects/fpga-systems/Genesys2/stream/rtl/filelists/stream_harness.f',
    )
    # Reuse the ext_suite build (identical RTL params; only TEST_TYPE differs).
    test_name_plus_params = f"test_{dut_name}_ext_suite_rowcol"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"
    log_path = os.path.join(log_dir, f'test_{dut_name}_ext_chain_soak.log')
    results_path = os.path.join(log_dir, f'results_test_{dut_name}_ext_chain_soak.xml')
    # sim_build is keyed by ELABORATION INPUTS, not the test name -- assigned
    # just before run(), once rtl_parameters and compile_args exist.
    os.makedirs(log_dir, exist_ok=True)
    rtl_parameters = {
        'FPGA_CLK_HZ': str(SIM_FPGA_CLK_HZ),
        'UART_BAUD':   str(SIM_UART_BAUD),
        'USE_ROW_COL_MAJOR_ADDRESSING': '1',
        **{k: str(v) for k, v in BASE_RTL_PARAMS.items()},
    }
    extra_env = {
        'TEST_TYPE':        'ext_chain_soak',
        'FPGA_CLK_HZ':      str(SIM_FPGA_CLK_HZ),
        'UART_BAUD':        str(SIM_UART_BAUD),
        'TEST_LEVEL':       'gate',
        'DUT':              dut_name,
        'NUM_CHANNELS': str(BASE_RTL_PARAMS['NUM_CHANNELS']),
        'LOG_PATH':         log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED':             str(random.randint(0, 100000)),
        'EXT_SOAK_ITERS':   os.environ.get('EXT_SOAK_ITERS', '15'),
    }
    simulator = os.environ.get('SIM', 'verilator').lower()
    compile_args = [
        "--trace-fst", "--trace-structs", "--trace-depth", "99", "--public-flat-rw",
        "-Wno-TIMESCALEMOD", "-Wno-MULTIDRIVEN", "-Wno-WIDTHEXPAND",
        "-Wno-WIDTHTRUNC", "-Wno-SELRANGE", "-Wno-UNOPTFLAT",
        # The harness is SHARED with build-mon now, so its compile closure
        # includes dma_slave_monitors -> monbus_group, whose optional status
        # pins are intentionally unconnected here. Verilator promotes the
        # resulting warnings to an error ("Exiting due to N warnings"), which
        # reads as a compile failure rather than an unused-feature notice.
        "-Wno-PINMISSING", "-Wno-PINCONNECTEMPTY",
        "--unroll-count", "4096", "--unroll-stmts", "20000",
    ]

    # Keyed by elaboration inputs so cases sharing a model compile ONCE.
    sim_build = elab_sim_build(tests_dir, rtl_parameters, compile_args)
    create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    run(
        python_search=[tests_dir, _AREA + "/dv", _AREA + "/bin", _BUILD_HOST], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=COCOTB_MODULE, testcase="cocotb_test_stream_perf",
        parameters=rtl_parameters, sim_build=sim_build, extra_env=extra_env,
        simulator=simulator, waves=bool(int(os.environ.get('WAVES', '0'))),
        keep_files=True, compile_args=compile_args,
        sim_args=["--trace", "--trace-structs", "--trace-depth", "99"],
    )
    print(f"PASS ext_chain_soak! Logs: {log_path}")


def test_stream_perf_ext_char(request):
    """TASK-101 characterization pre-validation: build the char harness param=1
    and sweep the four addressing modes x (small) sizes, measuring RD/WR perf and
    dumping JSON. Validates the perf plumbing in sim; the full board sweep uses
    host/stream_ext_char.py. JSON -> results/ext/ext_char_sim.json for the report
    generator."""
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root_path, tests_dir, log_dir, rtl_dict = get_paths({
        'stream_harness': 'projects/fpga-systems/Genesys2/stream',
    })
    dut_name = "stream_harness"

    os.environ['STREAM_ROOT'] = os.path.join(repo_root_path, 'projects/components/dmas/stream')
    os.environ['CONVERTERS_ROOT'] = os.path.join(repo_root_path, 'projects/components/converters')
    os.environ['MISC_ROOT'] = os.path.join(repo_root_path, 'projects/components/misc')
    os.environ['STREAM_CHAR_ROOT'] = os.path.join(repo_root_path, 'projects/fpga-systems/Genesys2/stream')
    # BOTH names. The harness filelist uses $FRAMEWORK_ROOT; instrumentation.f
    # (harness_csr, axi_response_delay, the GENERATED BRIDGES) uses
    # $STREAM_CHAR_FRAMEWORK_ROOT. env_python exports the latter pointing at
    # the pre-migration tree, so setting only FRAMEWORK_ROOT compiles this
    # area's harness against the OLD tree's bridge -- which is a real build,
    # just of a stale design (it predates the observer's APB slave).
    os.environ['STREAM_CHAR_FRAMEWORK_ROOT'] = os.path.join(repo_root_path, 'projects/fpga-systems/Genesys2/stream')
    os.environ['FRAMEWORK_ROOT'] = os.environ['STREAM_CHAR_FRAMEWORK_ROOT']

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_path,
        filelist_path='projects/fpga-systems/Genesys2/stream/rtl/filelists/stream_harness.f',
    )

    results_dir = os.path.join(os.environ['STREAM_CHAR_ROOT'], 'results', 'ext')
    os.makedirs(results_dir, exist_ok=True)
    out_json = os.path.join(results_dir, 'ext_char_sim.json')

    test_name_plus_params = f"test_{dut_name}_ext_char_rowcol"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    # sim_build is keyed by ELABORATION INPUTS, not the test name -- assigned
    # just before run(), once rtl_parameters and compile_args exist.
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'FPGA_CLK_HZ': str(SIM_FPGA_CLK_HZ),
        'UART_BAUD':   str(SIM_UART_BAUD),
        'USE_ROW_COL_MAJOR_ADDRESSING': '1',
        **{k: str(v) for k, v in BASE_RTL_PARAMS.items()},
    }
    extra_env = {
        'TEST_TYPE':        'ext_char',
        'EXT_CHAR_SIZES':   os.environ.get('EXT_CHAR_SIZES', '8x8,16x16'),
        'EXT_CHAR_OUT':     out_json,
        'FPGA_CLK_HZ':     str(SIM_FPGA_CLK_HZ),
        'UART_BAUD':        str(SIM_UART_BAUD),
        'TEST_LEVEL':       'gate',
        'DUT':              dut_name,
        'NUM_CHANNELS': str(BASE_RTL_PARAMS['NUM_CHANNELS']),
        'LOG_PATH':         log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED':             os.environ.get('SEED', str(random.randint(0, 100000))),
    }
    simulator = os.environ.get('SIM', 'verilator').lower()
    compile_args = [
        "--trace-fst", "--trace-structs", "--trace-depth", "99",
        "--public-flat-rw",
        "-Wno-TIMESCALEMOD", "-Wno-MULTIDRIVEN", "-Wno-WIDTHEXPAND",
        "-Wno-WIDTHTRUNC", "-Wno-SELRANGE", "-Wno-UNOPTFLAT",
        # deep monitor trans-table loops (RD_MON_MAX_TRANS>64) need unroll raised
        # The harness is SHARED with build-mon now, so its compile closure
        # includes dma_slave_monitors -> monbus_group, whose optional status
        # pins are intentionally unconnected here. Verilator promotes the
        # resulting warnings to an error ("Exiting due to N warnings"), which
        # reads as a compile failure rather than an unused-feature notice.
        "-Wno-PINMISSING", "-Wno-PINCONNECTEMPTY",
        "--unroll-count", "4096", "--unroll-stmts", "20000",
    ]

    # Keyed by elaboration inputs so cases sharing a model compile ONCE.
    sim_build = elab_sim_build(tests_dir, rtl_parameters, compile_args)
    create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    run(
        python_search=[tests_dir, _AREA + "/dv", _AREA + "/bin", _BUILD_HOST],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=COCOTB_MODULE,
        testcase="cocotb_test_stream_perf",
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        simulator=simulator,
        waves=enable_waves,
        keep_files=True,
        compile_args=compile_args,
        sim_args=["--trace", "--trace-structs", "--trace-depth", "99"],
        plus_args=['--trace'] if enable_waves else [],
    )
    print(f"PASS ext_char! JSON: {out_json}")
