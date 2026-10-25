# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""The board's STREAM / stream-g point profiles in simulation (stream TASK-020 phase 6).

`csv/gcompare.csv`, `csv/gscale.csv` and `csv/gscale1.csv` are rapids-g's A/B
profiles in STREAM terms; `make host-characterize ARGS="--csv csv/<p>.csv"`
runs them on the board. This runs the same points through the same host code
(host_characterize.run_one) on the harness sim, on STREAM (dut=fsm) and on
stream-g (dut=g, the STREAM_G define), one JSON per chunk in
results/sim/<profile>_<dut>_<k>of<n>.json, in the board tool's --json-output
schema. bin/compare_profiles.py puts sim and board side by side.

    make sim-gcompare | sim-gscale | sim-gscale1        (both DUTs)

Chunks are cost-balanced on the UART-op model (a UART op is ~9 us of sim time
at 4 clocks a bit; the transfer itself is small beside the descriptor writes)
so each cell stays inside the sim's time cap.
"""
import json
import os
import random
import sys

import pytest
from cocotb_test.simulator import run

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)
from test_stream_perf import (  # noqa: E402
    BASE_RTL_PARAMS, COCOTB_MODULE, FIELD_COMBO_VLT, SIM_FPGA_CLK_HZ, SIM_UART_BAUD,
    _AREA, _BUILD_HOST, elab_sim_build, verilator_unroll_args,
)
from TBClasses.shared.utilities import get_paths, create_view_cmd  # noqa: E402
from TBClasses.shared.filelist_utils import get_sources_from_filelist  # noqa: E402

sys.path.insert(0, os.path.join(_AREA, 'bin'))
from descriptor_builder import load_configs_from_csv  # noqa: E402

CSV_DIR = os.path.abspath(os.path.join(_HERE, '..', '..', 'csv'))
RESULTS_DIR = os.path.abspath(os.path.join(_HERE, '..', '..', 'results', 'sim'))
PROFILES = ('gcompare', 'gscale', 'gscale1')
DUTS = ('fsm', 'g')
# UART ops per point (host_characterize: descriptor words, config, kicks, polls);
# ~9 us of sim time each at 25 Mbaud. Budget per chunk keeps a cell under the
# 100 ms cap with the transfer and the warm-up ping on top.
COST_FIXED, COST_PER_DESC, COST_PER_CH, CHUNK_BUDGET = 140, 14, 12, 4000
BEATS_PER_OP = 900   # a UART op is ~9 us of sim time; a beat is a cycle, so the transfer counts too


def _cost(c):
    beats = (c.transfer_bytes // 16) * c.num_channels * c.descriptors_per_channel
    return (COST_FIXED + COST_PER_DESC * c.num_channels * c.descriptors_per_channel
            + COST_PER_CH * c.num_channels + beats // BEATS_PER_OP)


def chunks(profile):
    """Contiguous, cost-balanced slices of the profile's point names."""
    cfgs = load_configs_from_csv(os.path.join(CSV_DIR, f'{profile}.csv'))
    out, cur, acc = [], [], 0
    for c in cfgs:
        if cur and acc + _cost(c) > CHUNK_BUDGET:
            out.append(cur); cur, acc = [], 0
        cur.append(c.name); acc += _cost(c)
    if cur:
        out.append(cur)
    return out


def _cells():
    cells = []
    for prof in PROFILES:
        ch = chunks(prof)
        for dut in DUTS:
            for k, names in enumerate(ch, 1):
                cells.append(pytest.param(prof, dut, k, len(ch), names, id=f'{prof}-{dut}-{k}of{len(ch)}'))
    return cells


@pytest.mark.parametrize('profile, dut, k, n, names', _cells())
def test_stream_g_profile(request, profile, dut, k, n, names):
    module, repo_root_path, tests_dir, log_dir, rtl_dict = get_paths({
        'stream_harness': 'projects/fpga-systems/Genesys2/dma-ip/stream',
    })
    dut_name = 'stream_harness'
    for var, rel in (('STREAM_ROOT', 'projects/components/dma-ip/stream'),
                     ('CONVERTERS_ROOT', 'projects/components/utility-ip/converters'),
                     ('MISC_ROOT', 'projects/components/utility-ip/misc'),
                     ('STREAM_CHAR_ROOT', 'projects/fpga-systems/Genesys2/dma-ip/stream'),
                     ('STREAM_CHAR_FRAMEWORK_ROOT', 'projects/fpga-systems/Genesys2/dma-ip/stream'),
                     ('FRAMEWORK_ROOT', 'projects/fpga-systems/Genesys2/dma-ip/stream')):
        os.environ[var] = os.path.join(repo_root_path, rel)
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_path,
        filelist_path='projects/fpga-systems/Genesys2/dma-ip/stream/rtl/filelists/stream_harness.f')
    os.makedirs(RESULTS_DIR, exist_ok=True)
    out_json = os.path.join(RESULTS_DIR, f'{profile}_{dut}_{k}of{n}.json')
    if os.path.exists(out_json):
        os.remove(out_json)
    name = f'test_{dut_name}_profile_{profile}_{dut}_{k}of{n}'
    log_path = os.path.join(log_dir, f'{name}.log')
    os.makedirs(log_dir, exist_ok=True)
    stream_g = (dut == 'g')
    # The board's perf geometry, as test_stream_perf builds it: the package
    # defaults plus USE_AXI_MONITORS=0 -- the package says 1, and a first run of
    # this file took it, which built the in-core monitors into a sim meant to
    # match a bitstream that has none (the scope was g_stream_core_mon_enabled).
    rtl_parameters = {
        'FPGA_CLK_HZ': str(SIM_FPGA_CLK_HZ),
        'UART_BAUD': str(SIM_UART_BAUD),
        'USE_AXI_MONITORS': '0',
        'USE_ROW_COL_MAJOR_ADDRESSING': '1',
        **{kk: str(v) for kk, v in BASE_RTL_PARAMS.items()},
    }
    # CHAR_POINTS=a,b overrides the chunk's points (any names in the profile, or in
    # CHAR_CSV_OVERRIDE); CHAR_TRACE_OUT adds the channel-0 scheduler trace (TASK-021).
    if os.environ.get('CHAR_POINTS'):
        names = [n for n in os.environ['CHAR_POINTS'].split(',') if n]
    extra_env = {
        'TEST_TYPE': 'char_csv',
        'CHAR_CSV': os.environ.get('CHAR_CSV_OVERRIDE') or os.path.join(CSV_DIR, f'{profile}.csv'),
        'CHAR_CONFIGS': ','.join(names),
        **({'CHAR_TRACE_OUT': os.environ['CHAR_TRACE_OUT']} if os.environ.get('CHAR_TRACE_OUT') else {}),
        'CHAR_OUT': out_json,
        'SIM_TIMEOUT_MS': os.environ.get('SIM_TIMEOUT_MS', '300'),   # sim time; the 1 MB x 8 ch point alone is 5.2 ms
        'TEST_STREAM_G': '1' if stream_g else '0',
        'FPGA_CLK_HZ': str(SIM_FPGA_CLK_HZ),
        'UART_BAUD': str(SIM_UART_BAUD),
        'TEST_LEVEL': 'gate',
        'DUT': dut_name,
        'NUM_CHANNELS': str(BASE_RTL_PARAMS['NUM_CHANNELS']),
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{name}.xml'),
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
    }
    compile_args = [
        "--trace-fst", "--trace-structs", "--trace-depth", "99",
        "--public-flat-rw", "-Wno-TIMESCALEMOD",
        *(['+define+STREAM_G'] if stream_g else []),
        FIELD_COMBO_VLT, "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC", "-Wno-SELRANGE", "-Wno-UNOPTFLAT",
        "-Wno-PINMISSING", "-Wno-PINCONNECTEMPTY",
        *verilator_unroll_args(),
    ]
    sim_build = elab_sim_build(tests_dir, rtl_parameters, compile_args)
    create_view_cmd(log_dir, log_path, sim_build, module, name)
    os.makedirs(sim_build, exist_ok=True)
    run(
        python_search=[tests_dir, _AREA + "/dv", _AREA + "/bin", _BUILD_HOST],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=COCOTB_MODULE, testcase="cocotb_test_stream_perf",
        parameters=rtl_parameters, sim_build=sim_build, extra_env=extra_env,
        simulator=os.environ.get('SIM', 'verilator').lower(), waves=False, keep_files=True,
        compile_args=compile_args, sim_args=["--trace", "--trace-structs", "--trace-depth", "99"],
    )
    assert os.path.isfile(out_json), f"{name}: no results JSON"
    with open(out_json) as fh:
        doc = json.load(fh)
    assert [d['config'] for d in doc] == names
    if os.environ.get('CHAR_POINTS'):
        return   # an ad-hoc point list is a probe, not the profile's pass/fail
    assert all(d['result']['pass'] for d in doc), [d['config'] for d in doc if not d['result']['pass']]
