# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Tests for rtl/common/shifter_beat_pack.sv.
#
# The push side is driven by a GAXIMaster (chunk-wide data). The pop
# side is drained by a GAXISlave (max-beat-wide data). Delay profiles
# come from FlexConfigGen so we sweep backtoback / fast / constrained
# / burst_pause / etc. against the DUT — the aligner-race regression
# story (#31) is exactly what this profile mix catches.

import os
import random
from collections import deque
from typing import List

import cocotb
import pytest
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.common.shifter_beat_pack_tb import ShifterBeatPackTB
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from cov_utils.conftest_coverage import get_coverage_compile_args

from CocoTBFramework.components.shared.field_config import FieldConfig
from CocoTBFramework.components.shared.flex_config_gen import FlexConfigGen
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.gaxi.gaxi_monitor import GAXIMonitor
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket






# ---------------------------------------------------------------------------
# Scenarios
# ---------------------------------------------------------------------------


def _rand_chunk(rng: random.Random, chunk_bits: int) -> int:
    return rng.getrandbits(chunk_bits)


def _default_beat_bytes(tb: ShifterBeatPackTB) -> int:
    """Pick a nominal beat size for scenarios that don't sweep it —
    aligner-sized 8 bytes when possible, otherwise the largest the
    instance can actually encode."""
    return min(8, tb.MAX_BEAT_BYTES, tb.CHUNK_BITS // 8, tb.CFG_MAX_BYTES)


async def _smoke(tb: ShifterBeatPackTB) -> None:
    rng = random.Random(tb.SEED ^ 0xA1)
    tb.set_beat_bytes(_default_beat_bytes(tb))
    await tb.push(_rand_chunk(rng, tb.CHUNK_BITS))
    await tb.wait_drain()
    tb.verify()


async def _burst_many_chunks(tb: ShifterBeatPackTB) -> None:
    """Push many chunks in one go, then wait for all beats to drain."""
    rng = random.Random(tb.SEED ^ 0xA2)
    tb.set_beat_bytes(_default_beat_bytes(tb))
    n = {'gate': 8, 'func': 32, 'full': 128}.get(tb.TEST_LEVEL, 32)
    for _ in range(n):
        await tb.push(_rand_chunk(rng, tb.CHUNK_BITS))
    await tb.wait_drain()
    tb.verify()


async def _beat_size_sweep(tb: ShifterBeatPackTB) -> None:
    """Try every power-of-2 beat width up to CHUNK_BITS/8 (also capped
    by what CFG_BITS can encode). Each size iterates from a clean
    DUT reset so residual bits from the prior cfg can't leak in."""
    rng = random.Random(tb.SEED ^ 0xA3)
    max_bytes = min(tb.MAX_BEAT_BYTES, tb.CHUNK_BITS // 8, tb.CFG_MAX_BYTES)
    sizes = []
    n = 1
    while n <= max_bytes:
        sizes.append(n)
        n *= 2
    n_pushes = {'gate': 2, 'func': 4, 'full': 8}.get(tb.TEST_LEVEL, 4)
    for beat_bytes in sizes:
        # Full reset between sizes — the DUT's r_data holds a
        # cfg-relative view of its bits, and mid-run cfg changes
        # would race a partially-drained beat.
        await tb.dut_reset()
        tb.reset_scoreboards()
        tb.set_beat_bytes(beat_bytes)
        for _ in range(n_pushes):
            await tb.push(_rand_chunk(rng, tb.CHUNK_BITS))
        await tb.wait_drain()
        tb.verify()


# ---------------------------------------------------------------------------
# CocoTB dispatch
# ---------------------------------------------------------------------------


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_shifter_beat_pack(dut):
    test_type = os.environ.get('TEST_TYPE', 'smoke')
    tb = ShifterBeatPackTB(dut)
    await tb.setup()

    scenarios = {
        'smoke':             _smoke,
        'burst_many_chunks': _burst_many_chunks,
        'beat_size_sweep':   _beat_size_sweep,
    }
    if test_type not in scenarios:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")
    await scenarios[test_type](tb)
    await tb.wait_clocks('clk', 20)


# ---------------------------------------------------------------------------
# Pytest matrix
# ---------------------------------------------------------------------------


_ALL_TYPES = ['smoke', 'burst_many_chunks', 'beat_size_sweep']

# Delay profiles from FlexConfigGen. FULL sweeps every one; FUNC picks
# a representative subset; GATE just the backtoback baseline.
_PROFILES_GATE = ['backtoback']
_PROFILES_FUNC = ['backtoback', 'balanced', 'burst_pause', 'slow']
_PROFILES_FULL = [
    'backtoback', 'fast', 'constrained', 'bursty', 'slow', 'stress',
    'moderate', 'balanced', 'heavy_pause', 'chaotic', 'throttled',
]

# Chunk / beat / cfg sizing combos.
_COMBOS_GATE = [(128, 16, 8)]
_COMBOS_FUNC = [(128, 16, 8)]
_COMBOS_FULL = [
    ( 64,  4, 8),
    (128,  8, 4),
    (128, 16, 8),
    (256, 16, 8),
    (256, 32, 8),
]


def _matrix(types, combos, profiles):
    return [(t, c, b, g, p)
            for (c, b, g) in combos
            for t in types
            for p in profiles]


_GATE = _matrix(_ALL_TYPES, _COMBOS_GATE, _PROFILES_GATE)
_FUNC = _matrix(_ALL_TYPES, _COMBOS_FUNC, _PROFILES_FUNC)
_FULL = _matrix(_ALL_TYPES, _COMBOS_FULL, _PROFILES_FULL)

# The GRID comes from REG_LEVEL; TEST_LEVEL is the per-test depth knob and
# selecting the matrix with it meant `TEST_LEVEL=full` silently expanded the
# parameter sweep as well as the depth, while REG_LEVEL did nothing at all.
_REG_LEVEL = os.environ.get('REG_LEVEL', 'FUNC').upper()
_PARAMS = {'GATE': _GATE, 'FUNC': _FUNC, 'FULL': _FULL}.get(
    _REG_LEVEL, _FUNC)
# Depth defaults to the matching level, still overridable on its own.
_TEST_LEVEL = os.environ.get('TEST_LEVEL', _REG_LEVEL).upper()


@pytest.mark.parametrize(
    'test_type,chunk_bits,max_beat_bytes,cfg_bits,profile', _PARAMS,
    ids=[f"{t[0]}-c{t[1]}-b{t[2]}-cfg{t[3]}-{t[4]}" for t in _PARAMS])
def test_shifter_beat_pack(request, test_type, chunk_bits, max_beat_bytes,
                           cfg_bits, profile):
    module, repo_root, tests_dir, log_dir, _ = get_paths({
        'rtl_cmn': 'rtl/common'})

    dut_name = 'shifter_beat_pack'
    toplevel = dut_name

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/shifter_beat_pack.f')

    test_name = (
        f"test_{dut_name}_{test_type}_c{chunk_bits}"
        f"_b{max_beat_bytes}_cfg{cfg_bits}_{profile}"
    )
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name = f"{test_name}_{worker_id}"

    sim_build = sim_build_path(tests_dir, test_name)
    log_path     = os.path.join(log_dir, f"{test_name}.log")
    results_path = os.path.join(log_dir, f"results_{test_name}.xml")
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        'DUT':                 dut_name,
        'LOG_PATH':            log_path,
        'COCOTB_LOG_LEVEL':    'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED':                os.environ.get('SEED', str(random.randint(0, 100000))),
        'TEST_TYPE':           test_type,
        'TEST_LEVEL':          _TEST_LEVEL.lower(),
        'CHUNK_BITS':          str(chunk_bits),
        'MAX_BEAT_BYTES':      str(max_beat_bytes),
        'CFG_BITS':            str(cfg_bits),
        'PROFILE':             profile,
    }

    parameters = {
        'CHUNK_BITS':     str(chunk_bits),
        'MAX_BEAT_BYTES': str(max_beat_bytes),
        'CFG_BITS':       str(cfg_bits),
    }

    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    extra_args = ['--trace-fst', '--trace-structs', '-Wno-TIMESCALEMOD']

    # Verilator --coverage flags when COVERAGE=1, else nothing. Without this
    # the run produces no coverage.dat at all and `make coverage-report`
    # silently reports 0.0% from 0 merged files.
    extra_args.extend(get_coverage_compile_args())
    sim_args   = ['--trace'] if enable_waves else []

    cmd_filename = create_view_cmd(
        log_dir, log_path, sim_build, module, test_name)

    try:
        run(python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            extra_args=extra_args,
            plus_args=sim_args,
            waves=enable_waves)
    except Exception:
        print(f"Test failed. Logs: {log_path}")
        print(f"View waves: {cmd_filename}")
        raise
