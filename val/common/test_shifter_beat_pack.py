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
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, create_view_cmd

from CocoTBFramework.components.shared.field_config import FieldConfig
from CocoTBFramework.components.shared.flex_config_gen import FlexConfigGen
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.gaxi.gaxi_monitor import GAXIMonitor
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket


_NBA_SETTLE_PS = 1


class ShifterBeatPackTB(TBBase):
    """Testbench for shifter_beat_pack.

    Push side drives via GAXIMaster on push_{valid,ready,data} with a
    CHUNK_BITS-wide `data` field. Pop side drains via GAXISlave on
    pop_{valid,ready,data} with a MAX_BEAT_BITS-wide `data` field.
    Both sides share the same FlexConfigGen randomizer set so we can
    sweep named delay profiles (backtoback / fast / constrained /
    burst_pause / slow / stress / etc.).

    Golden model: a bit deque. Every push handshake appends
    CHUNK_BITS little-endian bits. Every pop handshake pulls the low
    beat_bits bits off. The scoreboard compares each captured
    pop_data against the golden's next expected beat.
    """

    CLK_PERIOD_NS = 10

    def __init__(self, dut) -> None:
        super().__init__(dut)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.SEED)
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()

        self.CHUNK_BITS     = self.convert_to_int(
            os.environ.get('CHUNK_BITS', '128'))
        self.MAX_BEAT_BYTES = self.convert_to_int(
            os.environ.get('MAX_BEAT_BYTES', '16'))
        self.CFG_BITS       = self.convert_to_int(
            os.environ.get('CFG_BITS', '8'))
        self.PROFILE        = os.environ.get('PROFILE', 'balanced')
        self.MAX_BEAT_BITS  = self.MAX_BEAT_BYTES * 8
        self.STORAGE_BITS   = 2 * self.CHUNK_BITS
        self.CFG_MAX_BYTES  = 1 << self.CFG_BITS

        # Runtime cfg — default aligner-sized 8-byte beat.
        self.beat_bytes = 8
        self.beat_bits  = self.beat_bytes * 8

        # Golden state
        self.bits: deque[int] = deque()
        self.expected_beats: List[int] = []
        self.actual_beats:   List[int] = []

        # Field configs — asymmetric widths on push vs pop side.
        self.push_field_config = FieldConfig.from_dict(
            field_dict={'data': {'bits': self.CHUNK_BITS, 'default': 0}},
            lsb_first=True,
        )
        self.pop_field_config = FieldConfig.from_dict(
            field_dict={'data': {'bits': self.MAX_BEAT_BITS, 'default': 0}},
            lsb_first=True,
        )

        # Signal maps — bind our push_/pop_ ports to the framework's
        # canonical {valid, ready, data} names.
        self.push_signal_map = {
            'valid': 'push_valid',
            'ready': 'push_ready',
            'data':  'push_data',
        }
        self.pop_signal_map = {
            'valid': 'pop_valid',
            'ready': 'pop_ready',
            'data':  'pop_data',
        }

        self._create_randomizer_manager()

    # ---------------- randomizer / profiles ----------------

    def _create_randomizer_manager(self) -> None:
        config_gen = FlexConfigGen(
            profiles=[
                'backtoback', 'fast', 'constrained', 'bursty', 'slow',
                'stress', 'moderate', 'balanced', 'heavy_pause',
                'chaotic', 'throttled',
            ],
            fields=['valid_delay', 'ready_delay'],
        )
        # A couple of sharpenings so the extremes are actually extreme.
        config_gen.backtoback.valid_delay.fixed_value(0)
        config_gen.backtoback.ready_delay.fixed_value(0)
        self.randomizer_instances = config_gen.build(return_flexrandomizer=True)

    def get_randomizer(self, profile_name: str):
        if profile_name not in self.randomizer_instances:
            self.log.warning(
                f"Profile '{profile_name}' not found; using 'balanced'")
            profile_name = 'balanced'
        return self.randomizer_instances[profile_name]

    # ---------------- BFM setup ----------------

    async def setup(self) -> None:
        # Reset first, then create BFMs so they see a stable bus.
        self.dut.cfg_beat_bytes_m1.value = self.beat_bytes - 1
        await self.start_clock('clk', freq=self.CLK_PERIOD_NS, units='ns')
        self.dut.rst_n.value = 0
        await self.wait_clocks('clk', 5)
        self.dut.rst_n.value = 1
        await self.wait_clocks('clk', 2)

        self.push_master = GAXIMaster(
            dut=self.dut,
            title='push_master',
            prefix='',
            clock=self.dut.clk,
            field_config=self.push_field_config,
            timeout_cycles=4096,
            mode='skid',
            bus_name='',
            pkt_prefix='',
            multi_sig=False,
            signal_map=self.push_signal_map,
            randomizer=self.get_randomizer(self.PROFILE),
            log=self.log,
        )

        self.pop_slave = GAXISlave(
            dut=self.dut,
            title='pop_slave',
            prefix='',
            clock=self.dut.clk,
            field_config=self.pop_field_config,
            timeout_cycles=4096,
            mode='skid',
            bus_name='',
            pkt_prefix='',
            multi_sig=False,
            signal_map=self.pop_signal_map,
            randomizer=self.get_randomizer(self.PROFILE),
            log=self.log,
        )

        # Monitor the pop side so we can scoreboard beats out of the
        # slave without racing the BFM's internal state.
        self.pop_monitor = GAXIMonitor(
            dut=self.dut,
            title='pop_mon',
            prefix='',
            clock=self.dut.clk,
            field_config=self.pop_field_config,
            is_slave=True,
            mode='skid',
            bus_name='',
            pkt_prefix='',
            multi_sig=False,
            signal_map=self.pop_signal_map,
            log=self.log,
        )
        cocotb.start_soon(self._collect_pops())

    async def _collect_pops(self) -> None:
        # Poll the monitor queue and drain into our beat list. The
        # mask must be re-evaluated on every drain because the
        # scenario may reconfigure cfg_beat_bytes mid-test.
        while True:
            await RisingEdge(self.dut.clk)
            while self.pop_monitor._recvQ:
                pkt = self.pop_monitor._recvQ.popleft()
                beat_mask = (1 << self.beat_bits) - 1
                self.actual_beats.append(int(pkt.data) & beat_mask)

    # ---------------- cfg / golden helpers ----------------

    def set_beat_bytes(self, n: int) -> None:
        self.beat_bytes = n
        self.beat_bits  = n * 8
        self.dut.cfg_beat_bytes_m1.value = n - 1

    def _golden_push(self, value: int) -> None:
        for b in range(self.CHUNK_BITS):
            self.bits.append((value >> b) & 1)
        self._replenish_expected()

    def _replenish_expected(self) -> None:
        while len(self.bits) >= self.beat_bits:
            v = 0
            for b in range(self.beat_bits):
                v |= (self.bits.popleft() & 1) << b
            self.expected_beats.append(v)

    def reset_scoreboards(self) -> None:
        self.bits.clear()
        self.expected_beats.clear()
        self.actual_beats.clear()
        self.pop_monitor._recvQ.clear()

    async def dut_reset(self) -> None:
        """Pulse rst_n, then reset the BFMs so they resync to the
        cleared bus. Cheap enough to run between scenario iterations."""
        self.dut.rst_n.value = 0
        await self.wait_clocks('clk', 4)
        self.dut.rst_n.value = 1
        await self.wait_clocks('clk', 2)
        await self.push_master.reset_bus()
        await self.pop_slave.reset_bus()

    # ---------------- drive ----------------

    async def push(self, value: int) -> None:
        self._golden_push(value)
        pkt = GAXIPacket(self.push_field_config)
        pkt.data = value
        await self.push_master.send(pkt)

    async def wait_drain(self, timeout_cycles: int = 8192) -> None:
        for _ in range(timeout_cycles):
            await RisingEdge(self.dut.clk)
            await Timer(_NBA_SETTLE_PS, units='ps')
            if len(self.actual_beats) >= len(self.expected_beats):
                return
        raise TimeoutError(
            f"drain timeout: got {len(self.actual_beats)}/"
            f"{len(self.expected_beats)} beats")

    def verify(self) -> None:
        assert len(self.actual_beats) == len(self.expected_beats), (
            f"beat count mismatch: got {len(self.actual_beats)} "
            f"expected {len(self.expected_beats)} "
            f"(beat_bytes={self.beat_bytes}, profile={self.PROFILE})"
        )
        for i, (g, e) in enumerate(
                zip(self.actual_beats, self.expected_beats)):
            assert g == e, (
                f"beat {i}: got {g:#x} expected {e:#x} "
                f"(beat_bytes={self.beat_bytes}, profile={self.PROFILE})"
            )


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

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
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
