# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: ShifterBeatPackTB
# Purpose: Testbench for shifter_beat_pack
# Subsystem: framework
#
# Extracted from val/common/test_shifter_beat_pack.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
from collections import deque
from typing import List
import cocotb
from cocotb.triggers import RisingEdge, Timer
from TBClasses.shared.tbbase import TBBase
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
        # Record it. The wrapper picks a fresh random SEED every run, so a
        # failure is only reproducible if the value reaches the log --
        # otherwise "rerun with SEED=<n>" has no n ([[seeds-and-determinism]]).
        self.log.info(f"shifter_beat_pack: SEED={self.SEED}, "
                      f"TEST_LEVEL={self.TEST_LEVEL}")

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

    # ---- contract lifecycle (/GLOBAL_REQUIREMENTS.md 2.2) ----------------
    # Mandatory on every TB. This class inherited TBBase's stubs, which
    # only log "should be overridden" and drive nothing -- nominally
    # compliant, functionally absent. Wraps the reset path this TB
    # already used, so behaviour is unchanged.

    async def assert_reset(self):
        """Assert reset."""
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        """Release reset."""
        self.dut.rst_n.value = 1

    async def setup_clocks_and_reset(self):
        """Start the clock and drive the full reset sequence."""
        await self.start_clock('clk', 10, 'ns')
        await self.assert_reset()
        await self.wait_clocks('clk', 5)
        await self.deassert_reset()
        await self.wait_clocks('clk', 5)

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
