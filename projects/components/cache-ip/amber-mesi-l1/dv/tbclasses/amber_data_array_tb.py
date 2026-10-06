"""
amber_data_array testbench

Per-way line-data store with byte-write enables. The DUT has a clock but NO
reset port (GLOBAL_REQUIREMENTS 1.4); the TB zero-fills every location first
(the fill-side equivalent of the tag init walk) so the model is total.

Checks: full-beat writes, byte-enable partial writes (unselected bytes must
be preserved), per-way isolation, {set, beat} addressing on both read ports,
and level-scaled random traffic against a dictionary model.

Author: RTL Design Sherpa
Created: 2026-10-06
"""

import os
import random

from cocotb.triggers import RisingEdge, Timer

from TBClasses.shared.tbbase import TBBase


class AmberDataArrayTB(TBBase):
    """Drives amber_data_array and scores both read ports against a model."""

    OP_COUNTS = {'gate': 16, 'func': 128, 'full': 1024}

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        if self.TEST_LEVEL not in self.OP_COUNTS:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'gate'")
            self.TEST_LEVEL = 'gate'
        random.seed(self.SEED)
        self.SETS = self.convert_to_int(os.environ.get('SETS', '128'))
        self.WAYS = self.convert_to_int(os.environ.get('WAYS', '4'))
        self.LINE_BYTES = self.convert_to_int(os.environ.get('LINE_BYTES', '64'))
        self.BUS_WIDTH = self.convert_to_int(os.environ.get('BUS_WIDTH', '64'))
        self.SET_INDEX_WIDTH = (self.SETS - 1).bit_length()
        self.FILL_BEATS = self.LINE_BYTES // (self.BUS_WIDTH // 8)
        self.BEAT_INDEX_WIDTH = (self.FILL_BEATS - 1).bit_length()
        self.STRB_W = self.BUS_WIDTH // 8
        self.checks = 0
        self.mismatches = 0
        self.model = {}
        self.log.info(f"AmberDataArrayTB sets={self.SETS} ways={self.WAYS} "
                      f"line_bytes={self.LINE_BYTES} bus_width={self.BUS_WIDTH} "
                      f"fill_beats={self.FILL_BEATS} level={self.TEST_LEVEL} "
                      f"seed={self.SEED}")

    # -- the three mandatory methods; clock but no reset port ----------------
    async def setup_clocks_and_reset(self):
        await self.start_clock('clk', freq=10, units='ns')

    async def assert_reset(self):
        await Timer(1, units='ns')

    async def deassert_reset(self):
        await Timer(1, units='ns')

    # -- helpers ------------------------------------------------------------------
    def _addr(self, set_idx, beat):
        return (set_idx << self.BEAT_INDEX_WIDTH) | beat

    def _be_mask(self, be):
        mask = 0
        for b in range(self.STRB_W):
            if be & (1 << b):
                mask |= 0xFF << (8 * b)
        return mask

    # -- drivers ----------------------------------------------------------------
    async def write_beat(self, way, set_idx, beat, data, be):
        """One beat through the shared write port; byte-enables merge into
        the model exactly as the DUT must merge them into the array."""
        self.dut.wr_en.value = 1
        self.dut.wr_way_onehot.value = 1 << way
        self.dut.wr_addr.value = self._addr(set_idx, beat)
        self.dut.wr_wdata.value = data
        self.dut.wr_be.value = be
        await RisingEdge(self.dut.clk)
        self.dut.wr_en.value = 0
        key = (way, set_idx, beat)
        if be == (1 << self.STRB_W) - 1:
            self.model[key] = data & ((1 << self.BUS_WIDTH) - 1)
        else:
            keep = self._be_mask(be)
            self.model[key] = (self.model[key] & ~keep) | (data & keep)

    async def zero_fill(self):
        for way in range(self.WAYS):
            for set_idx in range(self.SETS):
                for beat in range(self.FILL_BEATS):
                    await self.write_beat(way, set_idx, beat, 0,
                                          (1 << self.STRB_W) - 1)

    async def read_check(self, way, set_idx, beat):
        self.dut.a_addr.value = self._addr(set_idx, beat)
        self.dut.a_way.value = way
        self.dut.b_addr.value = self._addr(set_idx, beat)
        self.dut.b_way.value = way
        await Timer(1, units='ns')
        exp = self.model[(way, set_idx, beat)]
        self._score(f"a_rdata[way={way}][set={set_idx}][beat={beat}]",
                    int(self.dut.a_rdata.value), exp)
        self._score(f"b_rdata[way={way}][set={set_idx}][beat={beat}]",
                    int(self.dut.b_rdata.value), exp)

    # -- scoring --------------------------------------------------------------
    def _score(self, what, got, exp):
        self.checks += 1
        if got != exp:
            self.mismatches += 1
            if self.mismatches <= 20:
                self.log.error(f"{what}: got 0x{got:X} expected 0x{exp:X}")

    def _beat_value(self, way, set_idx, beat):
        return ((way + 1) << 24) | ((set_idx & 0xFFFF) << 8) | (beat << 2) | 0x1

    # -- tests ------------------------------------------------------------------
    async def run(self) -> bool:
        full_be = (1 << self.STRB_W) - 1
        await self.zero_fill()

        # Directed: full-beat write and readback on both ports, way isolation.
        await self.write_beat(0, 0, 0, 0xDEADBEEFCAFEBABE & ((1 << self.BUS_WIDTH) - 1), full_be)
        await self.write_beat(1, 0, 0, self._beat_value(1, 0, 0), full_be)
        await self.read_check(0, 0, 0)
        await self.read_check(1, 0, 0)

        # Directed: byte-enable partial write preserves the rest of the beat.
        if self.STRB_W > 1:
            await self.write_beat(0, 0, 1, 0xA5 & ((1 << self.BUS_WIDTH) - 1), 0x1)
            await self.write_beat(0, 0, 1, 0x5A & ((1 << self.BUS_WIDTH) - 1),
                                  1 << (self.STRB_W - 1))
            await self.read_check(0, 0, 1)

        # Level-scaled random traffic, mixing full and partial writes.
        n_ops = self.OP_COUNTS[self.TEST_LEVEL]
        for _ in range(n_ops):
            way = random.randrange(self.WAYS)
            set_idx = random.randrange(self.SETS)
            beat = random.randrange(self.FILL_BEATS)
            data = random.randrange(1 << self.BUS_WIDTH)
            if self.STRB_W > 1 and random.random() < 0.4:
                be = random.randrange(1, 1 << self.STRB_W)
            else:
                be = full_be
            await self.write_beat(way, set_idx, beat, data, be)
        n_reads = max(4, n_ops // 4)
        for _ in range(n_reads):
            await self.read_check(random.randrange(self.WAYS),
                                  random.randrange(self.SETS),
                                  random.randrange(self.FILL_BEATS))

        # Full: exhaustive unique-value round trip over the whole array.
        if self.TEST_LEVEL == 'full':
            for way in range(self.WAYS):
                for set_idx in range(self.SETS):
                    for beat in range(self.FILL_BEATS):
                        await self.write_beat(way, set_idx, beat,
                                              self._beat_value(way, set_idx, beat),
                                              full_be)
            for way in range(self.WAYS):
                for set_idx in range(self.SETS):
                    for beat in range(self.FILL_BEATS):
                        await self.read_check(way, set_idx, beat)

        return self.mismatches == 0

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches}
