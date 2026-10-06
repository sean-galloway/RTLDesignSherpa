"""
amber_tag_array testbench

Per-way tag+state store. The DUT has a clock but NO reset port (GLOBAL_REQUIREMENTS
1.4: SRAM carries no reset); line validity after reset is amber_control's job
(MAS ch02_blocks/03: init walk writes STATE_I to every way). The TB performs
that same init walk so every modeled location has a deterministic golden value,
then checks both combinational lookup ports against a dictionary model.

Geometry arrives via environment (set by the pytest wrapper from the
parametrized grid); widths are recomputed here with the same formulas as
amber_pkg so a parameter mismatch between wrapper and TB cannot pass silently.

Author: RTL Design Sherpa
Created: 2026-10-06
"""

import os
import random

from cocotb.triggers import RisingEdge, Timer

from TBClasses.shared.tbbase import TBBase


class AmberTagArrayTB(TBBase):
    """Drives amber_tag_array and scores both lookup ports against a model."""

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
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('ADDR_WIDTH', '32'))
        self.LINE_BYTES = self.convert_to_int(os.environ.get('LINE_BYTES', '64'))
        self.SET_INDEX_WIDTH = (self.SETS - 1).bit_length()
        self.TAG_WIDTH = self.ADDR_WIDTH - self.SET_INDEX_WIDTH \
            - (self.LINE_BYTES - 1).bit_length()
        self.TAG_STATE_WIDTH = self.TAG_WIDTH + 3
        self.STATE_I = 0
        self.checks = 0
        self.mismatches = 0
        self.model = {}
        self.log.info(f"AmberTagArrayTB sets={self.SETS} ways={self.WAYS} "
                      f"addr_width={self.ADDR_WIDTH} line_bytes={self.LINE_BYTES} "
                      f"tag_width={self.TAG_WIDTH} level={self.TEST_LEVEL} "
                      f"seed={self.SEED}")

    # -- the three mandatory methods; clock but no reset port ----------------
    async def setup_clocks_and_reset(self):
        await self.start_clock('clk', freq=10, units='ns')

    async def assert_reset(self):
        await Timer(1, units='ns')

    async def deassert_reset(self):
        await Timer(1, units='ns')

    # -- drivers ----------------------------------------------------------------
    async def write_entry(self, set_idx, way, tag_state):
        """One write through the shared write port; updates the model."""
        self.dut.wr_en.value = 1
        self.dut.wr_way_onehot.value = 1 << way
        self.dut.wr_set.value = set_idx
        self.dut.wr_tag_state.value = tag_state
        await RisingEdge(self.dut.clk)
        self.dut.wr_en.value = 0
        self.model[(set_idx, way)] = tag_state

    async def init_walk(self):
        """Write STATE_I everywhere -- the amber_control post-reset init
        sequence, performed here so unwritten locations cannot leak X's."""
        for way in range(self.WAYS):
            for set_idx in range(self.SETS):
                await self.write_entry(set_idx, way, self.STATE_I)

    async def read_check_set(self, set_idx):
        """Both lookup ports at the same set; every way scored."""
        self.dut.a_set.value = set_idx
        self.dut.b_set.value = set_idx
        await Timer(1, units='ns')
        mask = (1 << self.TAG_STATE_WIDTH) - 1
        for port in ('a_tag_state', 'b_tag_state'):
            vec = int(getattr(self.dut, port).value)
            for way in range(self.WAYS):
                got = (vec >> (way * self.TAG_STATE_WIDTH)) & mask
                exp = self.model[(set_idx, way)]
                self._score(f"{port}[set={set_idx}][way={way}]", got, exp)

    # -- scoring --------------------------------------------------------------
    def _score(self, what, got, exp):
        self.checks += 1
        if got != exp:
            self.mismatches += 1
            if self.mismatches <= 20:
                self.log.error(f"{what}: got 0x{got:X} expected 0x{exp:X}")

    def _entry_value(self, set_idx, way):
        """Distinct, packing-sensitive value per location: the tag field
        carries a nonzero pattern, the state field cycles I/S/E/M."""
        tag = ((set_idx << 8) | (way << 4) | 0x5) & ((1 << self.TAG_WIDTH) - 1)
        state = (set_idx + way) % 4
        return (tag << 3) | state

    # -- tests ------------------------------------------------------------------
    async def run(self) -> bool:
        await self.init_walk()

        # Directed: every way of set 0, distinct values, both ports.
        for way in range(self.WAYS):
            await self.write_entry(0, way, self._entry_value(0, way))
        await self.read_check_set(0)

        # Level-scaled random traffic: writes then spot reads on both ports.
        n_ops = self.OP_COUNTS[self.TEST_LEVEL]
        for _ in range(n_ops):
            set_idx = random.randrange(self.SETS)
            way = random.randrange(self.WAYS)
            await self.write_entry(set_idx, way,
                                   random.randrange(1 << self.TAG_STATE_WIDTH))
        n_reads = max(4, n_ops // 4)
        for _ in range(n_reads):
            await self.read_check_set(random.randrange(self.SETS))

        # Full: exhaustive unique-value write then exhaustive readback.
        if self.TEST_LEVEL == 'full':
            for way in range(self.WAYS):
                for set_idx in range(self.SETS):
                    await self.write_entry(set_idx, way,
                                           self._entry_value(set_idx, way))
            for set_idx in range(self.SETS):
                await self.read_check_set(set_idx)

        return self.mismatches == 0

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches}
