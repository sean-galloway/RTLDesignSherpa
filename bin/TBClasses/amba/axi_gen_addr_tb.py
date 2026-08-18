# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: AxiGenAddrTB
# Purpose: Testbench for axi_gen_addr — next-address generation for AXI bursts
# Subsystem: framework
#
# TB class lives here per rtl/amba/CLAUDE.md Rule #0 and GLOBAL_REQUIREMENTS
# 2.1/2.3; val/amba/test_axi_gen_addr.py holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os

import cocotb
from cocotb.triggers import Timer

from TBClasses.shared.tbbase import TBBase


# Burst encodings (AXI: 00 FIXED, 01 INCR, 10 WRAP, 11 reserved)
FIXED, INCR, WRAP, RESERVED = 0, 1, 2, 3


class AxiGenAddrTB(TBBase):
    """Testbench for axi_gen_addr.

    The DUT is depended on by ~38 files — every splitter, width
    converter and DMA slave that walks a burst — and had no test of its
    own. A wrong increment or wrap boundary here surfaces far downstream
    as one corrupted beat in a burst.

    Checks are written against the AXI addressing rules rather than
    against the implementation, so the model is an independent opinion:

    * FIXED never moves.
    * INCR advances 1<<size, except that a narrower output bus caps the
      step at the output width in bytes — the cap the width converters
      rely on.
    * WRAP keeps the high bits and wraps inside a
      (1<<size) * (len+1) byte container.
    * next_addr_align masks off the output-width byte offset.
    * Reserved burst 2'b11 follows the RTL's documented INCR default.
    """

    def __init__(self, dut):
        super().__init__(dut)

        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate')
        self.AW = self.convert_to_int(os.environ.get('TEST_AW', '32'))
        self.DW = self.convert_to_int(os.environ.get('TEST_DW', '32'))
        self.ODW = self.convert_to_int(os.environ.get('TEST_ODW', '32'))
        self.LEN = self.convert_to_int(os.environ.get('TEST_LEN', '8'))

        self.max_size = (self.DW // 8).bit_length() - 1
        self.addr_mask = (1 << self.AW) - 1
        self.odw_bytes = self.ODW // 8

        # Random depth scales with level; the directed cases below run at
        # every level because they are the ones that pin the contract.
        self.random_vectors = {
            'gate': 100, 'func': 400, 'full': 2000,
        }.get(self.TEST_LEVEL, 100)

        self.errors = 0

    # ---- three mandatory TB methods (GLOBAL_REQUIREMENTS 2.2) ----------
    #
    # axi_gen_addr is purely combinational: it has no clock and no reset
    # port. The methods are implemented because the rule is unconditional
    # and a mid-test reset hook must exist wherever a caller expects one;
    # here they legitimately have nothing to drive.

    async def setup_clocks_and_reset(self):
        """No clock or reset on a combinational DUT — settle inputs only."""
        self.dut.curr_addr.value = 0
        self.dut.size.value = 0
        self.dut.burst.value = 0
        self.dut.len.value = 0
        await Timer(1, units='ns')
        self.log.info(f"@ {cocotb.utils.get_sim_time('ns')}ns: "
                      f"axi_gen_addr TB ready: AW={self.AW} DW={self.DW} "
                      f"ODW={self.ODW} LEN={self.LEN} level={self.TEST_LEVEL}")

    async def assert_reset(self):
        """No reset port on this DUT."""
        return

    async def deassert_reset(self):
        """No reset port on this DUT."""
        return

    # ---- golden model --------------------------------------------------

    def expected(self, curr_addr, size, burst, length):
        """(next_addr, next_addr_align) per the AXI addressing rules."""
        increment = min(1 << size, self.odw_bytes)

        if burst == FIXED:
            nxt = curr_addr
        elif burst == WRAP:
            wrap_mask = ((1 << size) * (length + 1) - 1) & self.addr_mask
            aligned = ((curr_addr + increment) & ~(increment - 1)) & self.addr_mask
            nxt = (curr_addr & ~wrap_mask) | (aligned & wrap_mask)
        else:                                   # INCR and the reserved arm
            nxt = curr_addr + increment

        nxt &= self.addr_mask
        return nxt, nxt & ~((self.odw_bytes - 1) & self.addr_mask)

    # ---- checks ---------------------------------------------------------

    async def check(self, addr, size, burst, length, note=""):
        addr &= self.addr_mask
        self.dut.curr_addr.value = addr
        self.dut.size.value = size
        self.dut.burst.value = burst
        self.dut.len.value = length
        await Timer(1, units='ns')

        exp_next, exp_align = self.expected(addr, size, burst, length)
        got_next = int(self.dut.next_addr.value)
        got_align = int(self.dut.next_addr_align.value)

        ctx = (f"addr=0x{addr:08X} size={size} burst={burst} len={length}"
               f"{(' ' + note) if note else ''}")
        if got_next != exp_next:
            self.log.error(f"@ {cocotb.utils.get_sim_time('ns')}ns: "
                           f"next_addr {ctx}: got 0x{got_next:08X} "
                           f"exp 0x{exp_next:08X}")
            self.errors += 1
        if got_align != exp_align:
            self.log.error(f"@ {cocotb.utils.get_sim_time('ns')}ns: "
                           f"next_addr_align {ctx}: got 0x{got_align:08X} "
                           f"exp 0x{exp_align:08X}")
            self.errors += 1

    async def test_fixed_never_moves(self):
        for size in range(self.max_size + 1):
            for addr in (0x0000_0000, 0x0000_1000, 0x1234_5678, 0xDEAD_BEE0):
                await self.check(addr, size, FIXED, 3, note="fixed")

    async def test_incr_steps_by_size(self):
        for size in range(self.max_size + 1):
            for addr in (0x0000_0000, 0x0000_0004, 0x0000_0FF8, 0x8000_0000):
                await self.check(addr, size, INCR, 7, note="incr")

    async def test_incr_crosses_4k(self):
        """This block does not split at 4 KB. Pinning that keeps a
        'helpful' boundary clamp from being added silently."""
        for size in range(self.max_size + 1):
            await self.check(0x0000_1000 - (1 << size), size, INCR, 0,
                             note="pre-4k")
            await self.check(0x0000_0FFF, size, INCR, 0, note="unaligned-4k")

    async def test_wrap_containers(self):
        """WRAP stays inside (1<<size)*(len+1) bytes. AXI permits wrap
        only for lengths of 2/4/8/16, so walk exactly those."""
        for length in (1, 3, 7, 15):
            for size in range(self.max_size + 1):
                base = 0x0002_0000
                for beat in range(length + 1):
                    await self.check(base + beat * (1 << size), size, WRAP,
                                     length, note="wrap")

    async def test_wrap_returns_to_base(self):
        """A full wrap walk returns to its start — the property that
        makes it a wrap rather than an increment.

        The step count is container/increment, NOT len+1. Those differ
        exactly when a narrower output caps the increment, because that
        is the downsizing case: one input beat becomes two output beats
        and the caller iterates on the output side. Stating it as len+1
        asserts the caller's beat count instead of the addressing rule,
        and flagged correct RTL when this test was first written.
        """
        for length in (1, 3, 7, 15):
            for size in range(self.max_size + 1):
                container = (1 << size) * (length + 1)
                increment = min(1 << size, self.odw_bytes)
                steps = container // increment
                start = 0x0004_0000 + increment * 2
                addr = start
                for _ in range(steps):
                    self.dut.curr_addr.value = addr
                    self.dut.size.value = size
                    self.dut.burst.value = WRAP
                    self.dut.len.value = length
                    await Timer(1, units='ns')
                    addr = int(self.dut.next_addr.value)
                if addr != start:
                    self.log.error(
                        f"@ {cocotb.utils.get_sim_time('ns')}ns: wrap did not "
                        f"close: size={size} len={length} inc={increment} "
                        f"steps={steps} start=0x{start:08X} end=0x{addr:08X}")
                    self.errors += 1

    async def test_reserved_burst_behaves_as_incr(self):
        for size in range(self.max_size + 1):
            await self.check(0x0000_2000, size, RESERVED, 3, note="reserved")

    async def test_random(self):
        import random
        rng = random.Random(self.SEED)
        n = self.random_vectors
        self.log.info(f"@ {cocotb.utils.get_sim_time('ns')}ns: random pass: "
                      f"{n} vectors, seed={self.SEED}")
        for _ in range(n):
            await self.check(rng.randrange(1 << self.AW),
                             rng.randrange(self.max_size + 1),
                             rng.choice((FIXED, INCR, WRAP, RESERVED)),
                             rng.choice((0, 1, 3, 7, 15, (1 << self.LEN) - 1)),
                             note="random")

    async def run_all(self):
        await self.test_fixed_never_moves()
        await self.test_incr_steps_by_size()
        await self.test_incr_crosses_4k()
        await self.test_wrap_containers()
        await self.test_wrap_returns_to_base()
        await self.test_reserved_burst_behaves_as_incr()
        await self.test_random()

        assert self.errors == 0, \
            f"{self.errors} mismatch(es) against the AXI addressing model"
        self.log.info(f"@ {cocotb.utils.get_sim_time('ns')}ns: "
                      f"axi_gen_addr: all vectors match the model")
