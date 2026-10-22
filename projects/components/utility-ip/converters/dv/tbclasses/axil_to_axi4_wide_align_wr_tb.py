# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: axil_to_axi4_wide_align_wr_tb
# Purpose: Testbench class for axil_to_axi4_wide_align_wr (narrow AXIL-style
#          single-beat writes placed on the lanes of a wide AXI4 slave)

"""
Testbench for axil_to_axi4_wide_align_wr.

- lane_alignment: every 4-byte offset inside a wide row lands on its own
  lanes of the wide slave, and nothing else in the row changes.
- b_backpressure: several writes in flight while the master holds BREADY low
  for a long time after each BVALID. The converter keeps ONE B register; a
  second slave B must wait for it instead of overwriting it (bridge BUG-025:
  the overwritten response was lost and the master's last write timed out).
"""

import os
import sys

import cocotb
from cocotb.triggers import ClockCycles

from TBClasses.shared.utilities import get_repo_root
from TBClasses.shared.tbbase import TBBase

repo_root = get_repo_root()
sys.path.insert(0, repo_root)
from CocoTBFramework.components.axi4.axi4_interfaces import AXI4MasterWrite, AXI4SlaveWrite
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.shared.memory_model import MemoryModel


class AxilToAxi4WideAlignWrTB(TBBase):

    MEM_LINES = 1024

    def __init__(self, dut):
        super().__init__(dut)
        self.clk = dut.aclk
        self.clk_name = 'aclk'
        self.rst_n = dut.aresetn

        self.s_width = self.convert_to_int(os.environ.get('S_AXI_DATA_WIDTH', '32'))
        self.m_width = self.convert_to_int(os.environ.get('M_AXI_DATA_WIDTH', '64'))
        self.id_width = self.convert_to_int(os.environ.get('AXI_ID_WIDTH', '2'))
        self.s_bytes = self.s_width // 8
        self.m_bytes = self.m_width // 8

        self.memory = MemoryModel(num_lines=self.MEM_LINES, bytes_per_line=self.m_bytes,
                                  log=self.log)
        self.master = AXI4MasterWrite(
            dut=dut, clock=self.clk, prefix="s_axi_", log=self.log,
            data_width=self.s_width, id_width=self.id_width, addr_width=32,
            multi_sig=True, pipelined=True, timeout_cycles=2000)
        self.slave = AXI4SlaveWrite(
            dut=dut, clock=self.clk, prefix="m_axi_", log=self.log,
            data_width=self.m_width, id_width=self.id_width, addr_width=32,
            multi_sig=True, memory_model=self.memory, response_delay=1)

    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock(self.clk_name, freq=period_ns, units='ns')
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)

    async def assert_reset(self):
        self.rst_n.value = 0

    async def deassert_reset(self):
        self.rst_n.value = 1

    def _mem_word(self, addr):
        return int.from_bytes(bytes(self.memory.read(addr, self.s_bytes)), 'little')

    async def _write_all(self, plan):
        """Issue every (addr, data) at once; return the failures."""
        size = (self.s_bytes).bit_length() - 1
        results = {}

        async def _one(addr, data):
            try:
                r = await self.master.single_write(addr, data, size=size)
                results[addr] = r.get('success', False) if isinstance(r, dict) else r
            except Exception as e:  # noqa: BLE001 -- reported below
                results[addr] = f'{e}'

        tasks = [cocotb.start_soon(_one(a, d)) for a, d in plan]
        for t in tasks:
            await t
        return [f'0x{a:08X}: {results.get(a)!r}' for a, _ in plan if results.get(a) is not True]

    async def lane_alignment(self):
        base = 0x200
        plan = [(base + off, 0xA5000000 | off) for off in range(0, 4 * self.m_bytes, self.s_bytes)]
        fails = await self._write_all(plan)
        bad = [f'0x{a:08X} holds 0x{self._mem_word(a):08X}, want 0x{d:08X}'
               for a, d in plan if self._mem_word(a) != d]
        for msg in fails + bad:
            self.log.error(f'lane_alignment: {msg}')
        return not fails and not bad

    async def b_backpressure(self, writes=6, hold=30):
        # BREADY rises `hold` cycles after each BVALID, far longer than one
        # write takes through the converter, so the slave's next B arrives
        # while the previous one is still held.
        self.master.b_channel.set_randomizer(
            FlexRandomizer({'ready_delay': ([(hold, hold)], [1])}))
        base = 0x400
        plan = [(base + self.s_bytes * i, 0xB0000000 | i) for i in range(writes)]
        fails = await self._write_all(plan)
        await ClockCycles(self.clk, 5)
        bad = [f'0x{a:08X} holds 0x{self._mem_word(a):08X}, want 0x{d:08X}'
               for a, d in plan if self._mem_word(a) != d]
        for msg in fails + bad:
            self.log.error(f'b_backpressure: {msg}')
        return not fails and not bad
