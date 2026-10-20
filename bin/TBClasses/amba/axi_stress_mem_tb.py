# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: axi_stress_mem_tb
# Purpose: Testbench for tb_axi_stress_mem: axi4_master_stress on the
#          framework's AXI4 slave BFM with a memory model -- the master's
#          mem-window contract against a memory that keeps what it is given.
# Subsystem: framework
"""AxiStressMemTB -- the stress master's mem window on a real memory.

The memory model is the framework's MemoryModel behind create_axi4_slave_rd /
create_axi4_slave_wr. What a mem window must hold after a fill is computed
here from axi_stress_model (mem_byte), not read back from the RTL, so a
checker that agreed with a wrong writer would still fail on the image.

The slave BFM steps each beat by its size from the start address, which is
AXI only for an aligned INCR burst, so the window allows aligned INCR alone.
FIXED, WRAP and unaligned starts against a real memory are covered on the
board (MIG, the BRAM controller).
"""
from __future__ import annotations

import os
import random
from typing import Dict, List

from cocotb.triggers import RisingEdge, Timer

from TBClasses.shared.tbbase import TBBase
from TBClasses.amba import axi_stress_model as M
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.axi4.axi4_factories import (
    create_axi4_slave_rd, create_axi4_slave_wr)


class AxiStressMemTB(TBBase):
    MEM_BASE = 0x1000_0000

    def __init__(self, dut):
        super().__init__(dut)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.DW = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '64'))
        self.IW = self.convert_to_int(os.environ.get('TEST_ID_WIDTH', '4'))
        self.NWIN = self.convert_to_int(os.environ.get('TEST_NWIN', '2'))
        self.MEM_LG2 = self.convert_to_int(os.environ.get('TEST_MEM_LG2', '14'))
        self.NB = self.DW // 8
        self.BUS_LG2 = self.NB.bit_length() - 1
        random.seed(self.SEED)
        self.hash_seed = 0x1234_5678
        self.tag = 0x6D
        self.mem = MemoryModel(num_lines=(1 << self.MEM_LG2) // self.NB,
                               bytes_per_line=self.NB, log=self.log)
        kw = dict(dut=dut, clock=dut.aclk, prefix='m_axi', log=self.log,
                  id_width=self.IW, addr_width=32, data_width=self.DW, user_width=1,
                  memory_model=self.mem, base_addr=self.MEM_BASE)
        self.slv_rd = create_axi4_slave_rd(**kw)
        self.slv_wr = create_axi4_slave_wr(**kw)

    # ---- three mandatory TB methods (GLOBAL_REQUIREMENTS 2.2) --------------

    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', 10, 'ns')
        d = self.dut
        for s in ('go', 'stop', 'cfg_mrd', 'cfg_mwr', 'cfg_win_flat'):
            getattr(d, s).value = 0
        d.cfg_hash_seed.value = self.hash_seed
        await self.assert_reset()
        await self.wait_clocks('aclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 5)
        for port, fields in (('o_w_win', M.WIN_FIELDS), ('o_w_mcfg', M.MCFG_FIELDS),
                             ('o_w_msts', M.MSTS_FIELDS)):
            rtl = int(getattr(d, port).value)
            assert rtl == M.width(fields), \
                f'{port}: RTL struct is {rtl} bits, Python layout {M.width(fields)}'

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    # ---- configuration -----------------------------------------------------

    def window(self) -> M.Window:
        return M.Window(self.MEM_BASE, self.MEM_LG2, self.tag, len_mask=0x3F,
                        size_min=0, size_max=7, burst_mask=0b010, unaligned=0,
                        strb_rand=1, mem=1)

    def direction(self, n: int, *, fill: int = 0, enable: int = 1) -> Dict[str, int]:
        return dict(enable=enable, txn_count=n, seed=random.randint(1, M.M32),
                    id_base=0, id_mask=(1 << self.IW) - 1, timeout_lg2=16,
                    fill=fill, mem_lg2=self.MEM_LG2)

    def configure(self, rd: Dict[str, int], wr: Dict[str, int]):
        d = self.dut
        d.cfg_win_flat.value = M.pack_windows([self.window().fields()], self.NWIN)
        d.cfg_mrd.value = M.pack(M.MCFG_FIELDS, rd)
        d.cfg_mwr.value = M.pack(M.MCFG_FIELDS, wr)

    def fill_count(self) -> int:
        return M.fill_bursts(self.MEM_LG2, self.BUS_LG2)

    async def run(self, rd: Dict[str, int], wr: Dict[str, int], budget_cycles: int = 400_000):
        """One GO; wait for every enabled direction to finish."""
        self.configure(rd, wr)
        await RisingEdge(self.dut.aclk)
        runs0 = {k: v['runs'] for k, v in self.status().items()}
        self.dut.go.value = 1
        await RisingEdge(self.dut.aclk)
        await Timer(100, 'ps')
        self.dut.go.value = 0
        # On the GO edge itself DONE is still sampled from the idle state
        # (with RUNS already stepped), so poll from a few cycles later.
        live = [k for k, en in (('rd', rd['enable']), ('wr', wr['enable'])) if en]
        await self.wait_clocks('aclk', 4)
        for _ in range(budget_cycles):
            await RisingEdge(self.dut.aclk)
            st = self.status()
            if all(st[k]['runs'] != runs0[k] and st[k]['done'] for k in live):
                return st
        raise AssertionError(f'run did not finish in {budget_cycles} cycles: {self.status()}')

    def status(self) -> Dict[str, Dict[str, int]]:
        d = self.dut
        return {'rd': M.unpack(M.MSTS_FIELDS, int(d.sts_mrd.value)),
                'wr': M.unpack(M.MSTS_FIELDS, int(d.sts_mwr.value))}

    # ---- checks ------------------------------------------------------------

    def image_errors(self, limit: int = 8) -> List[str]:
        """Every byte of the memory model against what a filled mem window holds."""
        raw = self.mem.read(0, 1 << self.MEM_LG2)
        bad = []
        for off, got in enumerate(raw):
            exp = M.mem_byte(self.MEM_BASE + off, self.hash_seed, self.tag, self.MEM_LG2)
            if got != exp:
                bad.append(f'+{off:#07x}: {got:#04x}, expected {exp:#04x}')
                if len(bad) >= limit:
                    break
        return bad

    def corrupt(self) -> int:
        """Flip one byte of the memory model; returns its fabric address."""
        off = random.randrange(1 << self.MEM_LG2)
        b = self.mem.read(off, 1)
        self.mem.write(off, bytearray([b[0] ^ 0x5A]))
        return self.MEM_BASE + off

    @staticmethod
    def describe(st: Dict[str, int]) -> str:
        return (f"issued {st['issued']} completed {st['completed']} beats {st['beats']} "
                f"errors {M.err_list(st['err_mask'])} first "
                f"{M.ERR_NAMES.get(st['fe_kind'], '?') if st['fe_valid'] else '-'} "
                f"@{st['fe_addr']:#010x} exp {st['fe_exp']:#010x} act {st['fe_act']:#010x}")
