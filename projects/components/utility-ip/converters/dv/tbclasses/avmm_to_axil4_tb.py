# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Testbench for avmm_to_axil4 (Avalon-MM slave in, AXI4-Lite master out).

The AXI4-Lite side is answered by the framework's AXIL4 slave BFMs over one
shared memory model, so a write really lands where a later read finds it;
everything above MEM_BYTES answers SLVERR.

The Avalon side has no framework BFM yet. AvmmMaster below is the minimum a
pipelined Avalon-MM master does -- present a command, hold it while
waitrequest is high, collect readdata on readdatavalid -- and AvmmWatch checks
the wire rules the converter owns: readdatavalid / writeresponsevalid only
after an accepted command of that kind, never in the accept clock, never
twice. When an Avalon BFM lands in CocoTBFramework these two classes go.
"""
import os

import cocotb
from cocotb.triggers import RisingEdge, ReadOnly, NextTimeStep

from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.axil4.axil4_interfaces import AXIL4SlaveWrite, AXIL4SlaveRead
from TBClasses.shared.tbbase import TBBase

MEM_BYTES = 0x4000                       # everything above this answers SLVERR
ERR_BASE  = 0x8000
RESP_OKAY, RESP_SLVERR = 0b00, 0b10


class AvmmWatch:
    """Avalon-MM return-path rules, sampled every clock in ReadOnly."""

    def __init__(self, dut, clk, log):
        self.dut, self.clk, self.log = dut, clk, log
        self.pending_rd = 0               # accepted reads not yet returned
        self.pending_wr = 0
        self.violations = []
        self.reads_returned = 0
        self.writes_returned = 0

    async def run(self):
        d = self.dut
        while True:
            await RisingEdge(self.clk)
            await ReadOnly()
            if int(d.aresetn.value) == 0:
                continue
            rdv = int(d.s_avmm_readdatavalid.value)
            wrv = int(d.s_avmm_writeresponsevalid.value)
            # Returns are checked against acceptances from EARLIER clocks,
            # which is the "at least one clock later" rule.
            if rdv:
                if self.pending_rd == 0:
                    self.violations.append("readdatavalid with no accepted read")
                else:
                    self.pending_rd -= 1
                    self.reads_returned += 1
            if wrv:
                if self.pending_wr == 0:
                    self.violations.append("writeresponsevalid with no accepted write")
                else:
                    self.pending_wr -= 1
                    self.writes_returned += 1
            if rdv and wrv:
                self.violations.append("read and write returns in one clock")
            accepted = int(d.s_avmm_waitrequest.value) == 0
            if accepted and int(d.s_avmm_write.value):
                self.pending_wr += 1
            elif accepted and int(d.s_avmm_read.value):
                self.pending_rd += 1


class AvmmToAXIL4TB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.clk = dut.aclk
        self.clk_name = 'aclk'
        self.rst_n = dut.aresetn
        self.AW = self.convert_to_int(os.environ.get('ADDR_WIDTH', '32'))
        self.DW = self.convert_to_int(os.environ.get('DATA_WIDTH', '32'))
        self.SW = self.DW // 8
        self.wr_delay = self.convert_to_int(os.environ.get('WR_DELAY', '6'))
        self.rd_delay = self.convert_to_int(os.environ.get('RD_DELAY', '1'))

        self.mem = MemoryModel(num_lines=MEM_BYTES // self.SW, bytes_per_line=self.SW,
                               log=self.log)
        self.mirror = {}
        self.errors = []
        self.stats = {'wr': 0, 'rd': 0, 'okay': 0, 'slverr': 0}
        self.watch = AvmmWatch(dut, self.clk, self.log)
        self.axil_wr = AXIL4SlaveWrite(dut=dut, clock=self.clk, prefix='m_axil_', log=self.log,
                                       data_width=self.DW, addr_width=self.AW, multi_sig=True,
                                       memory_model=self.mem, response_delay=self.wr_delay)
        self.axil_rd = AXIL4SlaveRead(dut=dut, clock=self.clk, prefix='m_axil_', log=self.log,
                                      data_width=self.DW, addr_width=self.AW, multi_sig=True,
                                      memory_model=self.mem, response_delay=self.rd_delay)

    # ---- mandatory ------------------------------------------------------
    async def setup_clocks_and_reset(self):
        d = self.dut
        d.s_avmm_read.value = 0
        d.s_avmm_write.value = 0
        d.s_avmm_address.value = 0
        d.s_avmm_writedata.value = 0
        d.s_avmm_byteenable.value = 0
        await self.start_clock(self.clk_name, 10, 'ns')
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)
        cocotb.start_soon(self.watch.run())

    async def assert_reset(self):
        self.rst_n.value = 0

    async def deassert_reset(self):
        self.rst_n.value = 1

    # ---- the Avalon master ----------------------------------------------
    async def _transfer(self, we, adr, dat=0, be=0, timeout=2000):
        """Present one command and hold it until waitrequest drops; for a
        read, then wait for readdatavalid. Returns (response, readdata)."""
        d = self.dut
        d.s_avmm_address.value = adr
        d.s_avmm_write.value = int(we)
        d.s_avmm_read.value = int(not we)
        d.s_avmm_writedata.value = dat
        d.s_avmm_byteenable.value = be
        for _ in range(timeout):
            await RisingEdge(self.clk)
            await ReadOnly()
            if int(d.s_avmm_waitrequest.value) == 0:
                break
        else:
            raise TimeoutError(f"waitrequest held {timeout} clocks at 0x{adr:X}")
        await RisingEdge(self.clk)
        d.s_avmm_write.value = 0
        d.s_avmm_read.value = 0
        # The return is the clock after acceptance; we are now in it.
        await ReadOnly()
        flag = d.s_avmm_writeresponsevalid if we else d.s_avmm_readdatavalid
        if int(flag.value) != 1:
            self.errors.append(f"{'write' if we else 'read'} 0x{adr:X}: no return the clock "
                               f"after acceptance")
            await NextTimeStep()
            return None, None
        result = int(d.s_avmm_response.value), (None if we else int(d.s_avmm_readdata.value))
        # Leave the read-only phase so the next command can be driven at once:
        # back-to-back commands with no idle clock are part of the contract.
        await NextTimeStep()
        return result

    # ---- model ----------------------------------------------------------
    def _expected_word(self, adr):
        return sum(self.mirror.get(adr + i, 0) << (8 * i) for i in range(self.SW))

    async def run_traffic(self, count, rng, err_frac=0.1, max_gap=3):
        for _ in range(count):
            if rng.random() < err_frac:
                adr = ERR_BASE + rng.randrange(0, 0x1000 // self.SW) * self.SW
            else:
                adr = rng.randrange(0, MEM_BYTES // self.SW) * self.SW
            we = rng.random() < 0.5
            dat = rng.getrandbits(self.DW)
            be = rng.getrandbits(self.SW) or 1
            resp, rdata = await self._transfer(we, adr, dat, be)
            if resp is None:
                continue
            want = RESP_SLVERR if adr >= MEM_BYTES else RESP_OKAY
            self.stats['wr' if we else 'rd'] += 1
            self.stats['okay' if resp == RESP_OKAY else 'slverr'] += 1
            if resp != want:
                self.errors.append(f"{'wr' if we else 'rd'} 0x{adr:X}: response {resp:02b}, "
                                   f"want {want:02b}")
                continue
            if adr >= MEM_BYTES:
                continue
            if we:
                for i in range(self.SW):
                    if be >> i & 1:
                        self.mirror[adr + i] = (dat >> (8 * i)) & 0xFF
            elif rdata != self._expected_word(adr):
                self.errors.append(f"rd 0x{adr:X}: data 0x{rdata:X}, "
                                   f"want 0x{self._expected_word(adr):X}")
            for _ in range(rng.randrange(0, max_gap + 1)):
                await RisingEdge(self.clk)
        return not self.errors

    async def run_back_to_back(self, rng, pairs=8):
        """Write then read the same word with no idle clock between them: the
        converter must have cleared its sent flags in the accept clock or the
        read's AR is never issued (or a stale R is taken as its answer)."""
        for _ in range(pairs):
            adr = rng.randrange(0, MEM_BYTES // self.SW) * self.SW
            dat = rng.getrandbits(self.DW)
            full = (1 << self.SW) - 1
            resp, _ = await self._transfer(True, adr, dat, full)
            for i in range(self.SW):
                self.mirror[adr + i] = (dat >> (8 * i)) & 0xFF
            resp2, rdata = await self._transfer(False, adr)
            self.stats['wr'] += 1
            self.stats['rd'] += 1
            if resp != RESP_OKAY or resp2 != RESP_OKAY or rdata != dat:
                self.errors.append(f"back-to-back 0x{adr:X}: resp {resp}/{resp2} "
                                   f"data 0x{(rdata or 0):X} want 0x{dat:X}")
        return not self.errors

    async def wait_idle(self, limit=2000):
        for _ in range(limit):
            await RisingEdge(self.clk)
            if int(self.dut.busy.value) == 0:
                return True
        self.errors.append("busy never dropped")
        return False

    def report(self):
        w = self.watch
        if w.violations:
            self.errors.append(f"Avalon return-path violation(s): {w.violations[:5]}")
        if w.pending_rd or w.pending_wr:
            self.errors.append(f"accepted but never returned: rd={w.pending_rd} wr={w.pending_wr}")
        if w.reads_returned != self.stats['rd'] or w.writes_returned != self.stats['wr']:
            self.errors.append(f"watch saw rd={w.reads_returned} wr={w.writes_returned}, "
                               f"master completed {self.stats}")
        self.log.info(f"stats {self.stats} wr_delay={self.wr_delay} rd_delay={self.rd_delay} "
                      f"watch rd={w.reads_returned} wr={w.writes_returned} "
                      f"violations={len(w.violations)}")
        for e in self.errors[:20]:
            self.log.error(e)
        return not self.errors
