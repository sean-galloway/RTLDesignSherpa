"""
bch_axi4_read_engine / bch_axi4_write_engine testbench

The fixture is one real sdpram memory with the write engine on its write
channels and the read engine on its read channels. A pattern is pushed into the
write engine's stream, written to the memory as AXI4 bursts, read back out
through the read engine, and compared.

Author: RTL Design Sherpa
Created: 2026-10-03
"""

import os
import random

import cocotb
from cocotb.triggers import RisingEdge

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.shared.flex_config_gen import quick_config


class BCHAxi4EnginesTB(TBBase):
    """Drives the write engine's stream in and the read engine's stream out."""

    BEATS = {'gate': 63, 'func': 252, 'full': 1008}
    LENS = {'gate': [16], 'func': [1, 16, 64], 'full': [1, 7, 16, 64, 255]}
    PROFILES = {'gate': ['backtoback'],
                'func': ['backtoback', 'constrained'],
                'full': ['backtoback', 'constrained', 'bursty', 'slow']}

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.dw = self.convert_to_int(os.environ.get('DATA_WIDTH', 32))
        self.level = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.checks = 0
        self.mismatches = 0
        self._init_bfms()

    def _init_bfms(self):
        fc_in = FieldConfig()
        fc_in.add_field(FieldDefinition(name='data', bits=self.dw, default=0))
        fc_in.add_field(FieldDefinition(name='last', bits=1, default=0))
        self.master = GAXIMaster(dut=self.dut, title="WR_IN", prefix="in_", clock=self.dut.aclk,
                                 field_config=fc_in, pkt_prefix="", multi_sig=True, log=self.log)

        fc_out = FieldConfig()
        fc_out.add_field(FieldDefinition(name='data', bits=self.dw, default=0))
        fc_out.add_field(FieldDefinition(name='last', bits=1, default=0))
        self.slave = GAXISlave(dut=self.dut, title="RD_OUT", prefix="out_", clock=self.dut.aclk,
                               field_config=fc_out, pkt_prefix="", multi_sig=True, log=self.log)

    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock('aclk', period_ns, 'ns')
        self.dut.wr_start.value = 0
        self.dut.rd_start.value = 0
        self.dut.wr_addr.value = 0
        self.dut.rd_addr.value = 0
        self.dut.wr_beats.value = 0
        self.dut.rd_beats.value = 0
        self.dut.wr_burst_len.value = 16
        self.dut.rd_burst_len.value = 16
        self.dut.rd_beats_per_block.value = 1
        await self.assert_reset()
        await self.wait_clocks('aclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 5)

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    def set_profile(self, name):
        cfg = quick_config(profiles=[name], fields=['valid_delay', 'ready_delay']).build()
        self.master.set_randomizer(cfg[name])
        self.slave.set_randomizer(cfg[name])

    def _fail(self, msg):
        self.mismatches += 1
        self.log.error(msg)

    async def _pulse(self, sig):
        sig.value = 1
        await RisingEdge(self.dut.aclk)
        sig.value = 0

    async def _await_done(self, sig, label, limit):
        for _ in range(limit):
            if int(sig.value):
                return True
            await RisingEdge(self.dut.aclk)
        self._fail(f"{label}: cfg_done never asserted within {limit} cycles")
        return False

    async def run_loopback(self, beats, burst_len, per_block, profile='backtoback'):
        """Write `beats` words, read them back, compare."""
        self.checks += 1
        self.set_profile(profile)
        rnd = random.Random(0x5150 + beats * 131 + burst_len)
        mask = (1 << self.dw) - 1
        words = [rnd.randrange(1 << self.dw) & mask for _ in range(beats)]

        self.dut.wr_addr.value = 0
        self.dut.wr_beats.value = beats
        self.dut.wr_burst_len.value = burst_len
        await self._pulse(self.dut.wr_start)
        for i, w in enumerate(words):
            pkt = self.master.create_packet(data=w, last=int(i == beats - 1))
            await self.master.send(pkt)
        if not await self._await_done(self.dut.wr_done, f"write beats={beats} len={burst_len}",
                                      limit=60 * beats + 4000):
            return
        if int(self.dut.wr_resp_err.value):
            self._fail(f"write beats={beats} len={burst_len}: resp_err set")

        self.dut.rd_addr.value = 0
        self.dut.rd_beats.value = beats
        self.dut.rd_burst_len.value = burst_len
        self.dut.rd_beats_per_block.value = per_block
        await self._pulse(self.dut.rd_start)

        got, lasts, waited = [], [], 0
        limit = 60 * beats + 4000
        while len(got) < beats and waited < limit:
            if self.slave._recvQ:
                p = self.slave._recvQ.popleft()
                got.append(int(p.data) & mask)
                if int(p.last):
                    lasts.append(len(got))
            else:
                await RisingEdge(self.dut.aclk)
                waited += 1
        if not await self._await_done(self.dut.rd_done, f"read beats={beats} len={burst_len}",
                                      limit=4000):
            return
        if int(self.dut.rd_resp_err.value):
            self._fail(f"read beats={beats} len={burst_len}: resp_err set")

        label = f"beats={beats} len={burst_len} block={per_block} {profile}"
        if len(got) != beats:
            self._fail(f"{label}: read back {len(got)} of {beats} beats")
            return
        if got != words:
            first = next(i for i, (a, b) in enumerate(zip(got, words)) if a != b)
            self._fail(f"{label}: word {first} came back 0x{got[first]:08X}, wrote "
                       f"0x{words[first]:08X}")
        want_lasts = list(range(per_block, beats + 1, per_block))
        if lasts != want_lasts:
            self._fail(f"{label}: out_last at beats {lasts[:6]}, expected {want_lasts[:6]} "
                       f"-- a block boundary is not a burst boundary")

    async def run_bursts(self):
        beats = self.BEATS[self.level]
        for ln in self.LENS[self.level]:
            await self.run_loopback(beats, ln, per_block=beats)
        return self.mismatches == 0

    async def run_blocks(self):
        """A block length that deliberately disagrees with every burst boundary."""
        beats = self.BEATS[self.level]
        per_block = 63 if beats % 63 == 0 else beats
        for ln in self.LENS[self.level]:
            await self.run_loopback(beats, ln, per_block=per_block)
        return self.mismatches == 0

    async def run_backpressure(self):
        beats = self.BEATS[self.level]
        for profile in self.PROFILES[self.level]:
            if profile == 'backtoback':
                continue
            await self.run_loopback(beats, 16, per_block=beats, profile=profile)
        return self.mismatches == 0

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches,
                'level': self.level, 'data_width': self.dw}
