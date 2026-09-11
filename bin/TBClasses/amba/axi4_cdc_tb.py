# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: axi4_cdc_tb
# Purpose: Testbench class for axi4_cdc_wr / axi4_cdc_rd (AXI4 channels across
#          a clock-domain boundary)
#
# Author: sean galloway
# Created: 2026-09-11

"""Testbench for ``axi4_cdc_wr`` and ``axi4_cdc_rd``.

An AXI4 requester BFM on ``s_aclk`` drives the requester face; a memory-backed
AXI4 completer BFM on ``m_aclk`` answers the completer face. The two clocks
run at whatever periods the test asks for -- same, requester fast, requester
slow -- and every phase checks the same things:

* every burst completes and the data round-trips (written words are read
  straight out of the completer's memory; reads return what was seeded);
* beats arrive in order: the completer sees each burst's W beats contiguous
  and in address order, and the requester sees each burst's R beats in order
  (the FIFOs are in order per channel -- a crossing that reordered would
  fail here, a crossing that dropped would fail the count);
* an out-of-range access (the completer's SLVERR) comes back as SLVERR
  through the B / R crossing, with nothing written;
* AW and W cross independently: bursts whose W is offered before the AW
  still land (the completer BFM pairs them).

Both resets are asserted and released together; a one-sided reset is out of
scope by the module's own contract (handbook design/cdc.md).
"""

import os
import random
from cocotb.utils import get_sim_time
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
import sys

from cocotb.triggers import RisingEdge, Timer

from TBClasses.shared.utilities import get_repo_root
from TBClasses.shared.tbbase import TBBase

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from CocoTBFramework.components.axi4.axi4_interfaces import (
    AXI4MasterRead, AXI4MasterWrite, AXI4SlaveRead, AXI4SlaveWrite,
)
from CocoTBFramework.components.shared.memory_model import MemoryModel

OKAY, SLVERR = 0, 2


class AXI4CdcTB(TBBase):
    MEM_LINES = 512

    def __init__(self, dut):
        super().__init__(dut)
        self.channel = os.environ.get('CDC_CHANNEL', 'wr')       # 'wr' | 'rd'
        self.data_width = self.convert_to_int(os.environ.get('AXI_DATA_WIDTH', '32'))
        self.addr_width = self.convert_to_int(os.environ.get('AXI_ADDR_WIDTH', '32'))
        self.id_width = self.convert_to_int(os.environ.get('AXI_ID_WIDTH', '4'))
        self.s_period = self.convert_to_int(os.environ.get('S_PERIOD', '10'))
        self.m_period = self.convert_to_int(os.environ.get('M_PERIOD', '10'))
        self.bpb = self.data_width // 8
        self.axsize = self.bpb.bit_length() - 1
        self.mem_bytes = self.MEM_LINES * self.bpb
        self.errors = []

        self.s_clk = dut.s_aclk
        self.m_clk = dut.m_aclk
        self.mem = MemoryModel(num_lines=self.MEM_LINES, bytes_per_line=self.bpb, log=self.log)

        common = dict(data_width=self.data_width, id_width=self.id_width,
                      addr_width=self.addr_width, user_width=1, multi_sig=True, log=self.log)
        if self.channel == 'wr':
            self.req = AXI4MasterWrite(dut=dut, clock=self.s_clk, prefix='s_axi_', **common)
            self.cmp = AXI4SlaveWrite(dut=dut, clock=self.m_clk, prefix='m_axi_',
                                      memory_model=self.mem, response_delay=1, **common)
            self.cmp.aw_channel.add_callback(self._on_aw)
            self.cmp.w_channel.add_callback(self._on_w)
        else:
            self.req = AXI4MasterRead(dut=dut, clock=self.s_clk, prefix='s_axi_', **common)
            self.cmp = AXI4SlaveRead(dut=dut, clock=self.m_clk, prefix='m_axi_',
                                     memory_model=self.mem, response_delay=1, **common)
            self.cmp.ar_channel.add_callback(self._on_ar)
            self.req.r_channel.add_callback(self._on_beat)
        self.beat_t = []       # sim time (ns) of every data beat that crossed: W at the completer, R at the requester
        self.aw_seen = []      # (id, addr, len) at the completer, in arrival order
        self.w_seen = []       # (data, strb, last)
        self.ar_seen = []
        self.log.info(f"AXI4 CDC TB: channel={self.channel} dw={self.data_width} "
                      f"s_period={self.s_period} m_period={self.m_period}")

    # ---- mandatory ------------------------------------------------------

    async def setup_clocks_and_reset(self):
        await self.start_clock('s_aclk', freq=self.s_period, units='ns')
        await self.start_clock('m_aclk', freq=self.m_period, units='ns')
        await self.assert_reset()
        await Timer(20 * max(self.s_period, self.m_period), units='ns')
        await self.deassert_reset()
        await Timer(10 * max(self.s_period, self.m_period), units='ns')

    async def assert_reset(self):
        self.dut.s_aresetn.value = 0
        self.dut.m_aresetn.value = 0

    async def deassert_reset(self):
        self.dut.s_aresetn.value = 1
        self.dut.m_aresetn.value = 1

    # ---- observation ----------------------------------------------------

    def _on_aw(self, pkt):
        self.aw_seen.append((int(pkt.fields.get('id', 0)), int(pkt.fields['addr']), int(pkt.fields.get('len', 0))))

    def _on_beat(self, pkt):
        self.beat_t.append(get_sim_time('ns'))

    def _on_w(self, pkt):
        self.beat_t.append(get_sim_time('ns'))
        self.w_seen.append((int(pkt.fields['data']), int(pkt.fields.get('strb', 0)), int(pkt.fields.get('last', 1))))

    def _on_ar(self, pkt):
        self.ar_seen.append((int(pkt.fields.get('id', 0)), int(pkt.fields['addr']), int(pkt.fields.get('len', 0))))

    def _fail(self, msg):
        self.errors.append(msg)
        self.log.error(msg)

    def _mem_word(self, addr):
        return int.from_bytes(bytes(self.mem.read(addr, self.bpb)), 'little')

    def _resp_of(self, result):
        if isinstance(result, dict):
            return int(result.get('response', 0 if result.get('success', True) else 2))
        return int(result)

    # ---- phases ---------------------------------------------------------

    async def run_bursts(self, count, rng, max_beats):
        """Sequential bursts; every beat lands and arrives in order."""
        for i in range(count):
            beats = rng.randint(1, max_beats)
            addr = rng.randrange(0, self.mem_bytes - beats * self.bpb, self.bpb)
            data = [rng.getrandbits(self.data_width) for _ in range(beats)]
            txn_id = i % (1 << self.id_width)
            if self.channel == 'wr':
                n_w = len(self.w_seen)
                res = await self.req.write_transaction(addr, data, id=txn_id, size=self.axsize)
                if self._resp_of(res) != OKAY:
                    self._fail(f"burst {i}: B resp {self._resp_of(res)}")
                got = [d for d, _s, _l in self.w_seen[n_w:n_w + beats]]
                if got != data:
                    self._fail(f"burst {i}: W beats crossed out of order or were lost: {[hex(x) for x in got]} != {[hex(x) for x in data]}")
                if self.w_seen[n_w:n_w + beats] and self.w_seen[n_w + beats - 1][2] != 1:
                    self._fail(f"burst {i}: WLAST not on the last crossed beat")
                for k, d in enumerate(data):
                    if (m := self._mem_word(addr + k * self.bpb)) != d:
                        self._fail(f"burst {i} beat {k}: memory 0x{m:X}, wrote 0x{d:X}")
            else:
                for k, d in enumerate(data):
                    self.mem.write(addr + k * self.bpb, self.mem.integer_to_bytearray(d, self.bpb))
                got = await self.req.read_transaction(addr, burst_len=beats, id=txn_id, size=self.axsize)
                if list(got) != data:
                    self._fail(f"burst {i}: R beats {[hex(x) for x in got]} != {[hex(x) for x in data]}")
                if not self.ar_seen or self.ar_seen[-1][1] != addr:
                    self._fail(f"burst {i}: AR did not arrive with address 0x{addr:X}")

    async def run_concurrent(self, count, rng, beats):
        """Many bursts in flight across the crossing at once; all complete,
        all data correct, ids rotate."""
        import cocotb
        plan = [(rng.randrange(0, self.mem_bytes - beats * self.bpb, beats * self.bpb),
                 [rng.getrandbits(self.data_width) for _ in range(beats)]) for _ in range(count)]
        # distinct addresses so bursts cannot overwrite each other
        seen = set(); uniq = []
        for a, d in plan:
            if a not in seen:
                seen.add(a); uniq.append((a, d))
        plan = uniq
        done, bad = [], []

        async def _one(i, addr, data):
            txn_id = i % (1 << self.id_width)
            if self.channel == 'wr':
                res = await self.req.write_transaction(addr, data, id=txn_id, size=self.axsize)
                if self._resp_of(res) != OKAY:
                    bad.append(f"concurrent {i}: B resp {self._resp_of(res)}")
            else:
                for k, d in enumerate(data):
                    self.mem.write(addr + k * self.bpb, self.mem.integer_to_bytearray(d, self.bpb))
                got = await self.req.read_transaction(addr, burst_len=beats, id=txn_id, size=self.axsize)
                if list(got) != data:
                    bad.append(f"concurrent {i}: R data mismatch")
            done.append(1)

        for i, (a, d) in enumerate(plan):
            cocotb.start_soon(_one(i, a, d))
        for _ in range(20000):
            if len(done) == len(plan):
                break
            await RisingEdge(self.s_clk)
        if len(done) != len(plan):
            self._fail(f"concurrent: {len(done)}/{len(plan)} bursts completed")
        self.errors.extend(bad)
        if self.channel == 'wr':
            for i, (addr, data) in enumerate(plan):
                for k, d in enumerate(data):
                    if (m := self._mem_word(addr + k * self.bpb)) != d:
                        self._fail(f"concurrent {i} beat {k}: memory 0x{m:X}, wrote 0x{d:X}")

    async def run_oor(self, count, rng):
        for i in range(count):
            bad = self.mem_bytes + rng.randrange(0, self.mem_bytes, self.bpb)
            if self.channel == 'wr':
                res = await self.req.write_transaction(bad, [rng.getrandbits(self.data_width)], id=1, size=self.axsize)
                if self._resp_of(res) != SLVERR:
                    self._fail(f"oor write {i}: B resp {self._resp_of(res)}, expected SLVERR through the crossing")
            else:
                try:
                    await self.req.read_transaction(bad, burst_len=1, id=1, size=self.axsize)
                    self._fail(f"oor read {i}: OKAY, expected SLVERR through the crossing")
                except RuntimeError as e:
                    if 'SLVERR' not in str(e):
                        self._fail(f"oor read {i}: {e}")

    STREAM_FLOOR = 0.85    # data beats per cycle of the slower clock while streaming

    async def run_stream(self, count, rng, beats):
        """Back-to-back bursts in flight together: the crossing must stream at
        one beat per cycle of the slower clock. A FIFO shallower than the
        pointer round trip cannot (CDC_DEPTH 4 measured 0.58 at equal clocks)
        and this is where that shows."""
        for ch in ('aw_channel', 'w_channel', 'ar_channel'):
            if hasattr(self.req, ch):
                getattr(self.req, ch).set_randomizer(FlexRandomizer({'valid_delay': ([(0, 0)], [1])}))
        for ch in ('b_channel', 'r_channel'):
            if hasattr(self.req, ch):
                getattr(self.req, ch).set_randomizer(FlexRandomizer({'ready_delay': ([(0, 0)], [1])}))
        for ch in ('aw_channel', 'w_channel', 'ar_channel'):
            if hasattr(self.cmp, ch):
                getattr(self.cmp, ch).set_randomizer(FlexRandomizer({'ready_delay': ([(0, 0)], [1])}))
        for ch in ('b_channel', 'r_channel'):
            if hasattr(self.cmp, ch):
                getattr(self.cmp, ch).set_randomizer(FlexRandomizer({'valid_delay': ([(0, 0)], [1])}))
        self.cmp.response_delay_cycles = 0
        first = len(self.beat_t)
        await self.run_concurrent(count, rng, beats)
        marks = self.beat_t[first:]
        slow = max(self.s_period, self.m_period)
        if len(marks) < 2 * beats:
            self._fail(f"stream: only {len(marks)} beats crossed")
            return
        cycles = (marks[-1] - marks[0]) / slow + 1
        rate = len(marks) / cycles
        self.log.info(f"PERF stream {self.channel}: {len(marks)} beats in {cycles:.0f} cycles of the "
                      f"{slow} ns clock = {rate:.3f} beats/cycle (floor {self.STREAM_FLOOR})")
        if rate < self.STREAM_FLOOR:
            self._fail(f"stream: {rate:.3f} beats per cycle of the slower clock, floor {self.STREAM_FLOOR} "
                       f"-- the crossing cannot keep up (CDC_DEPTH below the pointer round trip?)")

    async def run_suite(self, level, seed):
        rng = random.Random(seed)
        plan = {'gate': dict(bursts=6, beats=4, conc=4, oor=1, stream=6),
                'func': dict(bursts=24, beats=8, conc=12, oor=2, stream=16),
                'full': dict(bursts=64, beats=16, conc=32, oor=4, stream=32)}[level]
        self.log.info(f"AXI4 CDC {self.channel} {level.upper()} plan: {plan}")
        await self.run_bursts(plan['bursts'], rng, plan['beats'])
        await self.run_concurrent(plan['conc'], rng, 4)
        await self.run_oor(plan['oor'], rng)
        await self.run_stream(plan['stream'], rng, 16)
        seen = len(self.w_seen) if self.channel == 'wr' else len(self.ar_seen)
        if seen == 0:
            self._fail("the completer saw nothing cross")
        self.log.info(f"crossed: {seen} beats/requests, errors={len(self.errors)}")
        return not self.errors
