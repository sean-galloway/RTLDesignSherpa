# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: SchedulerByteTB
# Purpose: the byte-granular scheduler (rtl/fub/scheduler.sv, rapids TASK-019)
#
# Extends SchedulerTB, which drives the beat-granular scheduler_beats, with
# what the byte version adds:
#   - descriptor length is in BYTES: create_descriptor() scales a beat count
#     to bytes so the inherited beat-oriented tests run unchanged, and takes
#     length_bytes for byte-exact descriptors;
#   - src/dst addresses may carry a byte offset within the first beat;
#   - the packet-record ports (sched_*_pkt_valid/ready/bytes/offset) are
#     driven and recorded;
#   - a deterministic engine model (self.chop beats per completion) so the
#     address sequence the scheduler presents can be checked exactly.
#
# Subsystem: rapids

from typing import List, Tuple

import cocotb
from cocotb.triggers import RisingEdge

from projects.components.dma_ip.rapids.dv.tbclasses.scheduler_tb import SchedulerTB, ChannelState


class SchedulerByteTB(SchedulerTB):

    def __init__(self, dut):
        super().__init__(dut)
        self.DW = int(dut.DATA_WIDTH.value)
        self.bpb = self.DW // 8                       # bytes per beat
        self.rd_pkts: List[Tuple[int, int]] = []      # (bytes, offset) records seen on sched_rd_pkt_*
        self.wr_pkts: List[Tuple[int, int]] = []
        self.chop = None                              # beats per engine completion (None: inherited random model)
        self.rd_addr_seq: List[Tuple[int, int]] = []  # (addr presented, beats presented) per completion
        self.wr_addr_seq: List[Tuple[int, int]] = []
        self.log.info(f"SchedulerByteTB: DATA_WIDTH={self.DW}, {self.bpb} bytes per beat")

    # ------------------------------------------------------------------
    # configuration: the packet-record consumers are ready unless a test says otherwise
    # ------------------------------------------------------------------
    async def configure_scheduler(self):
        self.dut.sched_rd_pkt_ready.value = 1
        self.dut.sched_wr_pkt_ready.value = 1
        await super().configure_scheduler()

    async def initialize_test(self):
        await super().initialize_test()
        cocotb.start_soon(self.monitor_pkt_records())

    async def monitor_pkt_records(self):
        """Record every packet-record pulse. The pulse is combinational and one
        cycle wide, and a test may raise pkt_ready between edges, so sample
        mid-cycle (falling edge): that sees what the RTL consumer latches at
        the next rising edge, where a post-edge sample already sees it gone."""
        from cocotb.triggers import FallingEdge
        while True:
            await FallingEdge(self.clk)
            if int(self.dut.sched_rd_pkt_valid.value):
                self.rd_pkts.append((int(self.dut.sched_rd_pkt_bytes.value),
                                     int(self.dut.sched_rd_pkt_offset.value)))
            if int(self.dut.sched_wr_pkt_valid.value):
                self.wr_pkts.append((int(self.dut.sched_wr_pkt_bytes.value),
                                     int(self.dut.sched_wr_pkt_offset.value)))

    # ------------------------------------------------------------------
    # descriptors: bytes on the wire
    # ------------------------------------------------------------------
    def create_descriptor(self, src_addr: int = 0x1000, dst_addr: int = 0x2000,
                          length: int = 16, next_ptr: int = 0,
                          gen_irq: bool = False, last: bool = True,
                          channel_id: int = 0, priority: int = 0,
                          length_bytes: int = None) -> int:
        """length is a BEAT count (the inherited tests' unit) and is scaled to
        bytes; length_bytes, when given, is the exact byte length."""
        if length_bytes is None:
            length_bytes = length * self.bpb
        return super().create_descriptor(src_addr=src_addr, dst_addr=dst_addr, length=length_bytes,
                                         next_ptr=next_ptr, gen_irq=gen_irq, last=last,
                                         channel_id=channel_id, priority=priority)

    @staticmethod
    def beats_for(offset: int, nbytes: int, bpb: int) -> int:
        return 0 if nbytes == 0 else (offset + nbytes + bpb - 1) // bpb

    # ------------------------------------------------------------------
    # deterministic engine models (active when self.chop is set)
    # ------------------------------------------------------------------
    async def simulate_read_engine(self):
        if self.chop is None:
            await super().simulate_read_engine()
            return
        while True:
            await self.wait_clocks(self.clk_name, 1)
            if int(self.dut.sched_rd_valid.value) == 1:
                addr = int(self.dut.sched_rd_addr.value)
                beats = int(self.dut.sched_rd_beats.value)
                self.beat_requests_seen += 1
                if beats == 0:
                    self.zero_beat_requests += 1
                    continue
                self.rd_addr_seq.append((addr, beats))
                n = min(beats, self.chop)
                await self.wait_clocks(self.clk_name, 2)
                self.dut.sched_rd_done_strobe.value = 1
                self.dut.sched_rd_beats_done.value = n
                await self.wait_clocks(self.clk_name, 1)
                self.dut.sched_rd_done_strobe.value = 0
                self.total_read_beats += n

    async def simulate_write_engine(self):
        if self.chop is None:
            await super().simulate_write_engine()
            return
        while True:
            await self.wait_clocks(self.clk_name, 1)
            if int(self.dut.sched_wr_valid.value) == 1:
                addr = int(self.dut.sched_wr_addr.value)
                beats = int(self.dut.sched_wr_beats.value)
                self.beat_requests_seen += 1
                if beats == 0:
                    self.zero_beat_requests += 1
                    continue
                self.wr_addr_seq.append((addr, beats))
                n = min(beats, self.chop)
                await self.wait_clocks(self.clk_name, 2)
                self.dut.sched_wr_done_strobe.value = 1
                self.dut.sched_wr_beats_done.value = n
                self.dut.sched_wr_commit_strobe.value = 1
                self.dut.sched_wr_commit_beats.value = n
                await self.wait_clocks(self.clk_name, 1)
                self.dut.sched_wr_done_strobe.value = 0
                self.dut.sched_wr_commit_strobe.value = 0
                self.total_write_beats += n

    @classmethod
    def byte_expected_seq(cls, addr: int, nbytes: int, bpb: int, chop: int):
        """(address presented, beats remaining) per completion: the byte address
        first, then beat-aligned addresses; remaining counts down by chop."""
        total = cls.beats_for(addr % bpb, nbytes, bpb)
        seq, a, left = [], addr, total
        while left > 0:
            seq.append((a, left))
            n = min(left, chop)
            a = (a - a % bpb) + n * bpb
            left -= n
        return seq

    # ------------------------------------------------------------------
    # tests
    # ------------------------------------------------------------------
    async def test_desc_skid(self):
        """rapids TASK-028: the scheduler's two-deep descriptor skid buffer.

        1. Behind a running descriptor the skid takes exactly two more and
           then holds descriptor_ready low; all four then run in order.
        2. A one-cycle channel reset with the skid full runs neither entry:
           the reset drains one, and the reset epoch drops the other at the
           head. Only a descriptor sent after the reset runs."""
        self.log.info("=== Descriptor skid buffer: depth and channel reset ===")
        self.chop = 8                       # deterministic engine models record rd_addr_seq
        hs = {'n': 0}
        rd_seen = []   # read addresses the scheduler presents, straight off the port

        async def watch():
            while True:
                await RisingEdge(self.clk)
                if int(self.dut.descriptor_valid.value) and int(self.dut.descriptor_ready.value):
                    hs['n'] += 1
                if int(self.dut.sched_rd_valid.value):
                    a = int(self.dut.sched_rd_addr.value)
                    if not rd_seen or rd_seen[-1] != a:
                        rd_seen.append(a)

        async def send_all(descs):
            for d in descs:
                await self.send_descriptor(d)

        def desc(src, beats):
            return self.create_descriptor(src_addr=src, dst_addr=src + 0x8000000,
                                          length=beats, last=True)

        def starts():
            return [a for a, _ in self.rd_addr_seq]

        async def until(cond, cycles):
            for _ in range(cycles):
                if cond():
                    return True
                await self.wait_clocks(self.clk_name, 1)
            return cond()

        w = cocotb.start_soon(watch())
        ok = True

        # 1. depth: one running, two in the skid, one held at the port
        self.rd_addr_seq = []
        srcs = [0x100000, 0x200000, 0x300000, 0x400000]
        send = cocotb.start_soon(send_all([desc(s, 1024 if i == 0 else 4)
                                           for i, s in enumerate(srcs)]))
        await until(lambda: hs['n'] >= 3, 600)
        await self.wait_clocks(self.clk_name, 20)
        d0_running = bool(starts()) and all(a < srcs[1] for a in starts())
        held = hs['n'] == 3 and int(self.dut.descriptor_ready.value) == 0   # skid full
        if not (d0_running and held):
            self.log.error(f"  depth: taken={hs['n']} (exp 3 behind the running one) "
                           f"ready={int(self.dut.descriptor_ready.value)} d0_running={d0_running}")
            ok = False
        idle = await self.wait_for_idle(timeout_cycles=20000)
        first = [next((a for a in starts() if s <= a < s + 0x100000), None) for s in srcs]
        order = [starts().index(a) for a in first if a is not None]
        if not (idle and hs['n'] == 4 and None not in first and order == sorted(order)):
            self.log.error(f"  depth: idle={idle} taken={hs['n']} first={first}")
            ok = False
        send.kill()

        # 2. a one-cycle reset with the skid full runs neither skid entry
        hs['n'] = 0
        self.rd_addr_seq = []
        send = cocotb.start_soon(send_all([desc(0x500000, 1024), desc(0x600000, 4),
                                           desc(0x700000, 4)]))
        if not await until(lambda: hs['n'] >= 3, 600):
            self.log.error(f"  reset: skid never filled (taken={hs['n']})")
            ok = False
        await self.wait_clocks(self.clk_name, 2)
        self.dut.cfg_channel_reset.value = 1
        await self.wait_clocks(self.clk_name, 1)
        self.dut.cfg_channel_reset.value = 0
        rd_seen.clear()                       # every read presented from here on is checked
        await self.wait_clocks(self.clk_name, 200)    # in-flight engine bursts finish
        await self.wait_for_idle(timeout_cycles=2000)
        send.kill()
        await self.send_descriptor(desc(0x800000, 4))
        idle = await self.wait_for_idle(timeout_cycles=2000)
        # The skid held 0x600000 and 0x700000; neither may run. (The aborted
        # 0x500000 descriptor's request can still show the cycle after the
        # reset, which is the scheduler's registered reset, not the skid.)
        stale = [a for a in rd_seen if 0x600000 <= a < 0x800000]
        if not (idle and 0x800000 in rd_seen and not stale):
            self.log.error(f"  reset: idle={idle} reads after reset={[hex(a) for a in rd_seen]}")
            ok = False
        w.kill()
        return ok

    async def test_byte_lengths(self) -> bool:
        """Byte lengths and byte offsets: the scheduler must present
        ceil((offset + bytes) / bpb) beats per direction, advance addresses on
        beat boundaries after the first burst, and emit one packet record per
        direction carrying the byte length and the offset."""
        self.chop = 8
        bpb = self.bpb
        cases = [  # (src offset, dst offset, bytes)
            (0, 0, bpb),
            (5 % bpb, 0, 1),
            (bpb - 1, 0, 2),
            (0, 17 % bpb, 100),
            (13 % bpb, 29 % bpb, 1000),
        ]
        ok = True
        for i, (so, do, nbytes) in enumerate(cases):
            src = 0x10000 + i * 0x4000 + so
            dst = 0x80000 + i * 0x4000 + do
            self.rd_addr_seq, self.wr_addr_seq = [], []
            self.rd_pkts, self.wr_pkts = [], []
            desc = self.create_descriptor(src_addr=src, dst_addr=dst, length_bytes=nbytes, last=True)
            if not await self.send_descriptor(desc):
                ok = False
                continue
            idle = await self.wait_for_idle(timeout_cycles=4000)
            exp_rd = self.byte_expected_seq(src, nbytes, bpb, self.chop)
            exp_wr = self.byte_expected_seq(dst, nbytes, bpb, self.chop)
            good = (idle and self.rd_addr_seq == exp_rd and self.wr_addr_seq == exp_wr
                    and self.rd_pkts == [(nbytes, so)] and self.wr_pkts == [(nbytes, do)])
            self.log.info(f"  case {i}: src=0x{src:x} dst=0x{dst:x} bytes={nbytes}: "
                          f"rd {len(self.rd_addr_seq)} reqs (exp {len(exp_rd)}), "
                          f"wr {len(self.wr_addr_seq)} reqs (exp {len(exp_wr)}), "
                          f"records rd={self.rd_pkts} wr={self.wr_pkts} -> {'PASS' if good else 'FAIL'}")
            if not good:
                self.log.error(f"    rd seq {self.rd_addr_seq} expected {exp_rd}")
                self.log.error(f"    wr seq {self.wr_addr_seq} expected {exp_wr}")
                ok = False
        if self.zero_beat_requests:
            self.log.error(f"{self.zero_beat_requests} zero-beat requests")
            ok = False
        return ok

    async def test_pkt_backpressure(self) -> bool:
        """With the sink's record queue full (sched_wr_pkt_ready low) a DATA
        descriptor must wait in CH_FETCH_DESC: no engine request, no record.
        Releasing ready lets exactly one record through and the transfer runs."""
        self.chop = 4
        self.dut.sched_wr_pkt_ready.value = 0
        desc = self.create_descriptor(src_addr=0x20000 + 3, dst_addr=0x90000 + 9, length_bytes=200, last=True)
        if not await self.send_descriptor(desc):
            return False
        await self.wait_clocks(self.clk_name, 60)
        state = int(self.dut.scheduler_state.value)
        held = (state == ChannelState.CH_FETCH_DESC.value and not self.rd_addr_seq and not self.wr_addr_seq
                and not self.rd_pkts and not self.wr_pkts)
        self.log.info(f"  held: state=0x{state:02x} requests rd={len(self.rd_addr_seq)} wr={len(self.wr_addr_seq)} "
                      f"records rd={self.rd_pkts} wr={self.wr_pkts} -> {'PASS' if held else 'FAIL'}")
        self.dut.sched_wr_pkt_ready.value = 1
        idle = await self.wait_for_idle(timeout_cycles=4000)
        released = idle and self.rd_pkts == [(200, 3 % self.bpb)] and self.wr_pkts == [(200, 9 % self.bpb)]
        self.log.info(f"  released: idle={idle} records rd={self.rd_pkts} wr={self.wr_pkts} -> "
                      f"{'PASS' if released else 'FAIL'}")
        # One descriptor is one DESC_START, however long it waits in
        # CH_FETCH_DESC for its record (rapids TASK-034 finding).
        from TBClasses.monbus import parse
        starts = sum(1 for pkt in self.monitor_packets_received
                     if parse(int(pkt)).event_code == 0x00 and
                     parse(int(pkt)).get_packet_type_name() != "ERROR")
        one_start = (starts == 1)
        self.log.info(f"  DESC_START packets: {starts} -> {'PASS' if one_start else 'FAIL'}")
        return held and released and one_start

    async def test_zero_length(self) -> bool:
        """A zero-byte descriptor at a byte offset completes without an engine
        request and without a packet record."""
        self.chop = 4
        desc = self.create_descriptor(src_addr=0x30000 + 7, dst_addr=0xA0000 + 11, length_bytes=0, last=True)
        if not await self.send_descriptor(desc):
            return False
        idle = await self.wait_for_idle(timeout_cycles=2000)
        good = idle and not self.rd_addr_seq and not self.wr_addr_seq and not self.rd_pkts and not self.wr_pkts
        self.log.info(f"  zero length: idle={idle} requests rd={len(self.rd_addr_seq)} wr={len(self.wr_addr_seq)} "
                      f"records rd={self.rd_pkts} wr={self.wr_pkts} -> {'PASS' if good else 'FAIL'}")
        return good
