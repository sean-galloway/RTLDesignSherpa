# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: wb4_master_slave_loop_tb
# Purpose: Testbench for the wb4_master <-> wb4_slave loop. Both blocks are
#          driven and observed ONLY through their FUB-side valid/ready queues
#          with the GAXI BFMs; the Wishbone wires between them are checked by
#          the protocol assertions inside the loop wrapper.
#
# Documentation: docs/markdown/rtl-amba/wb4/wb4_master.md
# Subsystem: amba
#
# Author: sean galloway
# Created: 2026-09-09
"""
Traffic model
-------------
The master's command queue is fed by a GAXI master BFM; its response queue is
drained by a GAXI slave BFM. On the far side, a GAXI slave BFM takes each
command off the wb4_slave's queue and a GAXI master BFM pushes the response
back. The response is computed here from a word-addressed memory model:

    write -> store dat under sel, respond ACK with dat=0
    read  -> respond ACK with the stored word
    adr in ERR_WINDOW -> respond ERR ; adr in RTY_WINDOW -> respond RTY

Every command the TB sends is recorded; the slave-side callback checks the
command arrived unchanged and in order, computes the response, queues it for
the responder, and records the expectation the master-side callback checks
against. So both directions, both blocks, in-order delivery, and every status
value are proven end to end, and the four queues run under four independent
FlexRandomizer timing profiles.
"""

import os
from collections import deque

from cocotb.triggers import RisingEdge

from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_master, create_gaxi_slave
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.wb4.wb4_factories import create_wb4_monitor
from CocoTBFramework.components.wb4.wb4_sequence import WB4Sequence
from TBClasses.shared.tbbase import TBBase
from TBClasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS

# wb4_pkg encoding. Stated once in the RTL package; mirrored here because
# cocotb cannot import an SV package.
WB4_RSP_ACK, WB4_RSP_ERR, WB4_RSP_RTY = 0, 1, 2
STATUS_NAME = {WB4_RSP_ACK: "ACK", WB4_RSP_ERR: "ERR", WB4_RSP_RTY: "RTY"}

# Address windows the responder answers with ERR / RTY. Word addresses.
ERR_WINDOW = (0x0000_E000, 0x0000_EFFF)
RTY_WINDOW = (0x0000_F000, 0x0000_FFFF)


class WB4MasterSlaveLoopTB(TBBase):
    """wb4_master <-> wb4_slave loop, driven through the FUB-side queues."""

    def __init__(self, dut):
        super().__init__(dut)
        self.clk = dut.clk
        self.clk_name = 'clk'
        self.rst_n = dut.aresetn
        self.AW = self.convert_to_int(os.environ.get('ADDR_WIDTH', '32'))
        self.DW = self.convert_to_int(os.environ.get('DATA_WIDTH', '32'))
        self.SW = self.DW // 8
        self.done = False

        self.mem = {}                   # word address -> data
        self.sent = deque()             # commands the TB issued, in order
        self.expected = deque()         # (status, dat) the master must return, in order
        self.pending_rsp = deque()      # responses waiting for the responder coroutine
        self.got = deque()              # (status, dat) seen on the master's rsp queue
        self.errors = []
        self.stats = {'sent': 0, 'slave_cmds': 0, 'responses': 0,
                      'ack': 0, 'err': 0, 'rty': 0}

        self.cmd_fc = self._cmd_field_config()
        self.rsp_fc = self._rsp_field_config()
        self._create_bfms()

    # ---- field configs (MSB-first order matches the RTL packing) -----------
    def _cmd_field_config(self):
        fc = FieldConfig()
        fc.add_field(FieldDefinition(name="we", bits=1, default=0, format="bin",
                                     display_width=1, description="write enable"))
        fc.add_field(FieldDefinition(name="adr", bits=self.AW, default=0, format="hex",
                                     display_width=(self.AW + 3) // 4, description="address"))
        fc.add_field(FieldDefinition(name="dat", bits=self.DW, default=0, format="hex",
                                     display_width=(self.DW + 3) // 4, description="write data"))
        fc.add_field(FieldDefinition(name="sel", bits=self.SW, default=(1 << self.SW) - 1,
                                     format="bin", display_width=self.SW, description="byte select"))
        return fc

    def _rsp_field_config(self):
        fc = FieldConfig()
        fc.add_field(FieldDefinition(name="status", bits=2, default=0, format="dec",
                                     display_width=1, description="ACK=0 ERR=1 RTY=2",
                                     encoding=STATUS_NAME))
        fc.add_field(FieldDefinition(name="dat", bits=self.DW, default=0, format="hex",
                                     display_width=(self.DW + 3) // 4, description="read data"))
        return fc

    def _create_bfms(self):
        fixed_m = FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fixed']['master'])
        fixed_s = FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fixed']['slave'])
        # Master FUB side: we are the FUB.
        self.m_cmd = create_gaxi_master(
            self.dut, 'M CMD', '', self.clk, field_config=self.cmd_fc,
            pkt_prefix='m_cmd', randomizer=fixed_m, memory_model=None,
            log=self.log, multi_sig=True)
        self.m_rsp = create_gaxi_slave(
            self.dut, 'M RSP', '', self.clk, field_config=self.rsp_fc,
            pkt_prefix='m_rsp', randomizer=fixed_s, memory_model=None,
            log=self.log, multi_sig=True)
        # Slave FUB side: we are the peripheral behind the slave.
        self.s_cmd = create_gaxi_slave(
            self.dut, 'S CMD', '', self.clk, field_config=self.cmd_fc,
            pkt_prefix='s_cmd', randomizer=FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fixed']['slave']),
            memory_model=None, log=self.log, multi_sig=True)
        self.s_rsp = create_gaxi_master(
            self.dut, 'S RSP', '', self.clk, field_config=self.rsp_fc,
            pkt_prefix='s_rsp', randomizer=FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fixed']['master']),
            memory_model=None, log=self.log, multi_sig=True)
        self.s_cmd.add_callback(self._on_slave_cmd)
        self.m_rsp.add_callback(self._on_master_rsp)
        # The framework's Wishbone monitor on the wires between the two blocks.
        # The wrapper's own checkers stay as the second opinion; the two must agree.
        self.mon = create_wb4_monitor(self.dut, 'WB Mon', 'wb', self.clk, addr_width=self.AW,
                                      data_width=self.DW, classic=os.environ.get('CLASSIC', '0') == '1',
                                      log=self.log)

    # ---- mandatory TB methods ---------------------------------------------
    async def setup_clocks_and_reset(self):
        await self.start_clock(self.clk_name, 10, 'ns')
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)
        import cocotb
        self._responder = cocotb.start_soon(self._respond())

    async def assert_reset(self):
        self.rst_n.value = 0
        self.dut.m_cmd_valid.value = 0
        self.dut.m_rsp_ready.value = 0
        self.dut.s_cmd_ready.value = 0
        self.dut.s_rsp_valid.value = 0

    async def deassert_reset(self):
        self.rst_n.value = 1

    # ---- timing profiles ----------------------------------------------------
    def set_profiles(self, m_cmd='fixed', m_rsp='fixed', s_cmd='fixed', s_rsp='fixed'):
        """One AXI_RANDOMIZER_CONFIGS profile name per queue."""
        self.m_cmd.set_randomizer(FlexRandomizer(AXI_RANDOMIZER_CONFIGS[m_cmd]['master']))
        self.m_rsp.set_randomizer(FlexRandomizer(AXI_RANDOMIZER_CONFIGS[m_rsp]['slave']))
        self.s_cmd.set_randomizer(FlexRandomizer(AXI_RANDOMIZER_CONFIGS[s_cmd]['slave']))
        self.s_rsp.set_randomizer(FlexRandomizer(AXI_RANDOMIZER_CONFIGS[s_rsp]['master']))
        self.log.info(f"profiles: m_cmd={m_cmd} m_rsp={m_rsp} s_cmd={s_cmd} s_rsp={s_rsp}")

    # ---- the peripheral model behind the slave ------------------------------
    @staticmethod
    def _status_for(adr):
        if ERR_WINDOW[0] <= adr <= ERR_WINDOW[1]:
            return WB4_RSP_ERR
        if RTY_WINDOW[0] <= adr <= RTY_WINDOW[1]:
            return WB4_RSP_RTY
        return WB4_RSP_ACK

    def _on_slave_cmd(self, pkt):
        we, adr, dat, sel = int(pkt.we), int(pkt.adr), int(pkt.dat), int(pkt.sel)
        self.stats['slave_cmds'] += 1
        if not self.sent:
            self.errors.append(f"slave received a command nothing sent: we={we} adr=0x{adr:X}")
            return
        exp = self.sent.popleft()
        if (we, adr, dat, sel) != exp:
            self.errors.append(f"command corrupted/reordered: got we={we} adr=0x{adr:X} "
                               f"dat=0x{dat:X} sel=0x{sel:X}, expected we={exp[0]} "
                               f"adr=0x{exp[1]:X} dat=0x{exp[2]:X} sel=0x{exp[3]:X}")
        status = self._status_for(adr)
        rdat = 0
        if status == WB4_RSP_ACK:
            if we:
                old = self.mem.get(adr, 0)
                new = old
                for b in range(self.SW):
                    if (sel >> b) & 1:
                        mask = 0xFF << (8 * b)
                        new = (new & ~mask) | (dat & mask)
                self.mem[adr] = new
            else:
                rdat = self.mem.get(adr, 0)
        self.expected.append((status, rdat))
        self.pending_rsp.append((status, rdat))

    async def _respond(self):
        while not self.done:
            if self.pending_rsp:
                status, rdat = self.pending_rsp.popleft()
                pkt = GAXIPacket(self.rsp_fc)
                pkt.status = status
                pkt.dat = rdat
                await self.s_rsp.send(pkt)
            else:
                await RisingEdge(self.clk)

    def _on_master_rsp(self, pkt):
        status, dat = int(pkt.status), int(pkt.dat)
        self.stats['responses'] += 1
        self.stats[STATUS_NAME[status].lower() if status in STATUS_NAME else 'err'] += 1
        if not self.expected:
            self.errors.append(f"master returned a response with nothing expected: "
                               f"status={status} dat=0x{dat:X}")
            return
        exp = self.expected.popleft()
        if (status, dat) != exp:
            self.errors.append(f"response mismatch: got status={status} dat=0x{dat:X}, "
                               f"expected status={exp[0]} dat=0x{exp[1]:X}")
        self.got.append((status, dat))

    # ---- traffic --------------------------------------------------------------
    def _sequence(self, rng, count, mix):
        """The traffic for one phase. The sequence axis owns WHAT transfers
        happen -- the read/write mix and the ERR/RTY windows the wrapper's
        slave decodes; this TB still owns who drives them and when. Seeded
        from the TB's generator so the run stays reproducible.

        Addresses are left unaligned (``align=False``): the loopback wrapper
        has no memory model, so nothing here cares about word boundaries and
        unaligned traffic is the wider stimulus.
        """
        seq = WB4Sequence("loop.traffic", addr_width=self.AW, data_width=self.DW,
                          seed=rng.getrandbits(32))
        seq.add_random_workload(
            count, addr_lo=0, addr_hi=0x1000, write_frac=0.5,
            align=False, random_sel=True,
            windows=[(ERR_WINDOW[0], ERR_WINDOW[1], mix / 2),
                     (RTY_WINDOW[0], RTY_WINDOW[1], mix / 2)])
        return seq

    async def run_traffic(self, count, rng, mix=0.2, timeout_clocks=20000):
        """Send `count` random commands, then wait for every response."""
        start = self.stats['responses']
        # send_burst: queue the phase, then drive at the profile's pace (a
        # per-packet send() drains the driver pipeline each time and throttles
        # the producer to one command per ~3 clocks regardless of profile).
        pkts = []
        for t in self._sequence(rng, count, mix):
            self.sent.append((t.we, t.adr, t.dat_w, t.sel))
            pkt = GAXIPacket(self.cmd_fc)
            pkt.we, pkt.adr, pkt.dat, pkt.sel = t.we, t.adr, t.dat_w, t.sel
            self.stats['sent'] += 1
            pkts.append(pkt)
        await self.m_cmd.send_burst(pkts)
        waited = 0
        while self.stats['responses'] - start < count:
            await RisingEdge(self.clk)
            waited += 1
            if waited > timeout_clocks:
                self.errors.append(f"timeout: {self.stats['responses'] - start}/{count} "
                                   f"responses after {timeout_clocks} clocks")
                return False
        return not self.errors

    def check_wires(self, expected_total):
        """The wrapper's protocol checker counters."""
        v = int(self.dut.violations.value)
        a = int(self.dut.accepted.value)
        t = int(self.dut.terminated.value)
        if v:
            self.errors.append(f"{v} Wishbone protocol violation(s) flagged by the wrapper")
        if a != expected_total or t != expected_total:
            self.errors.append(f"wire counts accepted={a} terminated={t}, expected {expected_total}")
        peak = int(self.dut.max_inflight.value)
        mv = self.mon.total_violations()
        if mv:
            self.errors.append(f"WB4Monitor flagged {mv} violation(s): {self.mon.violations}")
        if (self.mon.accepted, self.mon.terminated, self.mon.max_inflight) != (a, t, peak):
            self.errors.append(f"WB4Monitor ({self.mon.accepted}, {self.mon.terminated}, "
                               f"{self.mon.max_inflight}) disagrees with the wrapper ({a}, {t}, {peak})")
        self.log.info(f"wires: accepted={a} terminated={t} violations={v} max_inflight={peak} "
                      f"| monitor: accepted={self.mon.accepted} terminated={self.mon.terminated} "
                      f"max_inflight={self.mon.max_inflight} violations={mv}")
        return peak

    def report(self):
        s = self.stats
        self.log.info(f"sent={s['sent']} slave_cmds={s['slave_cmds']} responses={s['responses']} "
                      f"ack={s['ack']} err={s['err']} rty={s['rty']} errors={len(self.errors)}")
        for e in self.errors[:20]:
            self.log.error(e)
        return not self.errors
