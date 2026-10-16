# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: cxs_master_tb
# Purpose: Testbench for cxs_master / cxs_master_cg: a GAXI master on the FUB
#          side, the framework CXSReceiver granting credits on the link, and
#          a CXSMonitor checking the wires
#
# Documentation: docs/markdown/rtl-amba/cxs/cxs_master.md
# Subsystem: amba
# Author: sean galloway
# Created: 2026-10-15
"""
The expectation is the packetizer's output: the TB packs random packets into
flits, offers those flits on fub_cxs_*, and requires the receiver BFM to see
the same flits, in order, field for field -- and to reassemble the same
packets. The monitor is a third party on m_cxs_*, so its credit model and
link checks judge the DUT, not the receiver BFM that is driving it.

Phases, each with its own claim:
  fast     credits come straight back: the link must stream
  starve   the receiver drains slowly, so credits run out: the DUT must stall
           with flits queued and never send without a credit
  gappy    sparse grants and a slow ACK
  idle     (link control) the DUT must take the link to STOP when idle and
           return every credit first, then reactivate for new work
  hint     (link control) CXSDEACTHINT alone takes the link down
  parity   (CXS_CHECK) a corrupted CXSCRDGNTCHK must set parity_error
"""

import cocotb
from cocotb.triggers import FallingEdge, RisingEdge

from CocoTBFramework.components.cxs import (STOP, create_cxs_monitor, create_cxs_receiver)
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_master
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from TBClasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS
from TBClasses.cxs.cxs_tb_common import RX_PROFILES, CXSTBBase


class CXSMasterTB(CXSTBBase):
    def __init__(self, dut, cg=False):
        super().__init__(dut, cg)
        cfg = self.cfg
        self.fub = create_gaxi_master(
            dut, 'FUB', '', self.clk, field_config=self.fub_fc, pkt_prefix='fub_cxs',
            randomizer=FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fixed']['master']),
            memory_model=None, log=self.log, multi_sig=True,
            # credit starvation is a test phase, not a hang: a FUB blocked for
            # thousands of cycles is expected (RDS-DV #93: a GAXI ready timeout
            # silently drops the beat rather than failing)
            timeout_cycles=200000)
        self.rx = create_cxs_receiver(dut, 'CXS RX', 'm_cxs_', self.clk, cfg, reset=self.rst_n,
                                      randomizer=FlexRandomizer(RX_PROFILES['fast']), log=self.log)
        self.mon = create_cxs_monitor(dut, 'CXS Mon', 'm_cxs_', self.clk, cfg, reset=self.rst_n,
                                      log=self.log)
        self.expected = []
        self.packets = []
        self.deactivations = 0

    def _pre_reset(self):
        super()._pre_reset()
        self.dut.cfg_link_enable.value = 1
        self.dut.cfg_link_hold.value = 0
        self.dut.cfg_idle_cycles.value = 0      # phases choose their own
        self.dut.fub_cxs_valid.value = 0

    async def setup_clocks_and_reset(self):
        await super().setup_clocks_and_reset()
        if self.cg:
            cocotb.start_soon(self.count_gating())
        if self.cfg.link_control:
            cocotb.start_soon(self.watch_deactivation())

    async def watch_deactivation(self):
        """The DUT's contract (IHI 0079D 6.1): ACTIVEREQ never falls while a
        packet is open on the link. The monitor's packet state is updated from
        flits up to the previous cycle, and no flit moves once ACTIVEREQ is low."""
        prev = 0
        while True:
            await FallingEdge(self.clk)
            req = int(self.dut.m_cxs_activereq.value)
            if prev and not req:
                self.deactivations += 1
                if self.mon.in_packet:
                    self.errors.append("ACTIVEREQ fell with a packet open")
            prev = req

    async def run_midpacket_idle(self, count):
        """FUB stalls 8-20 cycles between flits, longer than a 3-cycle idle
        timeout: the link must go down between packets, never inside one."""
        if not self.cfg.link_control or self.cfg.is_lite:
            return True
        before = self.deactivations
        self.dut.cfg_idle_cycles.value = 3
        ok = await self.run_phase('midpacket', count, 'fast', fub_profile='slow_producer')
        self.dut.cfg_idle_cycles.value = 0
        if self.deactivations == before:
            self.errors.append("midpacket: the link never went down, the phase proved nothing")
        return ok

    # ---- traffic --------------------------------------------------------
    async def run_phase(self, name, count, rx_profile='fast', buffer_depth=None, fub_profile='fixed'):
        cfg = self.cfg
        self.rx.set_randomizer(FlexRandomizer(RX_PROFILES[rx_profile]))
        self.rx.buffer_depth = buffer_depth or cfg.max_credit
        self.fub.set_randomizer(FlexRandomizer(AXI_RANDOMIZER_CONFIGS[fub_profile]['master']))
        packets = self.make_packets(count)
        flits = self.packetize(packets)
        start = self.rx.stats['flits']
        self.expected += flits
        self.packets += packets
        await self.fub.send_burst([self.to_gaxi(f) for f in flits])
        ok = await self.wait_until(lambda: self.rx.stats['flits'] - start >= len(flits),
                                   200 * len(flits) + 2000, f"{name}: {len(flits)} flits")
        self.log.info(f"phase {name}: {len(packets)} packets / {len(flits)} flits "
                      f"{'ok' if ok else 'FAILED'} max_credits={self.mon.max_credits} "
                      f"stalls={self.rx.stats['grant_blocked_full']}")
        return ok

    async def run_pool_fill(self):
        """Link up, nothing to send, receiver pool of B credits: the DUT must
        hold exactly B (it tracks every grant and spends none)."""
        bound = self.rx.buffer_depth
        for _ in range(4 * bound + 40):
            await RisingEdge(self.clk)
        held = int(self.dut.credits.value)
        self.log.info(f"pool fill: DUT holds {held}, monitor {self.mon.tx_credits}, pool {bound}")
        if held != bound or self.mon.tx_credits != bound:
            self.errors.append(f"idle pool: DUT {held} / monitor {self.mon.tx_credits}, expected {bound}")
            return False
        return True

    async def run_idle_deactivate(self):
        """Idle RUN cycles take the link to STOP with every credit home."""
        if not self.cfg.link_control:
            return True
        held = int(self.dut.credits.value)
        returns = self.mon.stats['returns']
        self.dut.cfg_idle_cycles.value = 8
        ok = await self.wait_until(lambda: self.mon.link_state == STOP, 2000, "idle deactivation")
        if ok:
            await RisingEdge(self.clk)
            if int(self.dut.credits.value) or self.mon.tx_credits:
                self.errors.append(f"STOP with credits: dut={int(self.dut.credits.value)} "
                                   f"monitor={self.mon.tx_credits}")
            # every credit held (and any granted since) must come back on CRDRTN
            if self.mon.stats['returns'] - returns < held:
                self.errors.append(f"deactivated holding {held} credits but returned "
                                   f"{self.mon.stats['returns'] - returns}")
        self.dut.cfg_idle_cycles.value = 0
        return ok

    async def run_hint_deactivate(self):
        """CXSDEACTHINT alone takes the link down (cfg_idle_cycles = 0)."""
        if not self.cfg.link_control:
            return True
        ok = await self.run_phase('pre-hint', 4)
        self.rx.set_deact_hint(True)
        ok = ok and await self.wait_until(lambda: self.mon.link_state == STOP, 2000, "hint deactivation")
        self.rx.set_deact_hint(False)
        return ok

    async def run_parity_injection(self):
        """A corrupted CXSCRDGNTCHK must set the sticky parity_error."""
        if not self.cfg.check:
            return True
        if int(self.dut.parity_error.value):
            self.errors.append("parity_error set before any injection")
            return False
        self.rx.inject_check_error('crdgnt', 1)
        ok = await self.wait_until(lambda: int(self.dut.parity_error.value) == 1, 50,
                                   "parity_error after a bad CXSCRDGNTCHK")
        return ok

    # ---- verdict --------------------------------------------------------
    def check(self):
        self.compare_flits(self.expected, list(self.rx._recvQ), 'receiver')
        self.compare_flits(self.expected, list(self.mon._recvQ), 'monitor')
        if self.rx.packets != self.packets:
            self.errors.append(f"receiver reassembled {len(self.rx.packets)} packets, "
                               f"expected {len(self.packets)} (or contents differ)")
        if self.rx.depacketizer.violations:
            self.errors.append(f"placement: {self.rx.depacketizer.violations[:3]}")
        self.check_violations(self.rx, self.mon)
        if int(self.dut.protocol_error.value):
            self.errors.append("DUT protocol_error set")
        return self.report()
