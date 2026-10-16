# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: cxs_slave_tb
# Purpose: Testbench for cxs_slave / cxs_slave_cg: the framework
#          CXSTransmitter on the link, a GAXI slave on the FUB side, and a
#          CXSMonitor checking the wires
#
# Documentation: docs/markdown/rtl-amba/cxs/cxs_slave.md
# Subsystem: amba
# Author: sean galloway
# Created: 2026-10-15
"""
The transmitter BFM packs random packets into flits; every one must come out
of fub_cxs_* in order, field for field. The monitor's credit model judges the
DUT's grants: it must never let the transmitter hold more than
min(RX_FIFO_DEPTH, CXS_MAX_CREDIT) credits, and under FUB backpressure it
must REACH that bound (otherwise the credit pool was never exercised).

Phases:
  stream       back-to-back flits, FUB always ready
  backpressure FUB slow: credits are the only flow control, the FIFO fills
  gappy        sparse flits
  idle         (link control) the transmitter goes idle and drops ACTIVEREQ:
               the DUT must take every credit back before it drops ACTIVEACK
  hint         (link control) cfg_deact_hint drives CXSDEACTHINT and the
               transmitter BFM deactivates on it
  parity       (CXS_CHECK) a corrupted CXSDATACHK must set parity_error
"""

import cocotb
from cocotb.triggers import RisingEdge

from CocoTBFramework.components.cxs import (STOP, create_cxs_monitor, create_cxs_transmitter)
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_slave
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from TBClasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS
from TBClasses.cxs.cxs_tb_common import TX_PROFILES, CXSTBBase


class CXSSlaveTB(CXSTBBase):
    def __init__(self, dut, cg=False, rx_fifo_depth=None):
        super().__init__(dut, cg)
        cfg = self.cfg
        self.rx_fifo_depth = rx_fifo_depth or cfg.max_credit
        self.tx = create_cxs_transmitter(dut, 'CXS TX', 's_cxs_', self.clk, cfg, reset=self.rst_n,
                                         randomizer=FlexRandomizer(TX_PROFILES['b2b']),
                                         idle_deactivate=None, log=self.log)
        self.mon = create_cxs_monitor(dut, 'CXS Mon', 's_cxs_', self.clk, cfg, reset=self.rst_n,
                                      log=self.log)
        self.fub = create_gaxi_slave(
            dut, 'FUB', '', self.clk, field_config=self.fub_fc, pkt_prefix='fub_cxs',
            randomizer=FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fixed']['slave']),
            memory_model=None, log=self.log, multi_sig=True)
        self.got = []
        self.fub.add_callback(self.got.append)
        self.expected = []
        self.packets = []
        self.peak_credits = {}

    def _pre_reset(self):
        super()._pre_reset()
        self.dut.cfg_rx_enable.value = 1
        self.dut.cfg_deact_hint.value = 0

    async def setup_clocks_and_reset(self):
        await super().setup_clocks_and_reset()
        if self.cg:
            cocotb.start_soon(self.count_gating())

    # ---- traffic --------------------------------------------------------
    async def run_phase(self, name, count, tx_profile='b2b', fub_profile='fixed'):
        self.tx.set_randomizer(FlexRandomizer(TX_PROFILES[tx_profile]))
        # a named AXI profile, or an explicit FlexRandomizer constraint dict
        fub = fub_profile if isinstance(fub_profile, dict) else AXI_RANDOMIZER_CONFIGS[fub_profile]['slave']
        self.fub.set_randomizer(FlexRandomizer(fub))
        packets = self.make_packets(count)
        flits = self.packetize(packets)
        start = len(self.got)
        self.expected += flits
        self.packets += packets
        self.mon.max_credits = 0
        for f in flits:
            self.tx.send_flit(f)
        ok = await self.wait_until(lambda: len(self.got) - start >= len(flits),
                                   300 * len(flits) + 2000, f"{name}: {len(flits)} flits")
        self.peak_credits[name] = self.mon.max_credits
        self.log.info(f"phase {name}: {len(packets)} packets / {len(flits)} flits "
                      f"{'ok' if ok else 'FAILED'} peak credits={self.mon.max_credits} "
                      f"tx stalls={self.tx.stats['stall_cycles']}")
        return ok

    async def run_pool_fill(self):
        """Link up, nothing to send: the DUT must grant its WHOLE pool and
        then stop -- exactly min(RX_FIFO_DEPTH, CXS_MAX_CREDIT) credits at the
        transmitter, never more. Proves both the grant path and its bound."""
        bound = min(self.rx_fifo_depth, self.cfg.max_credit)
        await self.wait_until(lambda: not self.tx.queue and not self.fub_pending(), 5000, "drain")
        for _ in range(4 * bound + 40):
            await RisingEdge(self.clk)
        held, out = self.mon.tx_credits, int(self.dut.credits_outstanding.value)
        self.log.info(f"pool fill: monitor {held} credits, DUT {out} outstanding, bound {bound}")
        if held != bound or out != bound:
            self.errors.append(f"idle pool: monitor {held} / DUT {out} credits, expected {bound}")
            return False
        return True

    def fub_pending(self):
        return len(self.got) < len(self.expected)

    async def run_idle_deactivate(self):
        """The transmitter BFM drops ACTIVEREQ; the DUT must collect every
        credit before ACTIVEACK falls (the monitor checks it on the wires)."""
        if not self.cfg.link_control:
            return True
        self.tx.idle_deactivate = 4
        ok = await self.wait_until(lambda: self.mon.link_state == STOP, 2000, "deactivation")
        if ok:
            await RisingEdge(self.clk)
            if int(self.dut.credits_outstanding.value):
                self.errors.append(f"STOP with {int(self.dut.credits_outstanding.value)} credits out")
        self.tx.idle_deactivate = None
        return ok

    async def run_hint_deactivate(self):
        if not self.cfg.link_control:
            return True
        ok = await self.run_phase('pre-hint', 4)
        self.dut.cfg_deact_hint.value = 1
        ok = ok and await self.wait_until(lambda: self.mon.link_state == STOP, 2000, "hint deactivation")
        self.dut.cfg_deact_hint.value = 0
        return ok

    async def run_parity_injection(self):
        if not self.cfg.check:
            return True
        if int(self.dut.parity_error.value):
            self.errors.append("parity_error set before any injection")
            return False
        self.tx.inject_check_error('data', 1)
        packets = self.make_packets(1)
        for f in self.packetize(packets):
            self.tx.send_flit(f)
        return await self.wait_until(lambda: int(self.dut.parity_error.value) == 1, 500,
                                     "parity_error after a bad CXSDATACHK")

    # ---- verdict --------------------------------------------------------
    def check(self):
        self.compare_flits(self.expected, self.got, 'fub')
        bound = min(self.rx_fifo_depth, self.cfg.max_credit)
        peak = max(self.peak_credits.values() or [0])
        if peak > bound:
            self.errors.append(f"transmitter held {peak} credits > bound {bound}")
        self.check_violations(self.tx, self.mon)
        if int(self.dut.protocol_error.value):
            self.errors.append("DUT protocol_error set")
        return self.report()
