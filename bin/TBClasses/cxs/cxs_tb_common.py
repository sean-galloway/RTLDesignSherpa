# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: cxs_tb_common
# Purpose: Shared pieces of the cxs_master / cxs_slave testbenches
#
# Documentation: docs/markdown/rtl-amba/cxs/README.md
# Subsystem: amba
# Author: sean galloway
# Created: 2026-10-15
"""Shared CXS testbench parts.

The DUT's property set travels from the pytest runner as environment
variables named exactly like the RTL parameters (``CXS_ISSUE``,
``CXS_DATA_WIDTH`` ...); :func:`cfg_from_env` rebuilds the framework
:class:`CXSConfig` from them, so the BFMs bind exactly the signals the DUT
was built with. The FUB side of both endpoints is a valid/ready port and is
driven by the framework GAXI BFMs, never by hand.
"""

import os
import random

from cocotb.triggers import RisingEdge

from CocoTBFramework.components.cxs import CXSConfig, CXSPacketizer, random_packet
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from TBClasses.shared.tbbase import TBBase

PARAM_NAMES = ('CXS_ISSUE', 'CXS_DATA_WIDTH', 'CXS_MAX_PKT_PER_FLIT', 'CXS_START_ALIGN',
               'CXS_HAS_LAST', 'CXS_HAS_PRCLTYPE', 'CXS_SRCID_WIDTH', 'CXS_TGTID_WIDTH',
               'CXS_USER_WIDTH', 'CXS_MAX_CREDIT', 'CXS_LINK_CTRL', 'CXS_CHECK')

# Receiver BFM timing profiles (the DUT is a transmitter): how fast credits
# come back. 'starve' drains slowly, so the credit pool empties and the DUT
# must stall with flits queued -- the credit gate's only real test.
RX_PROFILES = {
    'fast':   {'grant_gap': ([(0, 0)], [1]), 'drain_gap': ([(0, 0)], [1]), 'ack_delay': ([(0, 0)], [1])},
    'gappy':  {'grant_gap': ([(0, 0), (1, 3)], [3, 1]), 'drain_gap': ([(0, 0), (1, 2)], [3, 1]),
               'ack_delay': ([(1, 6)], [1])},
    'starve': {'grant_gap': ([(0, 0)], [1]), 'drain_gap': ([(4, 12)], [1]), 'ack_delay': ([(0, 2)], [1])},
}

# Transmitter BFM timing profiles (the DUT is a receiver)
TX_PROFILES = {
    'b2b':   {'valid_gap': ([(0, 0)], [1])},
    'gappy': {'valid_gap': ([(0, 0), (1, 4)], [3, 1])},
}


def cfg_from_env():
    p = {n: int(os.environ[n]) for n in PARAM_NAMES if n in os.environ}
    return CXSConfig(
        issue=p.get('CXS_ISSUE', 4), data_width=p.get('CXS_DATA_WIDTH', 256),
        max_pkt_per_flit=p.get('CXS_MAX_PKT_PER_FLIT', 2), start_align=p.get('CXS_START_ALIGN', 16),
        has_last=bool(p.get('CXS_HAS_LAST', 0)), has_prcltype=bool(p.get('CXS_HAS_PRCLTYPE', 0)),
        srcid_width=p.get('CXS_SRCID_WIDTH', 0), tgtid_width=p.get('CXS_TGTID_WIDTH', 0),
        user_width=p.get('CXS_USER_WIDTH', 0), max_credit=p.get('CXS_MAX_CREDIT', 15),
        link_control=bool(p.get('CXS_LINK_CTRL', 1)), check=bool(p.get('CXS_CHECK', 0)),
    ).validate()


def fub_field_config(cfg: CXSConfig) -> FieldConfig:
    """Every fub_cxs_* payload port, absent ones as their one-bit tie, so no
    DUT input is left at X."""
    fc = FieldConfig()

    def add(name, bits):
        fc.add_field(FieldDefinition(name=name, bits=max(1, bits), default=0, format="hex",
                                     display_width=(max(1, bits) + 3) // 4))
    add('data', cfg.data_width)
    add('cntl', cfg.cntl_width)
    add('last', 1)
    add('prcltype', 3)
    add('srcid', cfg.srcid_width)
    add('tgtid', cfg.tgtid_width)
    add('user', cfg.user_width)
    return fc


FLIT_FIELDS = ('data', 'cntl', 'last', 'prcltype', 'srcid', 'tgtid', 'user')


class CXSTBBase(TBBase):
    """Clock/reset, config, the traffic generator and the scoreboard."""

    def __init__(self, dut, cg=False):
        super().__init__(dut)
        self.clk = dut.aclk
        self.clk_name = 'aclk'
        self.rst_n = dut.aresetn
        self.cg = cg
        self.cfg = cfg_from_env()
        self.fub_fc = fub_field_config(self.cfg)
        self.seed = int(os.environ.get('SEED', '0'))
        self.rng = random.Random(self.seed)
        self.errors = []
        self.gated_cycles = 0
        self.log.info(f"CXS config {self.cfg.short_name()} seed={self.seed} cg={cg}")

    # ---- mandatory ------------------------------------------------------
    async def setup_clocks_and_reset(self):
        await self.start_clock(self.clk_name, 10, 'ns')
        self._pre_reset()
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)

    async def assert_reset(self):
        self.rst_n.value = 0

    async def deassert_reset(self):
        self.rst_n.value = 1

    def _pre_reset(self):
        if self.cg:
            self.dut.cfg_cg_enable.value = 1
            self.dut.cfg_cg_idle_count.value = 4

    # ---- traffic --------------------------------------------------------
    def streams(self):
        cfg = self.cfg
        other = (1 if cfg.has_prcltype else 0,
                 self.rng.randrange(1, 1 << cfg.srcid_width) if cfg.srcid_width else 0,
                 self.rng.randrange(1, 1 << cfg.tgtid_width) if cfg.tgtid_width else 0)
        return [(0, 0, 0), other] if any(other) else None

    def make_packets(self, count):
        cfg = self.cfg
        return [random_packet(cfg, self.rng, max_bytes=3 * cfg.flit_bytes, streams=self.streams(),
                              end_error_rate=0.1, keep_rate=0.15 if cfg.has_last else 0.0)
                for _ in range(count)]

    def packetize(self, packets):
        """The flits the packets become, with random CXSUSER bits and, for a
        4-byte start alignment, random 4-byte gaps (both legal)."""
        cfg = self.cfg
        gap = (lambda pos: self.rng.randint(0, 2)) if cfg.start_align == 4 and not cfg.is_lite else None
        flits = CXSPacketizer(cfg, gap_hook=gap).add_all(packets).flush()
        if cfg.user_width:
            for f in flits:
                f.fields['user'] = self.rng.getrandbits(cfg.user_width)
        return flits

    def to_gaxi(self, flit):
        pkt = GAXIPacket(self.fub_fc)
        for n in FLIT_FIELDS:
            setattr(pkt, n, flit.get(n, 0))
        return pkt

    # ---- scoreboard -----------------------------------------------------
    def compare_flits(self, expected, got, where):
        """Field-by-field, only the fields the interface carries."""
        if len(got) != len(expected):
            self.errors.append(f"{where}: {len(got)} flits, expected {len(expected)}")
        for i, (e, g) in enumerate(zip(expected, got)):
            for n in FLIT_FIELDS:
                if n not in e.fields:
                    continue
                v = int(g.get(n, 0)) if hasattr(g, 'cfg') else int(getattr(g, n))
                if v != e.get(n):
                    self.errors.append(f"{where} flit {i}: {n}=0x{v:X}, expected 0x{e.get(n):X}")
                    break
            if len(self.errors) > 20:
                return

    def check_violations(self, *bfms):
        for b in bfms:
            if b.total_violations():
                self.errors.append(f"{b.title}: violations {b.violations}")

    async def count_gating(self):
        """Background: cycles the clock gate is engaged (cg variants)."""
        while True:
            await RisingEdge(self.clk)
            if int(self.dut.cg_gating.value):
                self.gated_cycles += 1

    async def wait_until(self, cond, timeout, what):
        for _ in range(timeout):
            if cond():
                return True
            await RisingEdge(self.clk)
        self.errors.append(f"timeout waiting for {what}")
        return False

    def report(self):
        for e in self.errors[:20]:
            self.log.error(e)
        return not self.errors
