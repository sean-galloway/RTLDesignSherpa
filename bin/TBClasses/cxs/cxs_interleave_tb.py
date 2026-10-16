# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: cxs_interleave_tb
# Purpose: Per-stream packet framing in cxs_master / cxs_slave: packets of
#          several streams interleaved flit by flit on one link
#
# Documentation: docs/markdown/rtl-amba/cxs/README.md
# Subsystem: amba
# Author: sean galloway
# Created: 2026-10-16
"""
A CXS stream is the flits sharing CXSPRCLTYPE / CXSSRCID / CXSTGTID, and
flits of different streams may interleave (IHI 0079D 2.5.2), so an endpoint
must frame packets per stream. Packets for NSTREAMS source IDs are packetized
stream by stream and the flit lists are then interleaved round-robin: every
stream's packets are legal on their own, and every flit boundary may switch
stream with packets open.

With CXS_STREAM_SRCID_BITS covering the streams the endpoint must pass every
flit through in order with protocol_error low. With the key off (0 bits) the
endpoint tracks the link as one stream, so the same traffic MUST set
protocol_error: that half proves the key is what makes the difference, not
the traffic being too easy. The wire monitor tracks streams per the spec and
must report no violation either way.
"""

import os

from CocoTBFramework.components.cxs import CXSPacketizer, random_packet

from TBClasses.cxs.cxs_master_tb import CXSMasterTB
from TBClasses.cxs.cxs_slave_tb import CXSSlaveTB


def interleaved_flits(tb, nstreams, count):
    """count packets per stream, each packetized on its own, then the flit
    lists interleaved round-robin. Returns (flits, packets)."""
    cfg = tb.cfg
    per, packets = [], []
    for s in range(nstreams):
        pk = [random_packet(cfg, tb.rng, max_bytes=3 * cfg.flit_bytes, streams=[(0, s, 0)])
              for _ in range(count)]
        packets += pk
        per.append(CXSPacketizer(cfg).add_all(pk).flush())
    flits = []
    while any(per):
        for lst in per:
            if lst:
                flits.append(lst.pop(0))
    return flits, packets


class _InterleaveMixin:
    def _settings(self):
        self.nstreams = int(os.environ.get('TEST_NSTREAMS', '4'))
        self.expect_error = os.environ.get('EXPECT_PROTOCOL_ERROR', '0') == '1'

    def _verdict(self, delivered_ok, sent, delivered):
        err = int(self.dut.protocol_error.value)
        self.log.info(f"interleave: {self.nstreams} streams, key bits "
                      f"{os.environ.get('CXS_STREAM_SRCID_BITS')}, {sent} flits sent, "
                      f"{delivered} delivered, protocol_error={err} "
                      f"(expected {int(self.expect_error)}), monitor violations={self.mon.total_violations()}")
        if self.expect_error:
            if not err:
                self.errors.append("key off: interleaved streams did NOT set protocol_error "
                                   "(the endpoint is not tracking the link as one stream)")
        else:
            if err:
                self.errors.append("key on: protocol_error set on legal interleaved streams")
            if not delivered_ok:
                self.errors.append("not every flit came through")
        if self.mon.total_violations():
            self.errors.append(f"wire monitor flagged legal traffic: {self.mon.violations}")
        return self.report()


class CXSSlaveInterleaveTB(_InterleaveMixin, CXSSlaveTB):
    async def run_interleaved(self, count):
        self._settings()
        flits, _ = interleaved_flits(self, self.nstreams, count)
        self.expected += flits
        for f in flits:
            self.tx.send_flit(f)
        ok = await self.wait_until(lambda: len(self.got) >= len(flits), 300 * len(flits) + 2000,
                                   f"{len(flits)} interleaved flits")
        if not self.expect_error:
            self.compare_flits(self.expected, self.got, 'fub')
        elif not ok:
            self.errors.pop()           # with the key off, delivery is not the question
        return self._verdict(ok, len(flits), len(self.got))


class CXSMasterInterleaveTB(_InterleaveMixin, CXSMasterTB):
    async def run_interleaved(self, count):
        self._settings()
        flits, packets = interleaved_flits(self, self.nstreams, count)
        self.rx.buffer_depth = self.cfg.max_credit
        await self.fub.send_burst([self.to_gaxi(f) for f in flits])
        ok = await self.wait_until(lambda: self.rx.stats['flits'] >= len(flits),
                                   300 * len(flits) + 2000, f"{len(flits)} interleaved flits")
        if not self.expect_error:
            self.compare_flits(flits, list(self.rx._recvQ), 'receiver')
            got = sorted((p.srcid, p.payload) for p in self.rx.packets)
            want = sorted((p.srcid, p.payload) for p in packets)
            if got != want:
                self.errors.append(f"receiver reassembled {len(got)} packets, expected {len(want)}")
        elif not ok:
            self.errors.pop()
        return self._verdict(ok, len(flits), self.rx.stats['flits'])
