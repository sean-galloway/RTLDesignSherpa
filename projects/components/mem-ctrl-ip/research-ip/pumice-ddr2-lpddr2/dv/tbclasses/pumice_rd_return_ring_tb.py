# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Testbench for `pumice_rd_return_ring` -- the AR-order read-return ring.

Contract under test: tickets are handed out in alloc order; the DFI return
fills the ISSUE-order head's slot; the drain releases slots in ALLOC order
only once each slot's data is complete; a slot frees on its last drained
beat. Every handshake is BFM-driven (pumice_fub_bfm); the TB samples the
ring's ticket OUTPUT at the alloc handshake and never pokes a valid/ready.
"""

import os
import sys
import subprocess
from collections import deque

import cocotb
from cocotb.triggers import RisingEdge

_repo_root = subprocess.check_output(
    ['git', 'rev-parse', '--show-toplevel']
).decode().strip()
if _repo_root not in sys.path:
    sys.path.insert(0, _repo_root)

from TBClasses.shared.tbbase import TBBase  # noqa: E402

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)
from tbclasses.pumice_fub_bfm import fub_consumer, fub_producer   # noqa: E402


class PumiceRdReturnRingTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.DEPTH = self.convert_to_int(os.environ.get('DEPTH', '32'))
        self.DW    = self.convert_to_int(os.environ.get('AXI_DATA_WIDTH', '64'))
        self.BL    = self.convert_to_int(os.environ.get('AXI_BEATS_PER_BURST', '4'))
        self.TW    = max(1, (self.DEPTH - 1).bit_length())
        self.tickets = deque()      # tickets in alloc order (sampled at handshake)
        self.drain_out = deque()    # completed drained bursts: [(data, resp), ...]

    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', freq=10, units='ns')
        self._build_bfms()
        await self.assert_reset()
        await self.wait_clocks('aclk', 5)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 5)
        cocotb.start_soon(self._mon_alloc())
        cocotb.start_soon(self._mon_drain())

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    def _build_bfms(self, profile="backtoback"):
        # alloc carries no payload INTO the DUT (the DUT returns the ticket).
        # The GAXI producer needs one payload field, so the DV wrapper top
        # (pumice_rd_return_ring_tb_top) adds an unused alloc_req_i for it.
        self.alloc_bfm = fub_producer(
            self.dut, "alloc", self.dut.aclk, profile=profile, log=self.log,
            valid="alloc_valid_i", ready="alloc_ready_o",
            fields={'req': ("alloc_req_i", 1)})
        self.issue_bfm = fub_producer(
            self.dut, "issue", self.dut.aclk, profile=profile, log=self.log,
            valid="issue_valid_i", ready="issue_ready_o",
            fields={'ticket': ("issue_ticket_i", self.TW)})
        self.dfi_ret_bfm = fub_producer(
            self.dut, "dfi_ret", self.dut.aclk, profile=profile, log=self.log,
            valid="dfi_ret_valid_i", ready="dfi_ret_ready_o",
            fields={'data': ("dfi_ret_data_i", self.DW),
                    'resp': ("dfi_ret_resp_i", 2),
                    'last': ("dfi_ret_last_i", 1)})
        self.drain_bfm = fub_consumer(
            self.dut, "drain", self.dut.aclk, profile=profile, log=self.log,
            valid="drain_valid_o", ready="drain_ready_i",
            fields={'data': ("drain_data_o", self.DW),
                    'resp': ("drain_resp_o", 2),
                    'last': ("drain_last_o", 1)})

    def set_drain_ready(self, accepting: bool):
        self.drain_bfm.set_ready_policy('always' if accepting else 'stall')

    async def _mon_alloc(self):
        while True:
            await RisingEdge(self.dut.aclk)
            if int(self.dut.alloc_valid_i.value) and int(self.dut.alloc_ready_o.value):
                self.tickets.append(int(self.dut.alloc_ticket_o.value))

    async def _mon_drain(self):
        cur = []
        while True:
            await RisingEdge(self.dut.aclk)
            while self.drain_bfm._recvQ:
                p = self.drain_bfm._recvQ.popleft()
                cur.append((p.data, p.resp))
                if p.last:
                    self.drain_out.append(cur)
                    cur = []

    async def alloc(self):
        """One allocation; returns the ticket the DUT handed out."""
        n0 = len(self.tickets)
        await self.alloc_bfm.send(self.alloc_bfm.create_packet(req=1))
        for _ in range(200):
            if len(self.tickets) > n0:
                return self.tickets[-1]
            await RisingEdge(self.dut.aclk)
        raise AssertionError("alloc handshake never completed")

    async def issue(self, ticket):
        await self.issue_bfm.send(self.issue_bfm.create_packet(ticket=ticket))

    async def dfi_return(self, data, resp=0):
        n = len(data)
        for i, d in enumerate(data):
            await self.dfi_ret_bfm.send(self.dfi_ret_bfm.create_packet(
                data=d, resp=resp, last=1 if i == n - 1 else 0))

    def occ(self):
        return int(self.dut.occ_o.value)

    def alloc_ready(self):
        return int(self.dut.alloc_ready_o.value)

    def drain_valid(self):
        return int(self.dut.drain_valid_o.value)

    async def wait_drained(self, n, limit=2000):
        for _ in range(limit):
            if len(self.drain_out) >= n:
                return
            await RisingEdge(self.dut.aclk)
        raise AssertionError(f"only {len(self.drain_out)}/{n} bursts drained")
