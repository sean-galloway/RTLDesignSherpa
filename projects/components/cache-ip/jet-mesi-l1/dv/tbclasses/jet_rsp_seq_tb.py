"""
jet_rsp_seq testbench

The response sequencer: a CAM-free ring of per-tag completion records that
lets fills and merges complete out of order while GAXI responses leave in
request-accept order (MAS ch02_blocks/04).  Direct pin-level stimulus scored
against a Python golden model.

Author: RTL Design Sherpa
Created: 2026-10-28
"""

import os
import random

from cocotb.triggers import RisingEdge, Timer

from TBClasses.shared.tbbase import TBBase


class RspSeqModel:
    """Golden model of the response sequencer per MAS ch02_blocks/04."""

    def __init__(self, rsp_depth, bus_width):
        self.DEPTH = rsp_depth
        self.BUS_WIDTH = bus_width
        self.entries = {}      # tag -> data for deposited-but-not-released
        self.alloc_tag = 0
        self.rel_tag = 0
        self.occupancy = 0

    def _mask_data(self, data):
        return data & ((1 << self.BUS_WIDTH) - 1)

    def _allocated_tags(self):
        return {(self.rel_tag + k) % self.DEPTH for k in range(self.occupancy)}

    def request_tag(self):
        if self.occupancy >= self.DEPTH:
            return None
        tag = self.alloc_tag
        self.alloc_tag = (self.alloc_tag + 1) % self.DEPTH
        self.occupancy += 1
        return tag

    def deposit(self, tag, data):
        self.entries[tag] = self._mask_data(data)

    def can_release(self):
        return self.rel_tag in self.entries

    def peek_release_data(self):
        return self.entries.get(self.rel_tag, 0)

    def release(self):
        if self.rel_tag not in self.entries:
            return None
        data = self.entries.pop(self.rel_tag)
        self.rel_tag = (self.rel_tag + 1) % self.DEPTH
        self.occupancy -= 1
        return data

    def full(self):
        return self.occupancy >= self.DEPTH

    def deposited_count(self):
        return len(self.entries)


class JetRspSeqTB(TBBase):
    """Drives jet_rsp_seq and scores observables against RspSeqModel."""

    OP_COUNTS = {'gate': 50, 'func': 500, 'full': 4000}

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        if self.TEST_LEVEL not in self.OP_COUNTS:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'gate'")
            self.TEST_LEVEL = 'gate'
        random.seed(self.SEED)
        self.RSP_DEPTH = self.convert_to_int(os.environ.get('RSP_DEPTH', '10'))
        self.BUS_WIDTH = self.convert_to_int(os.environ.get('BUS_WIDTH', '64'))
        self.SEQ_W = len(dut.tag_o.value)
        self.model = RspSeqModel(self.RSP_DEPTH, self.BUS_WIDTH)
        self.checks = 0
        self.mismatches = 0
        self.releases = 0
        self.log.info(f"JetRspSeqTB depth={self.RSP_DEPTH} bus_width={self.BUS_WIDTH} "
                      f"seq_w={self.SEQ_W} level={self.TEST_LEVEL} seed={self.SEED}")

    # -- mandatory methods --------------------------------------------------
    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock('clk', freq=period_ns, units='ns')
        self._drive_idle()
        await self.assert_reset()
        await self.wait_clocks('clk', 3)
        await self.deassert_reset()
        await self.wait_clocks('clk', 1)

    async def assert_reset(self):
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        self.dut.rst_n.value = 1

    # -- helpers ------------------------------------------------------------
    def _drive_idle(self):
        d = self.dut
        d.tag_req_i.value = 0
        d.cpl_i.value = 0
        d.cpl_tag_i.value = 0
        d.cpl_data_i.value = 0
        d.rsp_ready_i.value = 0

    async def _settle(self):
        await Timer(1, unit='ns')

    def _score(self, what, got, exp):
        self.checks += 1
        if got != exp:
            self.mismatches += 1
            if self.mismatches <= 20:
                self.log.error(f"{what}: got {got} expected {exp}")

    def _mkdata(self, tag, salt=0):
        """Turn a tag into a deterministic data payload."""
        return ((tag + 1) * 0x11111111 + salt) & ((1 << self.BUS_WIDTH) - 1)

    async def _check_head(self, note):
        await self._settle()
        exp_valid = 1 if self.model.can_release() else 0
        self._score(f"{note} rsp_valid_o", int(self.dut.rsp_valid_o.value), exp_valid)
        if self.model.can_release():
            self._score(f"{note} rsp_data_o",
                        int(self.dut.rsp_data_o.value),
                        self.model.peek_release_data())

    # -- operations ---------------------------------------------------------
    async def _request_tag(self, note=""):
        """Request one tag; returns granted tag or None."""
        d = self.dut
        d.tag_req_i.value = 1
        await self._settle()
        gnt = int(d.tag_gnt_o.value)
        tag = int(d.tag_o.value) if gnt else None
        if gnt:
            exp = self.model.request_tag()
            self._score(f"{note} tag_gnt_o", gnt, 1)
            self._score(f"{note} tag_o", tag, exp)
        else:
            self._score(f"{note} tag_gnt_o", gnt, 0)
        await RisingEdge(d.clk)
        d.tag_req_i.value = 0
        return tag

    async def _deposit(self, tag, data, note=""):
        """Deposit a completion record at tag."""
        d = self.dut
        d.cpl_i.value = 1
        d.cpl_tag_i.value = tag
        d.cpl_data_i.value = data
        await self._settle()
        self.model.deposit(tag, data)
        await RisingEdge(d.clk)
        d.cpl_i.value = 0
        d.cpl_tag_i.value = 0
        d.cpl_data_i.value = 0

    async def _release_one(self, note=""):
        """Release the head response if valid; returns released data or None."""
        d = self.dut
        await self._settle()
        can = self.model.can_release()
        rtl_valid = int(d.rsp_valid_o.value)
        self._score(f"{note} rsp_valid_o", rtl_valid, 1 if can else 0)
        if can:
            self._score(f"{note} rsp_data_o",
                        int(d.rsp_data_o.value), self.model.peek_release_data())
        d.rsp_ready_i.value = 1
        await RisingEdge(d.clk)
        d.rsp_ready_i.value = 0
        # Keep the model locked to what the RTL actually did.
        if can and rtl_valid:
            data = self.model.release()
            if data is not None:
                self.releases += 1
            return data
        return None

    async def _drain_all(self, note=""):
        """Release every completed response in tag order."""
        while self.model.can_release():
            await self._release_one(note=f"{note} drain")

    # -- directed scenarios -------------------------------------------------
    async def _scen_in_order_release(self):
        """Deposits complete out of order; releases leave in tag order."""
        tags = []
        for _ in range(min(3, self.RSP_DEPTH)):
            t = await self._request_tag(note="inorder alloc")
            assert t is not None
            tags.append(t)
        # Deposit tags out of order: last, first, middle.
        await self._deposit(tags[-1], self._mkdata(tags[-1]), note="inorder cpl last")
        await self._check_head("inorder head blocked")
        await self._deposit(tags[0], self._mkdata(tags[0]), note="inorder cpl head")
        await self._check_head("inorder head ready")
        await self._deposit(tags[1], self._mkdata(tags[1]), note="inorder cpl mid")
        # Drain in tag order.
        for t in tags:
            await self._release_one(note=f"inorder release[{t}]")

    async def _scen_head_of_line(self):
        """An incomplete head blocks the port; later tags do not pass it."""
        tags = []
        for _ in range(min(3, self.RSP_DEPTH)):
            t = await self._request_tag(note="hol alloc")
            assert t is not None
            tags.append(t)
        # Complete tags 1 and 2 but not head (tag 0).
        await self._deposit(tags[1], self._mkdata(tags[1]), note="hol cpl[1]")
        await self._deposit(tags[2], self._mkdata(tags[2]), note="hol cpl[2]")
        for _ in range(3):
            await self._check_head("hol blocked")
            await self.wait_clocks('clk', 1)
        # Complete the head.
        await self._deposit(tags[0], self._mkdata(tags[0]), note="hol cpl[0]")
        # Now drain 0, 1, 2.
        for t in tags:
            await self._release_one(note=f"hol release[{t}]")

    async def _scen_backpressure_freedom(self):
        """rsp_ready_i low holds only the release pointer; deposits continue."""
        d = self.dut
        # Allocate every tag first.
        tags = []
        while not self.model.full():
            t = await self._request_tag(note="bp alloc")
            assert t is not None
            tags.append(t)
        # Hold rsp_ready_i low and deposit completions in random order.
        d.rsp_ready_i.value = 0
        random.shuffle(tags)
        bp_cycles = 50
        cpl_idx = 0
        for cyc in range(bp_cycles):
            if cpl_idx < len(tags):
                await self._deposit(tags[cpl_idx], self._mkdata(tags[cpl_idx]),
                                    note=f"bp cpl[{tags[cpl_idx]}]")
                cpl_idx += 1
            else:
                await self._check_head("bp hold")
                await self.wait_clocks('clk', 1)
        self._score("bp deposited count", self.model.deposited_count(), len(tags))
        # Release resumes in order.
        d.rsp_ready_i.value = 1
        for _ in range(len(tags)):
            await self._settle()
            self._score("bp release valid", int(d.rsp_valid_o.value), 1)
            exp = self.model.peek_release_data()
            self._score("bp release data", int(d.rsp_data_o.value), exp)
            await RisingEdge(d.clk)
            self.model.release()
            self.releases += 1
        d.rsp_ready_i.value = 0

    async def _scen_tag_reuse(self):
        """A released tag becomes available for the next allocation."""
        tags = []
        while not self.model.full():
            t = await self._request_tag(note="reuse alloc first")
            assert t is not None
            tags.append(t)
        # Complete and release the head only.
        head = tags[0]
        await self._deposit(head, self._mkdata(head), note="reuse cpl head")
        await self._release_one(note="reuse release head")
        # Next allocation must reuse the freed tag.
        t = await self._request_tag(note="reuse alloc second")
        self._score("reuse tag", t, head)
        await self._deposit(t, self._mkdata(t, salt=1), note="reuse cpl reused")
        await self._release_one(note="reuse release reused")
        # Drain anything left.
        await self._drain_all(note="reuse")

    async def _scen_wraparound(self):
        """Pointers wrap at RSP_DEPTH under sustained traffic."""
        for round_n in range(3):
            tags = []
            # Allocate every tag in this round.
            while not self.model.full():
                t = await self._request_tag(note=f"wrap{round_n} alloc")
                assert t is not None
                tags.append(t)
            # Deposit completions in reverse tag order: the head is completed
            # last, so the release pointer must wait for it and then wrap.
            for t in reversed(tags):
                await self._deposit(t, self._mkdata(t, salt=round_n),
                                    note=f"wrap{round_n} cpl[{t}]")
            # Drain in strict tag order; the final release wraps the pointer.
            for _ in tags:
                await self._release_one(note=f"wrap{round_n} release")

    # -- random phase -------------------------------------------------------
    async def _random_phase(self, n_ops):
        self.log.info(f"jet_rsp_seq: {n_ops} random ops at {self.TEST_LEVEL}")
        for i in range(n_ops):
            m = self.model
            r = random.random()
            if r < 0.25 and not m.full():
                await self._request_tag(note=f"rnd{i} alloc")
            elif r < 0.55:
                to_deposit = m._allocated_tags() - set(m.entries.keys())
                if to_deposit:
                    t = random.choice(list(to_deposit))
                    await self._deposit(t, random.randrange(1 << self.BUS_WIDTH),
                                        note=f"rnd{i} cpl[{t}]")
                else:
                    await self.wait_clocks('clk', 1)
            elif r < 0.80 and m.can_release():
                await self._release_one(note=f"rnd{i} release")
            else:
                await self.wait_clocks('clk', 1)
            if random.random() < 0.3:
                await self._check_head(f"rnd{i}")

    # -- test ---------------------------------------------------------------
    async def run(self) -> bool:
        await self._scen_in_order_release()
        await self._scen_head_of_line()
        await self._scen_backpressure_freedom()
        await self._scen_tag_reuse()
        await self._scen_wraparound()
        await self._random_phase(self.OP_COUNTS[self.TEST_LEVEL])
        await self._drain_all(note="final")
        return self.mismatches == 0

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches,
                'releases': self.releases}
