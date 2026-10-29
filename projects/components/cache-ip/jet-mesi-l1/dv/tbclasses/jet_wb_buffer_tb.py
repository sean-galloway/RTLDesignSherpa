"""
jet_wb_buffer testbench

The decoupled writeback buffer: a VICTIM_DEPTH-deep FIFO of dirty victims
captured beat-serial from the data array and drained oldest-first in the
l1_victim shape {valid, addr, full_line}.  Direct pin-level stimulus scored
against a Python golden model (MAS ch02_blocks/03 contract).

Author: RTL Design Sherpa
Created: 2026-10-28
"""

import os
import random

from cocotb.triggers import RisingEdge, Timer

from TBClasses.shared.tbbase import TBBase

# jet_pkg encodings
JET_PEND_NONE = 0
JET_PEND_DOWNGRADE_S = 1
JET_PEND_INVALIDATE_I = 2


class WbBufferModel:
    """Golden model of the WB buffer per MAS ch02_blocks/03."""

    def __init__(self, victim_depth, line_w, line_bytes, bus_width):
        self.DEPTH = victim_depth
        self.LINE_W = line_w
        self.LINE_BYTES = line_bytes
        self.BUS_WIDTH = bus_width
        self.STRB_W = bus_width // 8
        self.FILL_BEATS = line_bytes // self.STRB_W
        self.LINE_WIDTH = line_bytes * 8
        self.entries = []   # list of dicts in FIFO order
        self.head = 0       # physical retire pointer
        self.tail = 0       # physical allocate pointer
        self.open_slot = None
        self.beats_rcvd = 0

    def _mask_line(self, line):
        return line & ((1 << self.LINE_W) - 1)

    def start_capture(self, line):
        if len(self.entries) >= self.DEPTH:
            return None
        slot = self.tail
        self.tail = (self.tail + 1) % self.DEPTH
        entry = {
            'line': self._mask_line(line),
            'data': 0,
            'beats_rcvd': 0,
            'valid': False,
            'eff': JET_PEND_NONE,
            'slot': slot,
        }
        self.entries.append(entry)
        self.open_slot = len(self.entries) - 1
        self.beats_rcvd = 0
        return slot

    def write_beat(self, data):
        if self.open_slot is None:
            return
        entry = self.entries[self.open_slot]
        shift = entry['beats_rcvd'] * self.BUS_WIDTH
        entry['data'] &= ~(((1 << self.BUS_WIDTH) - 1) << shift)
        entry['data'] |= (data & ((1 << self.BUS_WIDTH) - 1)) << shift
        entry['beats_rcvd'] += 1
        self.beats_rcvd = entry['beats_rcvd']
        if entry['beats_rcvd'] >= self.FILL_BEATS:
            entry['valid'] = True
            self.open_slot = None

    def oldest_valid(self):
        for i, e in enumerate(self.entries):
            if e['valid']:
                return i, e
        return None, None

    def retire(self):
        idx, entry = self.oldest_valid()
        if entry is not None:
            self.entries.pop(idx)
            self.head = (self.head + 1) % self.DEPTH

    def occupancy(self):
        return len(self.entries)

    def full(self):
        return len(self.entries) >= self.DEPTH

    def snarf_match(self, line):
        line = self._mask_line(line)
        for i, e in enumerate(self.entries):
            if e['valid'] and e['line'] == line:
                return i, e
        return None, None

    def apply_sn_eff(self, line, value):
        idx, entry = self.snarf_match(line)
        if entry is not None:
            entry['eff'] = value


class JetWbBufferTB(TBBase):
    """Drives jet_wb_buffer and scores observables against WbBufferModel."""

    OP_COUNTS = {'gate': 50, 'func': 500, 'full': 4000}

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        if self.TEST_LEVEL not in self.OP_COUNTS:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'gate'")
            self.TEST_LEVEL = 'gate'
        random.seed(self.SEED)
        self.VICTIM_DEPTH = self.convert_to_int(os.environ.get('VICTIM_DEPTH', '2'))
        self.LINE_W = len(dut.cap_line_i.value)
        self.ADDR_WIDTH = len(dut.drain_addr_o.value)
        self.LINE_BYTES = self.convert_to_int(os.environ.get('LINE_BYTES', '64'))
        self.BUS_WIDTH = self.convert_to_int(os.environ.get('BUS_WIDTH', '64'))
        self.STRB_W = self.BUS_WIDTH // 8
        self.FILL_BEATS = self.LINE_BYTES // self.STRB_W
        self.LINE_WIDTH = self.LINE_BYTES * 8
        self.SLOT_W = len(dut.cap_slot_o.value)
        self.OCC_W = len(dut.wb_occupancy_o.value)
        self.model = WbBufferModel(self.VICTIM_DEPTH, self.LINE_W,
                                   self.LINE_BYTES, self.BUS_WIDTH)
        self.checks = 0
        self.mismatches = 0
        self.log.info(f"JetWbBufferTB depth={self.VICTIM_DEPTH} line_w={self.LINE_W} "
                      f"addr_w={self.ADDR_WIDTH} line_bytes={self.LINE_BYTES} "
                      f"bus_width={self.BUS_WIDTH} level={self.TEST_LEVEL} seed={self.SEED}")

    # -- mandatory methods --------------------------------------------------
    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock('clk', freq=period_ns, units='ns')
        self._drive_idle()
        self.dut.sn_line_i.value = 0
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
        d.cap_i.value = 0
        d.cap_line_i.value = 0
        d.cap_beat_i.value = 0
        d.cap_beat_data_i.value = 0
        d.drain_done_i.value = 0
        d.sn_line_i.value = 0
        d.sn_eff_i.value = 0

    async def _settle(self):
        await Timer(1, unit='ns')

    def _score(self, what, got, exp):
        self.checks += 1
        if got != exp:
            self.mismatches += 1
            if self.mismatches <= 20:
                self.log.error(f"{what}: got {got} expected {exp}")

    def _mkline(self, tag):
        return tag & ((1 << self.LINE_W) - 1)

    def _mkaddr(self, tag):
        """Expand a line tag to a full byte address (offset bits zero)."""
        return self._mkline(tag) * self.LINE_BYTES

    def _mkline_data(self, tag):
        """Build a full line whose beats are tagged by (tag, beat_num)."""
        data = 0
        for b in range(self.FILL_BEATS):
            beat = ((tag << 8) | b) & ((1 << self.BUS_WIDTH) - 1)
            data |= beat << (b * self.BUS_WIDTH)
        return data

    async def _check_occupancy(self, note):
        await self._settle()
        self._score(f"{note} wb_occupancy_o",
                    int(self.dut.wb_occupancy_o.value), self.model.occupancy())

    async def _check_full(self, note, exp):
        await self._settle()
        self._score(f"{note} wb_full_o",
                    int(self.dut.wb_full_o.value), 1 if exp else 0)

    async def _check_drain_head(self, note):
        await self._settle()
        idx, entry = self.model.oldest_valid()
        exp_valid = 1 if entry is not None else 0
        self._score(f"{note} drain_valid_o",
                    int(self.dut.drain_valid_o.value), exp_valid)
        if entry is not None:
            self._score(f"{note} drain_addr_o",
                        int(self.dut.drain_addr_o.value), self._mkaddr(entry['line']))
            self._score(f"{note} drain_data_o",
                        int(self.dut.drain_data_o.value), entry['data'])

    async def _check_snarf(self, line, note, expect_match):
        d = self.dut
        d.sn_line_i.value = line
        await self._settle()
        idx, entry = self.model.snarf_match(line)
        exp_hit = 1 if (entry is not None and expect_match) else 0
        self._score(f"{note} sn_hit_o", int(d.sn_hit_o.value), exp_hit)
        if entry is not None and expect_match:
            self._score(f"{note} sn_data_o",
                        int(d.sn_data_o.value), entry['data'])

    # -- operations ---------------------------------------------------------
    async def _do_capture(self, tag, beats=None, note=""):
        """Capture one full victim line.  beats=None uses tagged beat data."""
        if beats is None:
            beats = [((tag << 8) | b) & ((1 << self.BUS_WIDTH) - 1)
                     for b in range(self.FILL_BEATS)]
        line = self._mkline(tag)
        d = self.dut
        d.cap_i.value = 1
        d.cap_line_i.value = line
        await self._settle()
        exp_gnt = 1 if not self.model.full() else 0
        self._score(f"{note} cap_gnt_o", int(d.cap_gnt_o.value), exp_gnt)
        if exp_gnt:
            slot = self.model.start_capture(line)
            self._score(f"{note} cap_slot_o", int(d.cap_slot_o.value), slot)
        else:
            await RisingEdge(d.clk)
            d.cap_i.value = 0
            d.cap_line_i.value = 0
            return None
        # Wait for the allocation edge before sending beats.  cap_i opens the
        # slot on the rising edge; cap_beat_i pulses begin the cycle after.
        await RisingEdge(d.clk)
        for i, beat in enumerate(beats):
            d.cap_beat_i.value = 1
            d.cap_beat_data_i.value = beat
            await self._settle()
            await RisingEdge(d.clk)
            self.model.write_beat(beat)
            d.cap_beat_i.value = 0
            d.cap_beat_data_i.value = 0
        d.cap_i.value = 0
        d.cap_line_i.value = 0
        await self._settle()
        await self._check_occupancy(note)
        return self.model.entries[-1] if self.model.entries else None

    async def _do_capture_pause_resume(self, tag, pause_after=2, pause_cycles=3, note=""):
        """Capture with a cap_i pause between beats; verifies slot resume."""
        assert 0 < pause_after < self.FILL_BEATS
        line = self._mkline(tag)
        d = self.dut
        d.cap_i.value = 1
        d.cap_line_i.value = line
        await self._settle()
        exp_gnt = 1 if not self.model.full() else 0
        self._score(f"{note} cap_gnt_o", int(d.cap_gnt_o.value), exp_gnt)
        if not exp_gnt:
            await RisingEdge(d.clk)
            d.cap_i.value = 0
            d.cap_line_i.value = 0
            return None
        slot = self.model.start_capture(line)
        self._score(f"{note} cap_slot_o", int(d.cap_slot_o.value), slot)
        await RisingEdge(d.clk)
        beats = [((tag << 8) | b) & ((1 << self.BUS_WIDTH) - 1)
                 for b in range(self.FILL_BEATS)]
        for i, beat in enumerate(beats):
            d.cap_beat_i.value = 1
            d.cap_beat_data_i.value = beat
            await self._settle()
            await RisingEdge(d.clk)
            self.model.write_beat(beat)
            d.cap_beat_i.value = 0
            d.cap_beat_data_i.value = 0
            if i == pause_after - 1:
                # Pause capture (data-array port sharing) then resume.
                d.cap_i.value = 0
                d.cap_line_i.value = 0
                for _ in range(pause_cycles):
                    await RisingEdge(d.clk)
                d.cap_i.value = 1
                d.cap_line_i.value = line
                await self._settle()
                self._score(f"{note} resume cap_slot_o", int(d.cap_slot_o.value), slot)
                await RisingEdge(d.clk)
        d.cap_i.value = 0
        d.cap_line_i.value = 0
        await self._settle()
        await self._check_occupancy(note)
        return self.model.entries[-1]

    async def _do_drain_one(self, note=""):
        """Retire the oldest valid entry with the BRESP pulse."""
        d = self.dut
        idx, entry = self.model.oldest_valid()
        assert entry is not None, f"{note}: no entry to drain"
        await self._check_drain_head(f"{note} pre-retire")
        d.drain_done_i.value = 1
        await RisingEdge(d.clk)
        self.model.retire()
        d.drain_done_i.value = 0
        await self._check_occupancy(note)

    async def _do_bresp(self, note=""):
        """Retire the oldest entry with BRESP only."""
        d = self.dut
        d.drain_done_i.value = 1
        await RisingEdge(d.clk)
        self.model.retire()
        d.drain_done_i.value = 0
        await self._check_occupancy(note)

    # -- directed scenarios -------------------------------------------------
    async def _scen_capture_then_drain(self):
        """Capture a victim over beats, then BRESP-retire it."""
        await self._do_capture(0xA5, note="cap1")
        await self._check_drain_head("cap1 captured")
        await self._do_drain_one(note="cap1 drain")

    async def _scen_capture_pause_resume(self):
        """Partial capture pauses and resumes without leaking the slot."""
        await self._do_capture_pause_resume(0xB6, pause_after=2, pause_cycles=3, note="pause")
        await self._check_drain_head("pause captured")
        await self._do_drain_one(note="pause drain")

    async def _scen_full_stall(self):
        """VICTIM_DEPTH captures -> wb_full_o; drain one reopens one slot."""
        tags = list(range(0x10, 0x10 + self.VICTIM_DEPTH))
        entries = []
        for i, tag in enumerate(tags):
            e = await self._do_capture(tag, note=f"full[{i}]")
            entries.append(e)
        await self._check_full("full after captures", True)
        d = self.dut
        d.cap_i.value = 1
        d.cap_line_i.value = self._mkline(0x99)
        await self._settle()
        self._score("full cap_gnt_o stall", int(d.cap_gnt_o.value), 0)
        await RisingEdge(d.clk)
        d.cap_i.value = 0
        # Drain one -> full drops, one more capture fits.
        await self._do_drain_one(note="full drain first")
        await self._check_full("full after one drain", False)
        await self._do_capture(0x99, note="full reopen")
        # Drain the rest
        while self.model.oldest_valid()[1] is not None:
            await self._do_drain_one(note="full drain rest")

    async def _scen_oldest_first_order(self):
        """Capture A,B; B only reaches head after A's BRESP."""
        await self._do_capture(0xA1, note="order A")
        await self._do_capture(0xB2, note="order B")
        # Delay BRESP for A, verify head stays A.
        d = self.dut
        for _ in range(3):
            await self._check_drain_head("order A waiting BRESP")
            await RisingEdge(d.clk)
        # BRESP A
        await self._do_bresp("order A bresp")
        # Drain B
        await self._do_drain_one(note="order B")

    async def _scen_snarf_hit(self):
        """Snoop matching a valid entry returns the entry data."""
        tag = 0xD4
        await self._do_capture(tag, note="snarf capture")
        line = self._mkline(tag)
        await self._check_snarf(line, "snarf hit", expect_match=True)
        await self._check_snarf(self._mkline(0xE5), "snarf miss", expect_match=False)
        await self._do_drain_one(note="snarf drain")

    async def _scen_snarf_at_bresp(self):
        """Snoop in the entry's BRESP cycle is still answered (Review Focus 3)."""
        tag = 0xF6
        await self._do_capture(tag, note="bresp capture")
        line = self._mkline(tag)
        d = self.dut
        # Present snoop + BRESP in the same cycle.
        d.sn_line_i.value = line
        d.drain_done_i.value = 1
        await self._settle()
        self._score("bresp_cycle sn_hit_o", int(d.sn_hit_o.value), 1)
        self._score("bresp_cycle sn_data_o", int(d.sn_data_o.value),
                    self._mkline_data(tag))
        self._score("bresp_cycle sn_bresp_cycle_o",
                    int(d.sn_bresp_cycle_o.value), 1)
        await RisingEdge(d.clk)
        self.model.retire()
        d.sn_line_i.value = 0
        d.drain_done_i.value = 0

    async def _scen_snarf_invalidated_still_drains(self):
        """Invalidated snarfed victim still drains to completion."""
        tag = 0x77
        await self._do_capture(tag, note="inv capture")
        line = self._mkline(tag)
        # Snoop match + record invalidate effect.
        d = self.dut
        d.sn_line_i.value = line
        d.sn_eff_i.value = JET_PEND_INVALIDATE_I
        await self._settle()
        self.model.apply_sn_eff(line, JET_PEND_INVALIDATE_I)
        self._score("inv sn_hit_o", int(d.sn_hit_o.value), 1)
        await RisingEdge(d.clk)
        d.sn_line_i.value = 0
        d.sn_eff_i.value = 0
        # Entry must still drain to completion.
        await self._do_drain_one(note="inv drain")
        await self._check_occupancy("inv retired")
        assert self.model.occupancy() == 0

    # -- random phase -------------------------------------------------------
    async def _random_phase(self, n_ops):
        self.log.info(f"jet_wb_buffer: {n_ops} random ops at {self.TEST_LEVEL}")
        for i in range(n_ops):
            m = self.model
            valids = [e for e in m.entries if e['valid']]
            r = random.random()
            if r < 0.30 and not m.full():
                tag = random.randrange(1 << self.LINE_W)
                await self._do_capture(tag, note=f"rnd{i} cap")
            elif r < 0.55 and valids:
                idx, entry = m.oldest_valid()
                if entry is not None and random.random() < 0.6:
                    await self._do_bresp(f"rnd{i} bresp")
            elif r < 0.80 and valids:
                entry = random.choice(valids)
                line = entry['line']
                eff = random.choice([JET_PEND_DOWNGRADE_S, JET_PEND_INVALIDATE_I])
                d = self.dut
                d.sn_line_i.value = line
                d.sn_eff_i.value = eff
                await self._settle()
                m.apply_sn_eff(line, eff)
                await RisingEdge(d.clk)
                d.sn_line_i.value = 0
                d.sn_eff_i.value = 0
            else:
                await self.wait_clocks('clk', 1)
            # occasional checks
            if random.random() < 0.3:
                await self._check_occupancy(f"rnd{i}")
            if random.random() < 0.3 and valids:
                idx, e = m.oldest_valid()
                if e is not None:
                    await self._check_drain_head(f"rnd{i}")

    # -- test ---------------------------------------------------------------
    async def run(self) -> bool:
        await self._scen_capture_then_drain()
        await self._scen_capture_pause_resume()
        await self._scen_full_stall()
        await self._scen_oldest_first_order()
        await self._scen_snarf_hit()
        await self._scen_snarf_at_bresp()
        await self._scen_snarf_invalidated_still_drains()
        await self._random_phase(self.OP_COUNTS[self.TEST_LEVEL])
        # drain anything left
        while self.model.oldest_valid()[1] is not None:
            await self._do_drain_one(note="final drain")
        return self.mismatches == 0

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches}
