"""
jet_mshr testbench

The MAB (miss address buffer) file: a fully-associative CAM of outstanding
misses with per-set victim-claim counters. Direct pin-level stimulus -- the
DUT has no bus interface, so no BFM applies (same posture as amber_repl).

A small Python golden model (MshrModel) mirrors the MAS ch02_blocks/02
contract: entry fields, first-free alloc, lowest-index CAM match with
alloc-first same-cycle visibility, per-set claim counters with same-cycle
alloc/retire netting, merge-list append order, beat bitmask, pending snoop
effect, and the occupancy gauge.

Author: RTL Design Sherpa
Created: 2026-10-28
"""

import os
import random

from cocotb.triggers import RisingEdge, Timer

from TBClasses.shared.tbbase import TBBase

# jet_pkg encodings (kept as ints; the TB must not import the SV package)
JET_CLS_RNSD = 0
JET_CLS_RU = 1
JET_PEND_NONE = 0
JET_PEND_DOWNGRADE_S = 1
JET_PEND_INVALIDATE_I = 2


class MshrModel:
    """Golden model of the MAB per MAS ch02_blocks/02."""

    def __init__(self, mshr_count, sets, ways):
        self.N = mshr_count
        self.SETS = sets
        self.WAYS = ways
        self.valid = [False] * mshr_count
        self.line = [0] * mshr_count
        self.cls = [0] * mshr_count
        self.install = [0] * mshr_count
        self.victim_way = [0] * mshr_count
        self.wb_slot = [0] * mshr_count
        self.wb_valid = [0] * mshr_count
        self.merge = [[] for _ in range(mshr_count)]
        self.beats = [0] * mshr_count
        self.pend_eff = [0] * mshr_count
        self.claims = [0] * sets

    def free_sel(self):
        for e in range(self.N):
            if not self.valid[e]:
                return e
        return None

    def full(self):
        return all(self.valid)

    def set_full(self, s):
        return self.claims[s] >= self.WAYS

    def gnt(self, s):
        return (not self.full()) and (not self.set_full(s))

    def occupancy(self):
        return sum(1 for v in self.valid if v)

    def match(self, line):
        """Lowest-index valid entry whose line matches, else None."""
        for e in range(self.N):
            if self.valid[e] and self.line[e] == line:
                return e
        return None

    def apply_alloc(self, line, set_, cls, install, victim_way,
                    wb_slot, wb_valid, seq):
        idx = self.free_sel()
        self.valid[idx] = True
        self.line[idx] = line
        self.cls[idx] = cls
        self.install[idx] = install
        self.victim_way[idx] = victim_way
        self.wb_slot[idx] = wb_slot
        self.wb_valid[idx] = wb_valid
        self.merge[idx] = [seq]
        self.beats[idx] = 0
        self.pend_eff[idx] = JET_PEND_NONE
        self.claims[set_] += 1
        return idx

    def apply_retire(self, idx):
        if self.valid[idx]:
            self.claims[self.line[idx] % self.SETS] -= 1
            self.valid[idx] = False

    def apply_merge(self, idx, seq):
        if len(self.merge[idx]) < self.N:
            self.merge[idx].append(seq)

    def apply_beat(self, idx, num):
        self.beats[idx] |= (1 << num)

    def apply_sn_eff(self, idx, value):
        self.pend_eff[idx] = value


class JetMshrTB(TBBase):
    """Drives jet_mshr and scores every observable against MshrModel."""

    OP_COUNTS = {'gate': 60, 'func': 800, 'full': 6000}

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        if self.TEST_LEVEL not in self.OP_COUNTS:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'gate'")
            self.TEST_LEVEL = 'gate'
        random.seed(self.SEED)
        self.MSHR_COUNT = self.convert_to_int(os.environ.get('MSHR_COUNT', '8'))
        self.SETS = self.convert_to_int(os.environ.get('SETS', '128'))
        self.WAYS = self.convert_to_int(os.environ.get('WAYS', '4'))
        self.RSP_DEPTH = self.MSHR_COUNT + 2   # jet_pkg derived quantity
        # Field widths read off the DUT so this TB tracks the elaboration.
        self.LINE_W = len(dut.lkup_line_i.value)
        self.SET_W = len(dut.alloc_set_i.value)
        self.WAY_W = len(dut.alloc_victim_way_i.value)
        self.MW = len(dut.alloc_idx_o.value)
        self.SEQ_W = len(dut.alloc_seq_i.value)
        self.FILL_BEATS = len(dut.sn_beats_rcvd_o.value)
        self.SEQ_MASK = (1 << self.SEQ_W) - 1
        assert (1 << self.MW) >= self.MSHR_COUNT > (1 << (self.MW - 1)), (
            f"MSHR_COUNT={self.MSHR_COUNT} inconsistent with MW={self.MW}")
        self.model = MshrModel(self.MSHR_COUNT, self.SETS, self.WAYS)
        self.checks = 0
        self.mismatches = 0
        self.log.info(f"JetMshrTB mshr={self.MSHR_COUNT} sets={self.SETS} "
                      f"ways={self.WAYS} level={self.TEST_LEVEL} seed={self.SEED}")

    # -- the three mandatory methods --------------------------------------
    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock('clk', freq=period_ns, units='ns')
        self._drive_idle()
        self.dut.lkup_line_i.value = 0
        self.dut.sn_line_i.value = 0
        self.dut.cpl_idx_i.value = 0
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
        d.alloc_i.value = 0
        d.alloc_line_i.value = 0
        d.alloc_set_i.value = 0
        d.alloc_cls_i.value = 0
        d.alloc_install_i.value = 0
        d.alloc_victim_way_i.value = 0
        d.alloc_wb_slot_i.value = 0
        d.alloc_wb_valid_i.value = 0
        d.alloc_seq_i.value = 0
        d.merge_i.value = 0
        d.merge_idx_i.value = 0
        d.merge_seq_i.value = 0
        d.beat_i.value = 0
        d.beat_idx_i.value = 0
        d.beat_num_i.value = 0
        d.sn_eff_i.value = 0
        d.sn_eff_idx_i.value = 0
        d.sn_eff_value_i.value = 0
        d.retire_i.value = 0
        d.retire_idx_i.value = 0

    async def _settle(self):
        await Timer(1, units='ns')

    def _score(self, what, got, exp):
        self.checks += 1
        if got != exp:
            self.mismatches += 1
            if self.mismatches <= 20:
                self.log.error(f"{what}: got {got} expected {exp}")

    def _mkline(self, tag, set_):
        return ((tag << self.SET_W) | set_) & ((1 << self.LINE_W) - 1)

    def _fresh_line(self, set_):
        """A line address mapping to set_ that no live entry holds."""
        while True:
            tag = random.randrange(1 << (self.LINE_W - self.SET_W))
            line = self._mkline(tag, set_)
            if self.model.match(line) is None:
                return line

    async def _check_occupancy(self, note):
        await self._settle()
        self._score(f"{note} occupancy_o",
                    int(self.dut.occupancy_o.value), self.model.occupancy())

    async def _check_probes(self, line, note):
        """Point both CAM probes at line and score every probe output.

        The expectation mirrors the alloc-first same-cycle rule: a granted
        in-flight alloc to the probed line is visible even though the entry
        is not yet registered (existing entries win the index)."""
        d = self.dut
        d.lkup_line_i.value = line
        d.sn_line_i.value = line
        await self._settle()
        e = self.model.match(line)
        alloc_hit = (e is None
                     and int(d.alloc_i.value) == 1
                     and int(d.alloc_gnt_o.value) == 1
                     and int(d.alloc_line_i.value) == line)
        exp_match = 1 if (e is not None or alloc_hit) else 0
        self._score(f"{note} lkup_match_o", int(d.lkup_match_o.value), exp_match)
        self._score(f"{note} sn_match_o", int(d.sn_match_o.value), exp_match)
        if e is not None:
            exp_idx = e
            exp_cls = self.model.cls[e]
            exp_beats = self.model.beats[e]
            exp_install = self.model.install[e]
        elif alloc_hit:
            exp_idx = self.model.free_sel()
            exp_cls = int(d.alloc_cls_i.value)
            exp_beats = 0
            exp_install = int(d.alloc_install_i.value)
        else:
            return
        self._score(f"{note} lkup_match_idx_o",
                    int(d.lkup_match_idx_o.value), exp_idx)
        self._score(f"{note} lkup_match_cls_o",
                    int(d.lkup_match_cls_o.value), exp_cls)
        self._score(f"{note} sn_match_idx_o",
                    int(d.sn_match_idx_o.value), exp_idx)
        self._score(f"{note} sn_beats_rcvd_o",
                    int(d.sn_beats_rcvd_o.value), exp_beats)
        self._score(f"{note} sn_install_o",
                    int(d.sn_install_o.value), exp_install)

    async def _check_cpl(self, idx, note):
        """Score the commit read port against the model entry."""
        d = self.dut
        d.cpl_idx_i.value = idx
        await self._settle()
        m = self.model
        self._score(f"{note} cpl_line_o", int(d.cpl_line_o.value), m.line[idx])
        self._score(f"{note} cpl_install_o",
                    int(d.cpl_install_o.value), m.install[idx])
        self._score(f"{note} cpl_pend_eff_o",
                    int(d.cpl_pend_eff_o.value), m.pend_eff[idx])
        self._score(f"{note} cpl_wb_slot_o",
                    int(d.cpl_wb_slot_o.value), m.wb_slot[idx])
        self._score(f"{note} cpl_wb_valid_o",
                    int(d.cpl_wb_valid_o.value), m.wb_valid[idx])
        self._score(f"{note} cpl_merge_count_o",
                    int(d.cpl_merge_count_o.value), len(m.merge[idx]))
        seqs = int(d.cpl_merge_seqs_o.value)
        for k, tag in enumerate(m.merge[idx]):
            got = (seqs >> (k * self.SEQ_W)) & self.SEQ_MASK
            self._score(f"{note} cpl_merge_seqs_o[{k}]", got, tag)

    # -- operations (drive, clock, model) ------------------------------------
    async def _do_alloc(self, line, set_, cls=JET_CLS_RNSD, install=0,
                        victim_way=0, wb_slot=0, wb_valid=0, seq=0,
                        retire_idx=None, note=""):
        """One alloc cycle, optionally paired with a same-cycle retire."""
        d = self.dut
        d.alloc_i.value = 1
        d.alloc_line_i.value = line
        d.alloc_set_i.value = set_
        d.alloc_cls_i.value = cls
        d.alloc_install_i.value = install
        d.alloc_victim_way_i.value = victim_way
        d.alloc_wb_slot_i.value = wb_slot
        d.alloc_wb_valid_i.value = wb_valid
        d.alloc_seq_i.value = seq
        if retire_idx is not None:
            d.retire_i.value = 1
            d.retire_idx_i.value = retire_idx
        await self._settle()
        exp_gnt = 1 if self.model.gnt(set_) else 0
        exp_free = self.model.free_sel()
        self._score(f"{note} alloc_gnt_o", int(d.alloc_gnt_o.value), exp_gnt)
        self._score(f"{note} full_o", int(d.full_o.value),
                    1 if self.model.full() else 0)
        self._score(f"{note} set_full_o", int(d.set_full_o.value),
                    1 if self.model.set_full(set_) else 0)
        if exp_gnt:
            self._score(f"{note} alloc_idx_o",
                        int(d.alloc_idx_o.value), exp_free)
        await RisingEdge(d.clk)
        if exp_gnt:
            self.model.apply_alloc(line, set_, cls, install, victim_way,
                                   wb_slot, wb_valid, seq)
        if retire_idx is not None:
            self.model.apply_retire(retire_idx)
        d.alloc_i.value = 0
        d.retire_i.value = 0
        await self._check_occupancy(note)
        return exp_free if exp_gnt else None

    async def _do_merge(self, idx, seq, note=""):
        d = self.dut
        d.merge_i.value = 1
        d.merge_idx_i.value = idx
        d.merge_seq_i.value = seq
        await RisingEdge(d.clk)
        self.model.apply_merge(idx, seq)
        d.merge_i.value = 0

    async def _do_beat(self, idx, num, note=""):
        d = self.dut
        d.beat_i.value = 1
        d.beat_idx_i.value = idx
        d.beat_num_i.value = num
        await RisingEdge(d.clk)
        self.model.apply_beat(idx, num)
        d.beat_i.value = 0

    async def _do_sn_eff(self, idx, value, note=""):
        d = self.dut
        d.sn_eff_i.value = 1
        d.sn_eff_idx_i.value = idx
        d.sn_eff_value_i.value = value
        await RisingEdge(d.clk)
        self.model.apply_sn_eff(idx, value)
        d.sn_eff_i.value = 0

    async def _do_retire(self, idx, note=""):
        d = self.dut
        d.retire_i.value = 1
        d.retire_idx_i.value = idx
        await RisingEdge(d.clk)
        self.model.apply_retire(idx)
        d.retire_i.value = 0
        await self._check_occupancy(note)

    async def _idle(self):
        await RisingEdge(self.dut.clk)

    async def _drain_all(self):
        for e in range(self.MSHR_COUNT):
            if self.model.valid[e]:
                await self._do_retire(e, note=f"drain[{e}]")
        await self._check_occupancy("drained")

    # -- directed scenarios (MAS ch02_blocks/02) -----------------------------
    async def _scen_alloc_and_match(self):
        """alloc -> both probes see the entry from the alloc cycle."""
        d = self.dut
        line = self._mkline(0x15, 5)
        d.alloc_i.value = 1
        d.alloc_line_i.value = line
        d.alloc_set_i.value = 5
        d.alloc_cls_i.value = JET_CLS_RU
        d.alloc_install_i.value = 1
        d.alloc_victim_way_i.value = 2
        d.alloc_wb_slot_i.value = 1
        d.alloc_wb_valid_i.value = 1
        d.alloc_seq_i.value = 5
        await self._settle()
        self._score("alloc_and_match alloc_gnt_o",
                    int(d.alloc_gnt_o.value), 1)
        self._score("alloc_and_match alloc_idx_o",
                    int(d.alloc_idx_o.value), self.model.free_sel())
        # Same-cycle visibility on BOTH probes (the alloc/match rule).
        await self._check_probes(line, "alloc_and_match alloc-cycle")
        await RisingEdge(d.clk)
        idx = self.model.apply_alloc(line, 5, JET_CLS_RU, 1, 2, 1, 1, 5)
        d.alloc_i.value = 0
        # Registered entry: probes still match, commit port reads it back.
        await self._check_probes(line, "alloc_and_match registered")
        await self._check_probes(self._mkline(0x35, 5),
                                 "alloc_and_match no-match")
        await self._check_cpl(idx, "alloc_and_match")

    async def _scen_full_stall(self):
        """alloc_gnt_o falls at MSHR_COUNT valids; full_o rises."""
        idxs = []
        for i in range(self.MSHR_COUNT):
            idx = await self._do_alloc(self._fresh_line(i), i,
                                       seq=i % self.RSP_DEPTH,
                                       note=f"full_stall[{i}]")
            idxs.append(idx)
        # One more alloc must stall on full (one claim per set, so no
        # set_full interference).
        d = self.dut
        d.alloc_i.value = 1
        d.alloc_line_i.value = self._fresh_line(self.MSHR_COUNT)
        d.alloc_set_i.value = self.MSHR_COUNT
        await self._settle()
        self._score("full_stall full_o", int(d.full_o.value), 1)
        self._score("full_stall set_full_o", int(d.set_full_o.value), 0)
        self._score("full_stall alloc_gnt_o", int(d.alloc_gnt_o.value), 0)
        await RisingEdge(d.clk)   # a stalled alloc cycle changes nothing
        d.alloc_i.value = 0
        await self._check_occupancy("full_stall stalled")
        # Retire one: full drops, the next alloc grants into that slot.
        await self._do_retire(idxs[0], note="full_stall retire")
        await self._do_alloc(self._fresh_line(self.MSHR_COUNT),
                             self.MSHR_COUNT, seq=1, note="full_stall reopen")

    async def _scen_set_claim_cap(self):
        """WAYS allocs to one set grant; the (WAYS+1)-th sees set_full_o
        while an alloc to a different set still grants."""
        await self._drain_all()
        set_a = 3
        idxs = []
        for w in range(self.WAYS):
            idxs.append(await self._do_alloc(self._fresh_line(set_a), set_a,
                                             seq=w, note=f"set_claim_cap[{w}]"))
        d = self.dut
        d.alloc_i.value = 1
        d.alloc_line_i.value = self._fresh_line(set_a)
        d.alloc_set_i.value = set_a
        await self._settle()
        self._score("set_claim_cap set_full_o", int(d.set_full_o.value), 1)
        self._score("set_claim_cap full_o", int(d.full_o.value), 0)
        self._score("set_claim_cap alloc_gnt_o", int(d.alloc_gnt_o.value), 0)
        d.alloc_i.value = 0
        # A different set is unaffected.
        await self._do_alloc(self._fresh_line(set_a + 1), set_a + 1,
                             seq=1, note="set_claim_cap other-set")
        # Retire one claim holder: the capped set grants again.
        await self._do_retire(idxs[0], note="set_claim_cap retire")
        await self._do_alloc(self._fresh_line(set_a), set_a,
                             seq=2, note="set_claim_cap reopen")

    async def _scen_set_claim_same_cycle(self):
        """alloc + retire to the SAME set in one cycle nets the per-set
        claim counter (Review Focus 1)."""
        await self._drain_all()
        set_a = 7
        e0 = await self._do_alloc(self._fresh_line(set_a), set_a,
                                  seq=0, note="same_cycle e0")
        await self._do_alloc(self._fresh_line(set_a), set_a,
                             seq=1, note="same_cycle e1")
        # claims[set_a] == 2; a paired alloc+retire must leave it at 2.
        await self._do_alloc(self._fresh_line(set_a), set_a, seq=2,
                             retire_idx=e0, note="same_cycle paired")
        self._score("same_cycle occupancy net",
                    self.model.occupancy(), 2)
        # Exactly WAYS-2 more allocs to set_a grant before set_full rises;
        # a wrong net (+1 or -1) moves this boundary.
        for w in range(self.WAYS - 2):
            await self._do_alloc(self._fresh_line(set_a), set_a,
                                 seq=(3 + w) % self.RSP_DEPTH,
                                 note=f"same_cycle fill[{w}]")
        d = self.dut
        d.alloc_i.value = 1
        d.alloc_line_i.value = self._fresh_line(set_a)
        d.alloc_set_i.value = set_a
        await self._settle()
        self._score("same_cycle boundary set_full_o",
                    int(d.set_full_o.value), 1)
        self._score("same_cycle boundary alloc_gnt_o",
                    int(d.alloc_gnt_o.value), 0)
        d.alloc_i.value = 0

    async def _scen_merge_appends(self):
        """Merge tags accumulate in append order behind the allocator's."""
        await self._drain_all()
        idx = await self._do_alloc(self._fresh_line(9), 9, seq=2,
                                   note="merge alloc")
        for tag in (7, 9, 1):
            await self._do_merge(idx, tag)
        await self._check_cpl(idx, "merge_appends")

    async def _scen_beat_marks(self):
        """sn_beats_rcvd_o tracks beat_i (the PF_GUARD bitmask)."""
        await self._drain_all()
        idx = await self._do_alloc(self._fresh_line(11), 11, seq=3,
                                   note="beat alloc")
        line = self.model.line[idx]
        await self._check_probes(line, "beat_marks empty")
        for b in (3, 0, self.FILL_BEATS - 1):
            await self._do_beat(idx, b)
            await self._check_probes(line, f"beat_marks[{b}]")

    async def _scen_pend_eff_records(self):
        """sn_eff_i records the deferred snoop effect; cpl reads it back."""
        await self._drain_all()
        idx = await self._do_alloc(self._fresh_line(13), 13, install=1,
                                   seq=4, note="pend alloc")
        await self._check_cpl(idx, "pend_eff none")
        await self._do_sn_eff(idx, JET_PEND_DOWNGRADE_S)
        await self._check_cpl(idx, "pend_eff downgrade")
        await self._do_sn_eff(idx, JET_PEND_INVALIDATE_I)
        await self._check_cpl(idx, "pend_eff invalidate")
        await self._do_sn_eff(idx, JET_PEND_NONE)
        await self._check_cpl(idx, "pend_eff cleared")

    async def _scen_retire_frees(self):
        """Retire frees the entry, the way claim, and occupancy."""
        await self._drain_all()
        a = await self._do_alloc(self._fresh_line(20), 20, install=1,
                                 wb_slot=1, wb_valid=1, seq=0,
                                 note="retire a")
        b = await self._do_alloc(self._fresh_line(21), 21, seq=1,
                                 note="retire b")
        c = await self._do_alloc(self._fresh_line(20), 20, seq=2,
                                 note="retire c")
        self._score("retire_frees occ3", self.model.occupancy(), 3)
        line_b = self.model.line[b]
        line_a = self.model.line[a]
        line_c = self.model.line[c]
        await self._check_cpl(a, "retire_frees wb fields")
        await self._do_retire(b, note="retire_frees b")
        await self._check_probes(line_b, "retire_frees b gone")
        await self._check_probes(line_a, "retire_frees a live")
        await self._check_probes(line_c, "retire_frees c live")
        # Retiring a releases one set-20 claim: exactly WAYS-1 more allocs
        # to set 20 grant before the cap (c still holds one).
        await self._do_retire(a, note="retire_frees a")
        for w in range(self.WAYS - 1):
            await self._do_alloc(self._fresh_line(20), 20,
                                 seq=(3 + w) % self.RSP_DEPTH,
                                 note=f"retire_frees refill[{w}]")
        d = self.dut
        d.alloc_i.value = 1
        d.alloc_line_i.value = self._fresh_line(20)
        d.alloc_set_i.value = 20
        await self._settle()
        self._score("retire_frees cap set_full_o", int(d.set_full_o.value), 1)
        self._score("retire_frees cap alloc_gnt_o",
                    int(d.alloc_gnt_o.value), 0)
        d.alloc_i.value = 0

    async def _scen_occupancy_gauge(self):
        """occupancy_o tracks the valid-entry count across alloc/retire."""
        await self._drain_all()
        idxs = []
        for i in range(4):
            idxs.append(await self._do_alloc(self._fresh_line(30 + i),
                                             30 + i, seq=i,
                                             note=f"occ alloc[{i}]"))
        await self._do_retire(idxs[1], note="occ retire1")
        await self._do_retire(idxs[3], note="occ retire3")
        idxs.append(await self._do_alloc(self._fresh_line(34), 34, seq=4,
                                         note="occ realloc"))
        for e in range(self.MSHR_COUNT):
            if self.model.valid[e]:
                await self._do_retire(e, note=f"occ drain[{e}]")

    # -- random phase ---------------------------------------------------------
    async def _random_phase(self, n_ops):
        self.log.info(f"jet_mshr: {n_ops} random ops at {self.TEST_LEVEL}")
        for i in range(n_ops):
            m = self.model
            valids = [e for e in range(self.MSHR_COUNT) if m.valid[e]]
            r = random.random()
            if r < 0.30:
                set_ = random.randrange(16)   # narrow window: set pressure
                pair = valids and random.random() < 0.2
                await self._do_alloc(
                    self._fresh_line(set_), set_,
                    cls=random.randrange(2),
                    install=random.randrange(2),
                    victim_way=random.randrange(self.WAYS),
                    wb_slot=random.randrange(2),
                    wb_valid=random.randrange(2),
                    seq=random.randrange(self.RSP_DEPTH),
                    retire_idx=random.choice(valids) if pair else None,
                    note=f"rnd{i} alloc")
            elif r < 0.45:
                cands = [e for e in valids if len(m.merge[e]) < self.MSHR_COUNT]
                if cands:
                    await self._do_merge(random.choice(cands),
                                         random.randrange(self.RSP_DEPTH))
                else:
                    await self._idle()
            elif r < 0.60 and valids:
                await self._do_beat(random.choice(valids),
                                    random.randrange(self.FILL_BEATS))
            elif r < 0.70 and valids:
                await self._do_sn_eff(random.choice(valids),
                                      random.randrange(4))
            elif r < 0.85 and valids:
                await self._do_retire(random.choice(valids),
                                      note=f"rnd{i} retire")
            else:
                await self._idle()
            if random.random() < 0.7:
                live = [m.line[e] for e in range(self.MSHR_COUNT)
                        if m.valid[e]]
                if live and random.random() < 0.6:
                    await self._check_probes(random.choice(live),
                                             f"rnd{i} live")
                else:
                    await self._check_probes(
                        random.randrange(1 << self.LINE_W), f"rnd{i} dead")
            valids = [e for e in range(self.MSHR_COUNT) if m.valid[e]]
            if valids and random.random() < 0.3:
                await self._check_cpl(random.choice(valids), f"rnd{i} cpl")

    # -- test -----------------------------------------------------------------
    async def run(self) -> bool:
        await self._scen_alloc_and_match()
        await self._scen_full_stall()
        await self._scen_set_claim_cap()
        await self._scen_set_claim_same_cycle()
        await self._scen_merge_appends()
        await self._scen_beat_marks()
        await self._scen_pend_eff_records()
        await self._scen_retire_frees()
        await self._scen_occupancy_gauge()
        await self._drain_all()
        await self._random_phase(self.OP_COUNTS[self.TEST_LEVEL])
        await self._drain_all()
        return self.mismatches == 0

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches}
