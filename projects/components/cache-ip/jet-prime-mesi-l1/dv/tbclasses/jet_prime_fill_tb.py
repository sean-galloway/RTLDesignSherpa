"""
jet_prime_fill testbench -- the multi-outstanding AXI4 read fill engine
(jet-prime TASK-001 step 2) against the house AXI4 slave read responder.

The DUT is the bare engine: launches come in on the jet_prime_control seam
(start held until accept, carrying the entry index and its claimed
set/way), beats and completions come out on the plane seam, and the
fub_axi_* AR/R pins close on the framework's AXI4 slave read BFM backed by
a MemoryModel (in-order by default; out-of-order and interleaved R at the
deeper levels).  The TB scores, per launch:

  * the AR: ARID = the slot (entry index; MSHR_COUNT for the no-data
    CLEAN_UNIQUE), line-aligned ARADDR, ARLEN = FILL_BEATS-1 (0 for a CU),
    ARSIZE = the bus, INCR;
  * the beats: exactly FILL_BEATS for a data fill in order 0..FILL_BEATS-1,
    each with the launch's entry index, set and way and the memory image
    of that beat; none for a CU; beats of different slots may interleave;
  * the done: with the slot's last beat (the CU with its single no-data
    response), naming the entry and class, PassDirty 0 (plain AXI4
    memory);
  * concurrency: launches accept while earlier fills are still in flight
    up to FILL_INFLIGHT, and never past it (a FILL_INFLIGHT=1 cell holds
    the second launch until the first done -- jet's single-outstanding
    engine, the pair rig's setting until step 3);
  * reuse: a slot relaunches after its done.

Author: RTL Design Sherpa
Created: 2026-11-15
"""

import os
import random
from collections import deque

import cocotb
from cocotb.triggers import RisingEdge, Timer

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.axi4.axi4_factories import create_axi4_slave_rd

# jet_prime_pkg encodings (ints; the TB never imports the SV package)
CLS_RNSD = 0
CLS_RU = 1
CLS_CU = 2
AXBURST_INCR = 1


class JetFillTB(TBBase):
    """Pin-level TB for jet_prime_fill with the AXI4 slave read BFM."""

    RANDOM_FILLS = {'gate': 40, 'func': 300, 'full': 1500}

    # responder timing profiles (the fill/drain unit suite's set)
    PROFILES = {
        'fast':   {'ready': ([(0, 0)], [1.0]),
                   'resp':  ([(0, 0)], [1.0])},
        'normal': {'ready': ([(0, 2), (3, 5)], [0.7, 0.3]),
                   'resp':  ([(0, 2), (3, 6)], [0.6, 0.4])},
        'slow':   {'ready': ([(1, 4), (5, 10)], [0.6, 0.4]),
                   'resp':  ([(2, 6), (7, 12)], [0.5, 0.5])},
    }

    def __init__(self, dut, **kwargs):
        super().__init__(dut, **kwargs)
        self.MSHR_COUNT = self.convert_to_int(os.environ.get('MSHR_COUNT', '8'))
        self.FILL_INFLIGHT = self.convert_to_int(
            os.environ.get('FILL_INFLIGHT', str(self.MSHR_COUNT + 1)))
        self.SETS = self.convert_to_int(os.environ.get('SETS', '128'))
        self.WAYS = self.convert_to_int(os.environ.get('WAYS', '4'))
        self.LINE_BYTES = self.convert_to_int(os.environ.get('LINE_BYTES', '64'))
        self.BUS_WIDTH = self.convert_to_int(os.environ.get('BUS_WIDTH', '64'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.SEED)

        self.STRB_W = self.BUS_WIDTH // 8
        self.FILL_BEATS = self.LINE_BYTES // self.STRB_W
        self.OFFSET_BITS = (self.LINE_BYTES - 1).bit_length()
        self.SLOTS = self.MSHR_COUNT + 1
        self.CU_SLOT = self.MSHR_COUNT
        # the responder's memory: 64K beats (512 KB at 8 B/beat); fills
        # address the low 2^19 bytes
        self.MEM_BYTES = (1 << 16) * self.STRB_W
        self.memory_model = MemoryModel(num_lines=1 << 16,
                                        bytes_per_line=self.STRB_W,
                                        log=self.log)
        self.ooo = self.TEST_LEVEL in ('func', 'full')
        rd = create_axi4_slave_rd(
            dut=dut, clock=dut.clk, prefix='fub_axi', log=self.log,
            id_width=8, addr_width=32, data_width=self.BUS_WIDTH,
            user_width=1, memory_model=self.memory_model,
            enable_ooo=self.ooo,
            interleave_r=(self.TEST_LEVEL == 'full'),
            ooo_config={'mode': 'random', 'reorder_probability': 0.5,
                        'min_delay_cycles': 1, 'max_delay_cycles': 24,
                        'pattern': None})
        self.ar_slave = rd['AR']
        self.r_master = rd['R']
        self.set_profile('fast')

        self.checks = 0
        self.mismatches = 0
        self.scenarios = {}
        self.cyc = 0

        # per-slot flight records (the TB's model of the engine)
        self.slot = {}          # slot -> dict (in flight)
        self.ar_seen = deque()  # AR handshakes not yet matched to a slot
        self.done_log = []      # (cyc, slot, cls, pd)
        self.max_inflight = 0
        self.ooo_dones = 0      # dones that overtook an earlier-accepted fill
        self.accept_cycles = {}  # slot -> cycle of the last accept

    # ------------------------------------------------------------------
    # infrastructure
    # ------------------------------------------------------------------
    def _score(self, what, got, exp):
        self.checks += 1
        if got != exp:
            self.mismatches += 1
            if self.mismatches <= 30:
                self.log.error(f"CHECK FAIL: {what}: got {got!r} expected {exp!r}")

    def set_profile(self, name):
        cfg = self.PROFILES[name]
        self.ar_slave.set_randomizer(FlexRandomizer({'ready_delay': cfg['ready']}))
        self.r_master.set_randomizer(FlexRandomizer({'valid_delay': cfg['resp']}))

    async def _drive_pt(self):
        """This cycle's drive point: shortly after the rising edge."""
        await RisingEdge(self.dut.clk)
        await Timer(200, units='ps')

    async def _sample_pt(self):
        """This cycle's sample point: late in the cycle, every BFM drive
        landed (the monitors sample here; the drivers drive at _drive_pt)."""
        await Timer(8800, units='ps')

    async def _cycle(self):
        await self._drive_pt()
        await self._sample_pt()

    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock('clk', freq=period_ns, units='ns')
        d = self.dut
        d.fill_start_i.value = 0
        d.fill_addr_i.value = 0
        d.fill_cls_i.value = 0
        d.fill_idx_i.value = 0
        d.fill_set_i.value = 0
        d.fill_way_i.value = 0
        d.cap_hold_i.value = 0
        d.cap_set_i.value = 0
        d.cap_way_i.value = 0
        d.rst_n.value = 0
        await self.wait_clocks('clk', 5)
        d.rst_n.value = 1
        cocotb.start_soon(self._monitor())
        await self.wait_clocks('clk', 2)

    # ------------------------------------------------------------------
    # memory image
    # ------------------------------------------------------------------
    def _line_addr(self, addr):
        return addr & ~(self.LINE_BYTES - 1)

    def _mem_beat(self, line_addr, b):
        data = self.memory_model.read(line_addr + b * self.STRB_W, self.STRB_W)
        return int.from_bytes(bytes(data), 'little')

    def _fill_line(self, line_addr):
        for b in range(self.FILL_BEATS):
            val = random.getrandbits(self.BUS_WIDTH)
            self.memory_model.write(line_addr + b * self.STRB_W,
                                    bytearray(val.to_bytes(self.STRB_W, 'little')))

    def _rand_line(self):
        """A random line no fill in flight is reading (a relaunch to a line
        still being fetched would rewrite the memory image under it)."""
        busy = {r['line'] for r in self.slot.values()}
        while True:
            line = self._line_addr(random.randrange(self.MEM_BYTES))
            if line not in busy:
                return line

    # ------------------------------------------------------------------
    # monitor: AR handshakes, beats, dones, the in-flight gauge
    # ------------------------------------------------------------------
    async def _monitor(self):
        d = self.dut
        while True:
            await self._drive_pt()
            await self._sample_pt()
            self.cyc += 1
            inflight = int(d.r_inflight.value)
            idle_before = not self.slot
            self.max_inflight = max(self.max_inflight, inflight)
            self._score("in-flight count never over FILL_INFLIGHT",
                        inflight <= self.FILL_INFLIGHT, True)
            if int(d.fill_accept_o.value):
                self._score("accept only with a launch presented",
                            int(d.fill_start_i.value), 1)
                self._score("accept only under the in-flight cap",
                            inflight < self.FILL_INFLIGHT, True)
            # AR handshake
            if int(d.fub_axi_arvalid.value) and int(d.fub_axi_arready.value):
                arid = int(d.fub_axi_arid.value)
                rec = self.slot.get(arid)
                if rec is None:
                    self._score("AR for a slot not in flight", arid, None)
                else:
                    self._score(f"slot {arid}: one AR per launch", rec['ar'], False)
                    rec['ar'] = True
                    self._score(f"slot {arid}: ARADDR is the line",
                                int(d.fub_axi_araddr.value), rec['line'])
                    self._score(f"slot {arid}: ARLEN",
                                int(d.fub_axi_arlen.value),
                                0 if rec['cls'] == CLS_CU else self.FILL_BEATS - 1)
                    self._score(f"slot {arid}: ARSIZE",
                                int(d.fub_axi_arsize.value),
                                self.STRB_W.bit_length() - 1)
                    self._score(f"slot {arid}: ARBURST INCR",
                                int(d.fub_axi_arburst.value), AXBURST_INCR)
            # beat
            beat = int(d.fill_beat_valid_o.value)
            if beat:
                idx = int(d.fill_beat_idx_o.value)
                if int(d.cap_hold_i.value) \
                        and int(d.fill_beat_set_o.value) == int(d.cap_set_i.value) \
                        and int(d.fill_beat_way_o.value) == int(d.cap_way_i.value):
                    self._score("beat into the way under capture hold", 1, 0)
                rec = self.slot.get(idx)
                if rec is None or rec['cls'] == CLS_CU:
                    self._score("beat for a slot not in a data fill", idx, None)
                else:
                    self._score(f"slot {idx}: beat after its AR", rec['ar'], True)
                    num = int(d.fill_beat_num_o.value)
                    self._score(f"slot {idx}: beat order", num, rec['beats'])
                    self._score(f"slot {idx}: beat set",
                                int(d.fill_beat_set_o.value), rec['set'])
                    self._score(f"slot {idx}: beat way",
                                int(d.fill_beat_way_o.value), rec['way'])
                    self._score(f"slot {idx}: beat {num} data",
                                int(d.fill_beat_data_o.value),
                                self._mem_beat(rec['line'], num))
                    rec['beats'] += 1
            # done
            if int(d.fill_done_o.value):
                cls = int(d.fill_done_cls_o.value)
                idx = int(d.fill_done_idx_o.value)
                slot = self.CU_SLOT if cls == CLS_CU else idx
                rec = self.slot.get(slot)
                if rec is None:
                    self._score("done for a slot not in flight", slot, None)
                else:
                    self._score(f"slot {slot}: done class", cls, rec['cls'])
                    self._score(f"slot {slot}: done after its AR", rec['ar'], True)
                    exp_beats = 0 if cls == CLS_CU else self.FILL_BEATS
                    self._score(f"slot {slot}: done with the last beat",
                                rec['beats'], exp_beats)
                    if cls != CLS_CU:
                        self._score(f"slot {slot}: done rides the last beat",
                                    beat and int(d.fill_beat_idx_o.value) == idx,
                                    True)
                    self._score(f"slot {slot}: PassDirty (plain AXI4 memory)",
                                int(d.fill_done_pd_o.value), 0)
                    rec['done_cyc'] = self.cyc
                    self.done_log.append((self.cyc, slot, cls))
                    if any(r['accept_cyc'] < rec['accept_cyc']
                           for k, r in self.slot.items() if k != slot):
                        self.ooo_dones += 1
                    del self.slot[slot]
            # busy is registered state: it drops the cycle after the last
            # done, so judge it only in a cycle that began idle
            if idle_before and not self.slot:
                self._score("busy drops with nothing in flight",
                            int(d.fill_busy_o.value) == 0
                            or int(d.fill_accept_o.value) == 1, True)

    # ------------------------------------------------------------------
    # launch driver
    # ------------------------------------------------------------------
    async def launch(self, line, cls, idx=0, set_idx=0, way=0, label='',
                     max_wait=2000):
        """Present one launch (held until accept) and return the accept
        cycle.  The slot record opens AT the accept (the sample point of
        the accept cycle sees the engine's state before the edge)."""
        d = self.dut
        slot = self.CU_SLOT if cls == CLS_CU else idx
        assert slot not in self.slot, f"{label}: slot {slot} already in flight"
        await self._drive_pt()
        d.fill_start_i.value = 1
        d.fill_addr_i.value = line
        d.fill_cls_i.value = cls
        d.fill_idx_i.value = idx
        d.fill_set_i.value = set_idx
        d.fill_way_i.value = way
        start = self.cyc
        waited = 0
        while True:
            await self._sample_pt()
            if int(d.fill_accept_o.value):
                acc = self.cyc + 1
                self.slot[slot] = {'line': line, 'cls': cls, 'idx': idx,
                                   'set': set_idx, 'way': way, 'ar': False,
                                   'beats': 0, 'accept_cyc': acc,
                                   'done_cyc': None, 'label': label}
                self.accept_cycles[slot] = acc
                break
            waited += 1
            if waited > max_wait:
                raise RuntimeError(f"{label}: launch never accepted")
            await self._drive_pt()
        await self._drive_pt()
        d.fill_start_i.value = 0
        return acc, waited

    async def wait_done(self, slot, label='', max_wait=4000):
        for _ in range(max_wait):
            if slot not in self.slot:
                return
            await self._cycle()
        raise RuntimeError(f"{label}: slot {slot} never completed")

    async def wait_idle(self, max_wait=6000):
        for _ in range(max_wait):
            if not self.slot and not int(self.dut.fill_busy_o.value):
                return
            await self._cycle()
        raise RuntimeError("engine never went idle")

    # ------------------------------------------------------------------
    # scenarios
    # ------------------------------------------------------------------
    async def _scen_single_fill(self):
        """single_fill: one RNSD launch is accepted the cycle it is
        presented, issues one line burst and lands FILL_BEATS beats in
        order with the memory image, done with the last beat."""
        line = self._rand_line()
        self._fill_line(line)
        acc, waited = await self.launch(line, CLS_RNSD, idx=3, set_idx=17,
                                        way=2, label='single')
        self._score("single: accepted at once", waited, 0)
        await self.wait_done(3, 'single')
        self._score("single: one done", len(self.done_log), 1)
        await self.wait_idle()
        self.scenarios['single_fill'] = True

    async def _scen_cu_no_data(self):
        """cu_no_data: a CLEAN_UNIQUE launch issues a single-beat
        (ARLEN=0) read on the upgrade slot's ID, presents no beat, and
        completes with class CU on its one response."""
        line = self._rand_line()
        n0 = len(self.done_log)
        await self.launch(line, CLS_CU, label='cu')
        await self.wait_done(self.CU_SLOT, 'cu')
        self._score("cu: one done", len(self.done_log) - n0, 1)
        self._score("cu: done on the upgrade slot",
                    self.done_log[-1][1:], (self.CU_SLOT, CLS_CU))
        await self.wait_idle()
        self.scenarios['cu_no_data'] = True

    async def _scen_concurrent(self):
        """concurrent_fills: K data fills to distinct slots launch back to
        back with a slow responder.  With FILL_INFLIGHT > 1 every launch
        is accepted before the first done and the in-flight gauge reaches
        min(K, FILL_INFLIGHT); with FILL_INFLIGHT = 1 the second launch
        waits for the first done (jet's single-outstanding engine).  All
        bursts are scored by the monitor whatever their order."""
        K = min(4, self.MSHR_COUNT)
        self.set_profile('slow')
        n0 = len(self.done_log)
        self.max_inflight = 0
        first_acc = None
        accs = []
        for i in range(K):
            line = self._rand_line()
            self._fill_line(line)
            acc, waited = await self.launch(line, CLS_RU if i % 2 else CLS_RNSD,
                                            idx=i, set_idx=i + 1, way=i % self.WAYS,
                                            label=f'conc{i}')
            accs.append(acc)
            if first_acc is None:
                first_acc = acc
        for i in range(K):
            await self.wait_done(i, f'conc{i}')
        self._score("conc: every fill done", len(self.done_log) - n0, K)
        dones = sorted(c for c, s, _ in self.done_log[n0:])
        if self.FILL_INFLIGHT >= K:
            self._score("conc: every launch accepted before the first done",
                        accs[-1] < dones[0], True)
            self._score("conc: in-flight gauge reached K",
                        self.max_inflight, K)
        elif self.FILL_INFLIGHT == 1:
            self._score("conc: second launch held until the first done",
                        accs[1] > dones[0], True)
            self._score("conc: in-flight gauge capped at 1",
                        self.max_inflight, 1)
        else:
            self._score("conc: in-flight gauge reached the cap",
                        self.max_inflight, self.FILL_INFLIGHT)
        self.set_profile('fast')
        await self.wait_idle()
        self.scenarios['concurrent_fills'] = True

    async def _scen_slot_reuse(self):
        """slot_reuse: a slot relaunches right after its done (the entry
        retired and reallocated) and the new burst is scored on its own
        line, set and way."""
        for rep in range(2):
            line = self._rand_line()
            self._fill_line(line)
            await self.launch(line, CLS_RNSD, idx=5, set_idx=40 + rep,
                              way=rep, label=f'reuse{rep}')
            await self.wait_done(5, f'reuse{rep}')
        await self.wait_idle()
        self.scenarios['slot_reuse'] = True

    async def _scen_capture_hold(self):
        """capture_hold: the capture contract at the beat.  A fill to
        (set 5, way 1) is launched with cap_hold_i raised for that very
        (set, way) before its burst returns; its beats wait at the
        staging-queue head -- none presented, the burst backpressured once
        the queue fills -- while a second fill to another way launched
        behind it waits too when its burst queued behind the held one (the
        in-order responder: the hold is head-of-line, by design, bounded
        by the capture) and completes under the hold when the responder
        returned it first (out of order: the hold is per (set, way)).
        Dropping the hold releases the held fill; a hold on a different
        (set, way) holds nothing."""
        d = self.dut
        a = self._rand_line(); self._fill_line(a)
        b = self._rand_line()
        while b == a:
            b = self._rand_line()
        self._fill_line(b)
        await self.launch(a, CLS_RNSD, idx=1, set_idx=5, way=1, label='hold-a')
        await self._drive_pt()
        d.cap_hold_i.value = 1
        d.cap_set_i.value = 5
        d.cap_way_i.value = 1
        # the second fill behind the held head needs in-flight room: at
        # FILL_INFLIGHT = 1 the engine (correctly) holds its launch until
        # the held fill completes, so the cell holds one fill only
        two = self.FILL_INFLIGHT > 1
        if two:
            await self.launch(b, CLS_RNSD, idx=2, set_idx=9, way=0, label='hold-b')
        # let the burst(s) arrive and sit: no beat of either slot, the
        # held slot stays in flight
        for _ in range(60):
            await self._cycle()
        # the held slot presents no beat; the one behind it only when its
        # burst queued behind the held one (in order) -- out of order it may
        # be mid-burst at this sample, legitimately (the hold is per
        # (set, way)), so its partial count is not a violation
        self.log.info(f"hold: beats so far slot1="
                      f"{self.slot[1]['beats'] if 1 in self.slot else '-'} "
                      f"slot2={self.slot[2]['beats'] if 2 in self.slot else '-'} "
                      f"ooo={self.ooo}")
        self._score("hold: no beat of the held slot presented while the hold is up",
                    self.slot[1]['beats'] if 1 in self.slot else 0, 0)
        if two and not self.ooo:
            self._score("hold: no beat of the slot behind the held head (in order)",
                        self.slot[2]['beats'] if 2 in self.slot else 0, 0)
        self._score("hold: slot 1 still in flight", 1 in self.slot, True)
        # the second fill waits behind the held head only when its burst
        # queued behind it -- the in-order responder (gate); out of order
        # (func/full) it may have returned first and completed under the
        # hold, which is the point: the hold is per (set, way), not global
        if two and not self.ooo:
            self._score("hold: slot 2 (behind the held head) still in flight",
                        2 in self.slot, True)
        self._score("hold: the engine reports busy", int(d.fill_busy_o.value), 1)
        # release: the held slot completes (first, with the one behind it
        # next, when the responder kept the order)
        await self._drive_pt()
        d.cap_hold_i.value = 0
        rel = self.cyc
        await self.wait_done(1, 'hold-a')
        done1 = [c for c, sl, *_ in self.done_log if sl == 1]
        self._score("hold: the held slot completes after the release",
                    bool(done1) and done1[-1] >= rel, True)
        if two:
            await self.wait_done(2, 'hold-b')
            if not self.ooo:
                self._score("hold: the held slot completes first, the one behind it next",
                            [x[1] for x in self.done_log[-2:]], [1, 2])
        await self.wait_idle()
        # a hold on an unrelated (set, way) holds nothing
        c = self._rand_line(); self._fill_line(c)
        await self._drive_pt()
        d.cap_hold_i.value = 1
        d.cap_set_i.value = 5
        d.cap_way_i.value = 0
        acc, _ = await self.launch(c, CLS_RNSD, idx=3, set_idx=5, way=1, label='hold-c')
        await self.wait_done(3, 'hold-c', max_wait=400)
        self._score("hold on another way: the fill completes under it",
                    3 in self.slot, False)
        await self._drive_pt()
        d.cap_hold_i.value = 0
        await self.wait_idle()
        self.scenarios['capture_hold'] = True

    async def _scen_random(self):
        """random_fills: random launches to any free slot (10 % CU on the
        upgrade slot), random lines, the responder profile rotating; at
        func/full the responder completes out of order (and at full
        interleaves R beats of different IDs).  Everything is scored by
        the monitor; the phase ends with the engine idle and every launch
        done exactly once."""
        n = self.RANDOM_FILLS.get(self.TEST_LEVEL, 40)
        n0 = len(self.done_log)
        launched = 0
        profiles = ['fast', 'normal', 'slow']
        while launched < n:
            if launched % 25 == 0:
                self.set_profile(random.choice(profiles))
                self.mark_progress(f"random fills {launched}/{n}")
            free = [s for s in range(self.MSHR_COUNT) if s not in self.slot]
            cu_free = self.CU_SLOT not in self.slot
            if not free and not cu_free:
                await self._cycle()
                continue
            if cu_free and (not free or random.random() < 0.1):
                await self.launch(self._rand_line(), CLS_CU, label=f'rnd{launched}')
            else:
                idx = random.choice(free)
                line = self._rand_line()
                self._fill_line(line)
                await self.launch(line, random.choice((CLS_RNSD, CLS_RU)), idx=idx,
                                  set_idx=random.randrange(self.SETS),
                                  way=random.randrange(self.WAYS),
                                  label=f'rnd{launched}')
            launched += 1
            for _ in range(random.choice((0, 0, 1, 3))):
                await self._cycle()
        await self.wait_idle()
        self._score("random: every launch done exactly once",
                    len(self.done_log) - n0, n)
        if self.ooo and self.FILL_INFLIGHT > 1:
            # the responder was told to reorder: the engine must have
            # seen (and demuxed) completions out of accept order
            self._score("random: out-of-order completions exercised",
                        self.ooo_dones > 0, True)
        self.set_profile('fast')
        self.scenarios['random_fills'] = True

    async def run(self) -> bool:
        await self._scen_single_fill()
        await self._scen_cu_no_data()
        await self._scen_concurrent()
        await self._scen_slot_reuse()
        await self._scen_capture_hold()
        await self._scen_random()
        missing = [k for k, v in self.scenarios.items() if not v]
        self._score("all scenarios ran", len(missing), 0)
        self._score("final: nothing in flight", len(self.slot), 0)
        self.log.info(f"jet_prime_fill: {self.checks} checks, "
                      f"{self.mismatches} mismatches, max in-flight "
                      f"{self.max_inflight} (cap {self.FILL_INFLIGHT}), "
                      f"{self.ooo_dones} out-of-order completions")
        return self.mismatches == 0

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches,
                'scenarios': sorted(self.scenarios),
                'max_inflight': self.max_inflight,
                'ooo_dones': self.ooo_dones}
