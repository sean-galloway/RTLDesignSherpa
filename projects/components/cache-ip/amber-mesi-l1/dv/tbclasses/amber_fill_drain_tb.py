"""
amber_fill / amber_drain testbench

AXI4 master-side sequencing engines (Task 6, MAS ch02_blocks/06 +
ch03_interfaces/02) against the house axi4_master_rd / axi4_master_wr
wrappers, with the house CocoTBFramework AXI4 slave responders
(create_axi4_slave_rd/wr + a shared MemoryModel) closing the loop at the
wrappers' m_axi pins. DECISION D3: the engines drive the wrappers' fub_axi_*
upstream side; the wrapper skids are in the loop, never re-implemented.
DECISION D-6: amber_fill stages R beats in a gaxi_fifo_sync (DEPTH=4);
amber_drain forwards the latched victim beats directly (AW/W/B skids inside
the wrapper absorb). The MAS ch03/02 waveform is scored at the wrapper's
fub pins (hierarchical taps, the same sanctioned pattern as the control
suite's u_victim taps); the protocol-visible contract is scored at m_axi.

Levels (TEST_LEVEL):
  gate  -- FillBurstWaveform (READ_SHARED), UpgradeNoFetch (CLEAN_UNIQUE,
           no AR at all), DrainBurstWaveform
  func  -- + ReadUniqueData, RBackpressureIntegrity, WBackpressurePayloadHold
           (+AW/AR payload-hold laws), BResponseDelay, SingleOutstanding
           streams, WritebackRoundTrip, DrainLatchesPayload
  full  -- + FillRandomSoak / DrainRandomSoak: SEED-pinned randomized
           concurrent streams (independent AXI channels, disjoint address
           ranges) with mid-stream responder-profile switches and a final
           MemoryModel audit in both directions

Author: RTL Design Sherpa
Created: 2026-10-08
"""

import os
import random

import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer

from TBClasses.shared.tbbase import TBBase

from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.axi4.axi4_factories import (
    create_axi4_slave_rd,
    create_axi4_slave_wr,
)

# amber_pkg ace_req_t encodings
ACE_READ_SHARED, ACE_READ_UNIQUE, ACE_CLEAN_UNIQUE = 0, 1, 2
ACE_NAMES = {ACE_READ_SHARED: 'READ_SHARED', ACE_READ_UNIQUE: 'READ_UNIQUE',
             ACE_CLEAN_UNIQUE: 'CLEAN_UNIQUE'}

# AXI encodings checked at the pins
AXBURST_INCR = 0b01
BRESP_OKAY = 0b00


class AmberFillDrainTB(TBBase):
    """Scores amber_fill / amber_drain against the MAS ch03/02 contract."""

    FULL_TXN = {'gate': 0, 'func': 0, 'full': 100}
    TIMEOUT_CYCLES = 2000

    # responder timing profiles: 'ready' shapes the slave-side ready_delay
    # (AR/AW/W backpressure), 'resp' shapes the master-side valid_delay
    # (R gaps / B latency), read fresh per application by each channel
    PROFILES = {
        'fast':   {'ready': ([(0, 0)], [1.0]),
                   'resp':  ([(0, 0)], [1.0])},
        'normal': {'ready': ([(0, 2), (3, 5)], [0.7, 0.3]),
                   'resp':  ([(0, 2), (3, 6)], [0.6, 0.4])},
        'slow':   {'ready': ([(1, 4), (5, 10)], [0.6, 0.4]),
                   'resp':  ([(2, 6), (7, 12)], [0.5, 0.5])},
    }

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        random.seed(self.SEED)

        # geometry (house convention: the grid varies SETS/WAYS only; the
        # line/bus stay at the pkg defaults, so FILL_BEATS is 8 in every cell)
        self.SETS = int(os.environ.get('SETS', '128'))
        self.WAYS = int(os.environ.get('WAYS', '4'))
        self.ADDR_WIDTH = 32
        self.LINE_BYTES = 64
        self.BUS_WIDTH = 64
        self.STRB_W = 8
        self.FILL_BEATS = self.LINE_BYTES // self.STRB_W
        self.BEAT_BITS = (self.FILL_BEATS - 1).bit_length()
        self.AXSIZE = self.STRB_W.bit_length() - 1
        self.LINE_WIDTH = self.LINE_BYTES * 8
        self.OFFSET_BITS = (self.LINE_BYTES - 1).bit_length()
        self.MEM_BYTES = 65536 * self.STRB_W   # MemoryModel capacity

        # deterministic per-line byte content (re-seeded per transaction)
        self._line_seed = {}

        # golden memory: the responders read/write this model, so drains
        # land here and fills read from here -- the round-trip scoreboard
        self.memory_model = MemoryModel(
            num_lines=65536,
            bytes_per_line=self.STRB_W,
            log=self.log,
        )

        clock = dut.clk
        try:
            self.rd_components = create_axi4_slave_rd(
                dut=dut, clock=clock, prefix='m_axi', log=self.log,
                id_width=8, addr_width=self.ADDR_WIDTH,
                data_width=self.BUS_WIDTH, user_width=1,
                memory_model=self.memory_model)
            self.ar_slave = self.rd_components['AR']   # drives m_axi_arready
            self.r_master = self.rd_components['R']    # drives m_axi_r*
            self.wr_components = create_axi4_slave_wr(
                dut=dut, clock=clock, prefix='m_axi', log=self.log,
                id_width=8, addr_width=self.ADDR_WIDTH,
                data_width=self.BUS_WIDTH, user_width=1,
                memory_model=self.memory_model)
            self.aw_slave = self.wr_components['AW']   # drives m_axi_awready
            self.w_slave = self.wr_components['W']     # drives m_axi_wready
            self.b_master = self.wr_components['B']    # drives m_axi_b*
        except Exception as e:
            self.log.error(f"Failed to create responder components: {e}")
            raise

        # observation log: (cyc, kind, payload); cyc ticks at negedge
        self.events = []
        self.cyc = 0

        # EVERY-CYCLE invariant state
        self._prev = {}
        self._fill_open = False
        self._fill_closed_cyc = -10
        self._drain_open = False
        self._drain_closed_cyc = -10
        self._burst_fill = False      # fub AR seen, RLAST not yet
        self._burst_fill_cyc = -1
        self._burst_drain = False     # fub AW seen, B not yet
        self._burst_drain_cyc = -1

        # scorekeeping
        self.checks = 0
        self.mismatches = 0
        self.fills = 0
        self.drains = 0
        self.scenarios = {}
        self._dbg_prev_st = -1

        self.log.info(f"AmberFillDrainTB sets={self.SETS} ways={self.WAYS} "
                      f"level={self.TEST_LEVEL} seed={self.SEED}")

    # ------------------------------------------------------------------
    # helpers
    # ------------------------------------------------------------------
    def _score(self, what, got, exp):
        self.checks += 1
        if got != exp:
            self.mismatches += 1
            if self.mismatches <= 30:
                self.log.error(f"CHECK FAIL: {what}: got {got!r} expected {exp!r}")

    def _line_bytes(self, addr, seed):
        """Deterministic per-transaction line content, written into the
        memory model before a fill / used as the golden drain payload."""
        rng = random.Random(seed)
        return bytes(rng.randrange(256) for _ in range(self.LINE_BYTES))

    def _model_line(self, addr):
        return bytes(self.memory_model.read(addr, self.LINE_BYTES))

    def _beat(self, line, b):
        lo = b * self.STRB_W
        return int.from_bytes(line[lo:lo + self.STRB_W], 'little')

    def set_profile(self, name):
        cfg = self.PROFILES[name]
        self.ar_slave.set_randomizer(FlexRandomizer({'ready_delay': cfg['ready']}))
        self.aw_slave.set_randomizer(FlexRandomizer({'ready_delay': cfg['ready']}))
        self.w_slave.set_randomizer(FlexRandomizer({'ready_delay': cfg['ready']}))
        self.r_master.set_randomizer(FlexRandomizer({'valid_delay': cfg['resp']}))
        self.b_master.set_randomizer(FlexRandomizer({'valid_delay': cfg['resp']}))
        self.log.info(f"responder timing profile -> {name}")

    # ------------------------------------------------------------------
    # clock/reset
    # ------------------------------------------------------------------
    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock('clk', freq=period_ns, units='ns')
        # Monitor sample point: just BEFORE the rising edge (period - 100ps
        # after the falling edge). Every protocol-relevant signal is settled
        # there (DUT outputs are registered; the responder's mid-cycle
        # ready/valid changes all land well before the edge), so a
        # (valid, ready) pair sampled here exactly matches the handshake
        # semantics at the upcoming edge. Sampling AT the falling edge races
        # the responder BFM's same-edge ready writes (measured: the
        # framework's own compliance monitor miscounts W beats under
        # ready-stall profiles for exactly this reason -- see the house
        # axi4_master_wr suite's identical false [W] lines on green runs).
        self._sample_ps = period_ns * 500 - 100
        d = self.dut
        d.fill_start.value = 0
        d.fill_addr.value = 0
        d.fill_req_class.value = 0
        d.drain_start.value = 0
        d.victim_addr.value = 0
        d.victim_data.value = 0
        await self.assert_reset()
        cocotb.start_soon(self._monitor())
        await self.wait_clocks('clk', 3)
        await self.deassert_reset()
        self.set_profile('fast')

    async def assert_reset(self):
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        self.dut.rst_n.value = 1

    async def _negedge_settled(self):
        await FallingEdge(self.dut.clk)
        await Timer(500, units='ps')

    # ------------------------------------------------------------------
    # monitor + EVERY-CYCLE invariants
    # ------------------------------------------------------------------
    def _sig(self, handle):
        v = handle.value
        return int(v) if v.is_resolvable else 0

    async def _monitor(self):
        d = self.dut
        rd = d.u_axi_rd
        wr = d.u_axi_wr
        fill = d.u_fill
        stage = fill.u_stage
        while True:
            await FallingEdge(d.clk)
            await Timer(self._sample_ps, units='ps')
            self.cyc += 1

            # ---- harness control pins ------------------------------
            if self._sig(d.fill_start):
                self.events.append((self.cyc, 'fill_start', {
                    'addr': self._sig(d.fill_addr),
                    'class': self._sig(d.fill_req_class)}))
                self._fill_open = True
            if self._sig(d.fill_done):
                self.events.append((self.cyc, 'fill_done', None))
                self._fill_open = False
                self._fill_closed_cyc = self.cyc
            if self._sig(d.fill_beat_valid):
                self.events.append((self.cyc, 'beat', {
                    'data': self._sig(d.fill_beat_data),
                    'idx': self._sig(d.fill_beat_idx),
                    'last': self._sig(d.fill_last)}))
            if self._sig(d.drain_start):
                self.events.append((self.cyc, 'drain_start', {
                    'addr': self._sig(d.victim_addr)}))
                self._drain_open = True
            if self._sig(d.drain_done):
                self.events.append((self.cyc, 'drain_done', None))
                self._drain_open = False
                self._drain_closed_cyc = self.cyc

            # ---- fub-side engine taps (MAS ch03/02 waveform) -------
            arv, arr = self._sig(rd.fub_axi_arvalid), self._sig(rd.fub_axi_arready)
            ar = {'addr': self._sig(rd.fub_axi_araddr),
                  'len': self._sig(rd.fub_axi_arlen),
                  'size': self._sig(rd.fub_axi_arsize),
                  'burst': self._sig(rd.fub_axi_arburst)}
            self._hold_check('ar', arv, arr, ar)
            if arv and arr:
                self.events.append((self.cyc, 'fub_ar', ar))
                self._score('inv: single outstanding (fill): no AR '
                            'inside an open burst', self._burst_fill, False)
                self._burst_fill = True
                self._burst_fill_cyc = self.cyc

            rv, rr = self._sig(rd.fub_axi_rvalid), self._sig(rd.fub_axi_rready)
            rlast = self._sig(rd.fub_axi_rlast)
            if rv and not rr:
                self._score('inv: fub rready low only at full FIFO',
                            self._sig(stage.wr_ready), 0)
            if rv and rr:
                self.events.append((self.cyc, 'fub_r',
                                    {'data': self._sig(rd.fub_axi_rdata),
                                     'last': rlast}))
                if rlast:
                    self._score('inv: open fill burst at RLAST',
                                self._burst_fill, True)
                    self._burst_fill = False

            awv, awr = self._sig(wr.fub_axi_awvalid), self._sig(wr.fub_axi_awready)
            aw = {'addr': self._sig(wr.fub_axi_awaddr),
                  'len': self._sig(wr.fub_axi_awlen),
                  'size': self._sig(wr.fub_axi_awsize),
                  'burst': self._sig(wr.fub_axi_awburst)}
            self._hold_check('aw', awv, awr, aw)
            if awv and awr:
                self.events.append((self.cyc, 'fub_aw', aw))
                self._score('inv: single outstanding (drain): no AW '
                            'inside an open burst', self._burst_drain, False)
                self._burst_drain = True
                self._burst_drain_cyc = self.cyc

            wv, wr_ = self._sig(wr.fub_axi_wvalid), self._sig(wr.fub_axi_wready)
            w = {'data': self._sig(wr.fub_axi_wdata),
                 'strb': self._sig(wr.fub_axi_wstrb),
                 'last': self._sig(wr.fub_axi_wlast)}
            self._hold_check('w', wv, wr_, w)
            if wv and wr_:
                self.events.append((self.cyc, 'fub_w', w))

            bv, br = self._sig(wr.fub_axi_bvalid), self._sig(wr.fub_axi_bready)
            if bv and br:
                self.events.append((self.cyc, 'fub_b',
                                    {'resp': self._sig(wr.fub_axi_bresp)}))
                self._score('inv: open drain burst at B', self._burst_drain,
                            True)
                self._score('fub bresp OKAY', self._sig(wr.fub_axi_bresp),
                            BRESP_OKAY)
                self._burst_drain = False

            # ---- m_axi protocol-visible taps ------------------------
            if self._sig(d.m_axi_arvalid) and self._sig(d.m_axi_arready):
                self.events.append((self.cyc, 'mx_ar', {
                    'addr': self._sig(d.m_axi_araddr),
                    'len': self._sig(d.m_axi_arlen),
                    'size': self._sig(d.m_axi_arsize),
                    'burst': self._sig(d.m_axi_arburst)}))
            if self._sig(d.m_axi_rvalid) and self._sig(d.m_axi_rready):
                self.events.append((self.cyc, 'mx_r', {
                    'data': self._sig(d.m_axi_rdata),
                    'last': self._sig(d.m_axi_rlast)}))
            if self._sig(d.m_axi_awvalid) and self._sig(d.m_axi_awready):
                self.events.append((self.cyc, 'mx_aw', {
                    'addr': self._sig(d.m_axi_awaddr),
                    'len': self._sig(d.m_axi_awlen),
                    'size': self._sig(d.m_axi_awsize),
                    'burst': self._sig(d.m_axi_awburst)}))
            if self._sig(d.m_axi_wvalid) and self._sig(d.m_axi_wready):
                self.events.append((self.cyc, 'mx_w', {
                    'data': self._sig(d.m_axi_wdata),
                    'strb': self._sig(d.m_axi_wstrb),
                    'last': self._sig(d.m_axi_wlast)}))
            if self._sig(d.m_axi_bvalid) and self._sig(d.m_axi_bready):
                self.events.append((self.cyc, 'mx_b', None))

            # ---- window invariants ----------------------------------
            # NoStrayBeats: a fill beat only inside a fill window (the
            # FIFO drains by fill_done; one cycle of slack for sampling)
            if self.events and self.events[-1][0] == self.cyc \
                    and self.events[-1][1] == 'beat':
                ok = self._fill_open or \
                    self.cyc <= self._fill_closed_cyc + 1
                self._score('inv: no stray fill beats outside a fill '
                            'window', ok, True)
            if self._sig(d.fill_beat_valid) and not self._fill_open:
                self._score('inv: no fill beats after fill_done',
                            self.cyc <= self._fill_closed_cyc + 1, True)

    def _hold_check(self, chan, valid, ready, fields):
        """AXI payload-hold law at the fub taps: once valid rises it stays
        high with identical payload until the handshake completes."""
        p = self._prev.get(chan)
        if p is not None and p['valid'] and not p['ready']:
            self._score(f'inv: {chan}valid held under backpressure',
                        valid, 1)
            for k, v in fields.items():
                self._score(f'inv: {chan} {k} stable under backpressure',
                            v, p['fields'][k])
        self._prev[chan] = {'valid': valid, 'ready': ready, 'fields': fields}

    # ------------------------------------------------------------------
    # event cursor helpers
    # ------------------------------------------------------------------
    async def _wait_tap(self, kind, pos, timeout=1000, pred=None, label=''):
        start = self.cyc
        while True:
            while pos < len(self.events):
                cyc, k, p = self.events[pos]
                pos += 1
                if k == kind and (pred is None or pred(p)):
                    return pos, cyc, p
            if self.cyc - start > timeout:
                raise RuntimeError(
                    f"{label}: _wait_tap({kind}) timed out; recent: "
                    f"{[e[1] for e in self.events[-12:]]}")
            await self._negedge_settled()

    def _slice(self, pos, until_cyc):
        return [e for e in self.events[pos:] if e[0] <= until_cyc]

    # ------------------------------------------------------------------
    # drivers
    # ------------------------------------------------------------------
    async def _launch_fill(self, addr, cls):
        d = self.dut
        await self._negedge_settled()
        d.fill_addr.value = addr
        d.fill_req_class.value = cls
        d.fill_start.value = 1
        pos = len(self.events)
        await self._negedge_settled()
        d.fill_start.value = 0
        return pos

    async def _launch_drain(self, addr, data, hold_payload=True):
        d = self.dut
        await self._negedge_settled()
        d.victim_addr.value = addr
        d.victim_data.value = data
        d.drain_start.value = 1
        pos = len(self.events)
        await self._negedge_settled()
        d.drain_start.value = 0
        if not hold_payload:
            d.victim_addr.value = 0
            d.victim_data.value = 0
        return pos

    # ------------------------------------------------------------------
    # scored transactions
    # ------------------------------------------------------------------
    async def do_fill(self, addr, cls, label, exp_line=None):
        """One fill; scores the full MAS ch03/02 waveform. exp_line is the
        expected beat content (defaults to the current model content)."""
        pos = await self._launch_fill(addr, cls)
        _, done_cyc, _ = await self._wait_tap('fill_done', pos,
                                              label=label)
        sl = self._slice(pos, done_cyc)

        fub_ar = [p for _, k, p in sl if k == 'fub_ar']
        fub_r = [p for _, k, p in sl if k == 'fub_r']
        mx_ar = [p for _, k, p in sl if k == 'mx_ar']
        mx_r = [p for _, k, p in sl if k == 'mx_r']
        beats = [p for _, k, p in sl if k == 'beat']

        if cls == ACE_CLEAN_UNIQUE:
            # the upgrade: no AR, no beats, done exactly one cycle after
            # the start was presented
            self._score(f"{label}: upgrade issues no fub AR", fub_ar, [])
            self._score(f"{label}: upgrade issues no m_axi AR", mx_ar, [])
            self._score(f"{label}: upgrade pulses no beats", beats, [])
            start_cyc = next(c for c, k, _ in sl if k == 'fill_start')
            self._score(f"{label}: upgrade done one cycle after start",
                        done_cyc, start_cyc + 1)
        else:
            if exp_line is None:
                exp_line = self._model_line(addr)
            self._score(f"{label}: exactly one fub AR", len(fub_ar), 1)
            if fub_ar:
                self._score(f"{label}: fub araddr", fub_ar[0]['addr'], addr)
                self._score(f"{label}: fub arlen", fub_ar[0]['len'],
                            self.FILL_BEATS - 1)
                self._score(f"{label}: fub arsize", fub_ar[0]['size'],
                            self.AXSIZE)
                self._score(f"{label}: fub arburst", fub_ar[0]['burst'],
                            AXBURST_INCR)
            self._score(f"{label}: exactly one m_axi AR", len(mx_ar), 1)
            if mx_ar:
                self._score(f"{label}: m_axi araddr", mx_ar[0]['addr'], addr)
                self._score(f"{label}: m_axi arlen", mx_ar[0]['len'],
                            self.FILL_BEATS - 1)
                self._score(f"{label}: m_axi arsize", mx_ar[0]['size'],
                            self.AXSIZE)
                self._score(f"{label}: m_axi arburst", mx_ar[0]['burst'],
                            AXBURST_INCR)
            self._score(f"{label}: fub R beat count", len(fub_r),
                        self.FILL_BEATS)
            self._score(f"{label}: m_axi R beat count", len(mx_r),
                        self.FILL_BEATS)
            self._score(f"{label}: fub R last only on final beat",
                        [p['last'] for p in fub_r],
                        [1 if i == self.FILL_BEATS - 1 else 0
                         for i in range(len(fub_r))])
            # fill_done exactly one cycle after the fub RLAST handshake
            rlast_cyc = next((c for c, k, p in sl
                              if k == 'fub_r' and p['last']), None)
            self._score(f"{label}: fill_done one cycle after fub RLAST",
                        done_cyc, None if rlast_cyc is None
                        else rlast_cyc + 1)
            # beat presentation: count, idx order, data, last
            self._score(f"{label}: beat count", len(beats), self.FILL_BEATS)
            self._score(f"{label}: beat idx order",
                        [b['idx'] for b in beats],
                        list(range(self.FILL_BEATS)))
            for i, b in enumerate(beats):
                self._score(f"{label}: beat{i} data", b['data'],
                            self._beat(exp_line, i))
                self._score(f"{label}: beat{i} last", b['last'],
                            1 if i == self.FILL_BEATS - 1 else 0)
        self.fills += 1
        return done_cyc

    async def do_drain(self, addr, data, label, check_model=True):
        """One drain; scores the AW/W/B waveform + the memory-side effect."""
        line = data.to_bytes(self.LINE_BYTES, 'little')
        pos = await self._launch_drain(addr, data)
        _, done_cyc, _ = await self._wait_tap('drain_done', pos,
                                              label=label)
        sl = self._slice(pos, done_cyc)

        fub_aw = [p for _, k, p in sl if k == 'fub_aw']
        fub_w = [p for _, k, p in sl if k == 'fub_w']
        fub_b = [p for _, k, p in sl if k == 'fub_b']
        mx_aw = [p for _, k, p in sl if k == 'mx_aw']
        mx_w = [p for _, k, p in sl if k == 'mx_w']
        mx_b = [p for _, k, p in sl if k == 'mx_b']

        self._score(f"{label}: exactly one fub AW", len(fub_aw), 1)
        if fub_aw:
            self._score(f"{label}: fub awaddr", fub_aw[0]['addr'], addr)
            self._score(f"{label}: fub awlen", fub_aw[0]['len'],
                        self.FILL_BEATS - 1)
            self._score(f"{label}: fub awsize", fub_aw[0]['size'], self.AXSIZE)
            self._score(f"{label}: fub awburst", fub_aw[0]['burst'],
                        AXBURST_INCR)
        self._score(f"{label}: exactly one m_axi AW", len(mx_aw), 1)
        if mx_aw:
            self._score(f"{label}: m_axi awaddr", mx_aw[0]['addr'], addr)
            self._score(f"{label}: m_axi awlen", mx_aw[0]['len'],
                        self.FILL_BEATS - 1)
        self._score(f"{label}: fub W beat count", len(fub_w), self.FILL_BEATS)
        self._score(f"{label}: m_axi W beat count", len(mx_w),
                    self.FILL_BEATS)
        for i, p in enumerate(fub_w):
            self._score(f"{label}: fub w{i} data", p['data'],
                        self._beat(line, i))
            self._score(f"{label}: fub w{i} strb all-1s", p['strb'],
                        (1 << self.STRB_W) - 1)
            self._score(f"{label}: fub w{i} last", p['last'],
                        1 if i == self.FILL_BEATS - 1 else 0)
        self._score(f"{label}: fub B count", len(fub_b), 1)
        self._score(f"{label}: m_axi B count", len(mx_b), 1)

        # MAS ch03/02 waveform order: AW < first W; WLAST < B; B < done+1
        aw_cyc = next((c for c, k, _ in sl if k == 'fub_aw'), None)
        first_w = next((c for c, k, _ in sl if k == 'fub_w'), None)
        last_w = next((c for c, k, p in sl if k == 'fub_w'
                       and p['last']), None)
        b_cyc = next((c for c, k, _ in sl if k == 'fub_b'), None)
        self._score(f"{label}: AW before first W",
                    None in (aw_cyc, first_w), False)
        if aw_cyc is not None and first_w is not None:
            self._score(f"{label}: AW strictly before first W",
                        aw_cyc < first_w, True)
        self._score(f"{label}: WLAST before B", None in (last_w, b_cyc),
                    False)
        if last_w is not None and b_cyc is not None:
            self._score(f"{label}: WLAST strictly before B",
                        last_w < b_cyc, True)
        self._score(f"{label}: drain_done one cycle after fub B",
                    done_cyc, None if b_cyc is None else b_cyc + 1)

        if check_model:
            self._score(f"{label}: memory writeback payload",
                        self._model_line(addr), line)
        self.drains += 1
        return done_cyc

    # ------------------------------------------------------------------
    # directed scenarios
    # ------------------------------------------------------------------
    async def _fill_waveform(self):
        # FillBurstWaveform (gate): READ_SHARED, fast responder
        self.set_profile('fast')
        addr = 0x0000_4000
        seed = random.randrange(2 ** 31)
        line = self._line_bytes(addr, seed)
        self.memory_model.write(addr, bytearray(line))
        await self.do_fill(addr, ACE_READ_SHARED, 'fill_wf')
        self.log.info("FillBurstWaveform directed done")

    async def _upgrade_no_fetch(self):
        # UpgradeNoFetch (gate): CLEAN_UNIQUE -- no AR at all
        addr = 0x0000_5000
        await self.do_fill(addr, ACE_CLEAN_UNIQUE, 'upgr')
        self.log.info("UpgradeNoFetch directed done")

    async def _drain_waveform(self):
        # DrainBurstWaveform (gate)
        self.set_profile('fast')
        addr = 0x0001_0000
        seed = random.randrange(2 ** 31)
        line = self._line_bytes(addr, seed)
        await self.do_drain(addr, int.from_bytes(line, 'little'), 'drain_wf')
        self.log.info("DrainBurstWaveform directed done")

    async def _read_unique_data(self):
        # ReadUniqueData (func): randomized contents, READ_UNIQUE
        for i in range(4):
            addr = 0x0000_6000 + i * self.LINE_BYTES
            seed = random.randrange(2 ** 31)
            line = self._line_bytes(addr, seed)
            self.memory_model.write(addr, bytearray(line))
            await self.do_fill(addr, ACE_READ_UNIQUE, f'ru[{i}]')
        self.log.info("ReadUniqueData directed done")

    async def _r_backpressure(self):
        # RBackpressureIntegrity (func): slow R + AR stalls
        self.set_profile('slow')
        for i in range(3):
            addr = 0x0000_7000 + i * self.LINE_BYTES
            seed = random.randrange(2 ** 31)
            line = self._line_bytes(addr, seed)
            self.memory_model.write(addr, bytearray(line))
            await self.do_fill(addr, ACE_READ_SHARED, f'rback[{i}]')
        self.log.info("RBackpressureIntegrity directed done")

    async def _w_backpressure(self):
        # WBackpressurePayloadHold + BResponseDelay (func): slow W/B
        self.set_profile('slow')
        for i in range(3):
            addr = 0x0001_1000 + i * self.LINE_BYTES
            seed = random.randrange(2 ** 31)
            line = self._line_bytes(addr, seed)
            await self.do_drain(addr, int.from_bytes(line, 'little'),
                                f'wback[{i}]')
        self.log.info("WBackpressurePayloadHold directed done")

    async def _single_outstanding(self):
        # SingleOutstanding (func): back-to-back transactions under slow
        # responder timing; the EVERY-CYCLE burst invariants own the claim,
        # here we additionally pin the cross-transaction ordering
        self.set_profile('normal')
        prev_done = None
        for i in range(3):
            addr = 0x0000_8000 + i * self.LINE_BYTES
            seed = random.randrange(2 ** 31)
            line = self._line_bytes(addr, seed)
            self.memory_model.write(addr, bytearray(line))
            pos = len(self.events)
            done = await self.do_fill(addr, ACE_READ_SHARED, f'so_f[{i}]')
            if prev_done is not None:
                ar_cyc = next((c for c, k, _ in self.events[pos:]
                               if k == 'fub_ar'), None)
                self._score(f"so_f[{i}]: AR strictly after previous "
                            f"fill_done", ar_cyc > prev_done, True)
            prev_done = done
        prev_done = None
        for i in range(3):
            addr = 0x0001_2000 + i * self.LINE_BYTES
            seed = random.randrange(2 ** 31)
            line = self._line_bytes(addr, seed)
            pos = len(self.events)
            done = await self.do_drain(addr, int.from_bytes(line, 'little'),
                                       f'so_d[{i}]')
            if prev_done is not None:
                aw_cyc = next((c for c, k, _ in self.events[pos:]
                               if k == 'fub_aw'), None)
                self._score(f"so_d[{i}]: AW strictly after previous "
                            f"drain_done", aw_cyc > prev_done, True)
            prev_done = done
        self.log.info("SingleOutstanding directed done")

    async def _writeback_round_trip(self):
        # WritebackRoundTrip (func): drain then fill the same line; the
        # fill beats must return the exact victim bytes
        self.set_profile('normal')
        addr = 0x0001_3000
        seed = random.randrange(2 ** 31)
        line = self._line_bytes(addr, seed)
        await self.do_drain(addr, int.from_bytes(line, 'little'), 'rt:drain')
        await self.do_fill(addr, ACE_READ_SHARED, 'rt:fill', exp_line=line)
        self.log.info("WritebackRoundTrip directed done")

    async def _drain_latches_payload(self):
        # DrainLatchesPayload (func): the payload registers at drain_start;
        # corrupting the pins right after the start must not change AW/W
        addr = 0x0001_4000
        seed = random.randrange(2 ** 31)
        line = self._line_bytes(addr, seed)
        pos = await self._launch_drain(addr, int.from_bytes(line, 'little'),
                                       hold_payload=False)
        _, done_cyc, _ = await self._wait_tap('drain_done', pos, label='latch')
        sl = self._slice(pos, done_cyc)
        fub_aw = [p for _, k, p in sl if k == 'fub_aw']
        fub_w = [p for _, k, p in sl if k == 'fub_w']
        self._score("latch: AW addr is the pre-corruption payload",
                    fub_aw[0]['addr'] if fub_aw else None, addr)
        for i, p in enumerate(fub_w):
            self._score(f"latch: W beat{i} is the pre-corruption payload",
                        p['data'], self._beat(line, i))
        self._score("latch: memory holds the pre-corruption payload",
                    self._model_line(addr), line)
        self.drains += 1
        self.log.info("DrainLatchesPayload directed done")

    # ------------------------------------------------------------------
    # FULL soak: concurrent randomized fill + drain streams
    # ------------------------------------------------------------------
    async def _fill_soak(self, n, base, span_lines, profile_switch=0.25):
        for i in range(n):
            if random.random() < profile_switch:
                self.set_profile(random.choice(list(self.PROFILES)))
            line_no = base + random.randrange(span_lines)
            addr = line_no * self.LINE_BYTES
            cls = random.choice([ACE_READ_SHARED, ACE_READ_UNIQUE,
                                 ACE_CLEAN_UNIQUE])
            if cls != ACE_CLEAN_UNIQUE:
                seed = random.randrange(2 ** 31)
                line = self._line_bytes(addr, seed)
                self.memory_model.write(addr, bytearray(line))
            await self.do_fill(addr, cls, f'soak_f[{i}]')
            for _ in range(random.randrange(3)):
                await self._negedge_settled()

    async def _drain_soak(self, n, base, span_lines, profile_switch=0.25):
        for i in range(n):
            if random.random() < profile_switch:
                self.set_profile(random.choice(list(self.PROFILES)))
            line_no = base + random.randrange(span_lines)
            addr = line_no * self.LINE_BYTES
            seed = random.randrange(2 ** 31)
            line = self._line_bytes(addr, seed)
            await self.do_drain(addr, int.from_bytes(line, 'little'),
                                f'soak_d[{i}]')
            for _ in range(random.randrange(3)):
                await self._negedge_settled()

    # ------------------------------------------------------------------
    # top-level run
    # ------------------------------------------------------------------
    async def run(self):
        await self._fill_waveform()
        self.scenarios['FillBurstWaveform'] = True
        await self._upgrade_no_fetch()
        self.scenarios['UpgradeNoFetch'] = True
        await self._drain_waveform()
        self.scenarios['DrainBurstWaveform'] = True

        if self.TEST_LEVEL in ('func', 'full'):
            await self._read_unique_data()
            self.scenarios['ReadUniqueData'] = True
            await self._r_backpressure()
            self.scenarios['RBackpressureIntegrity'] = True
            await self._w_backpressure()
            self.scenarios['WBackpressurePayloadHold'] = True
            self.scenarios['BResponseDelay'] = True
            await self._single_outstanding()
            self.scenarios['SingleOutstanding'] = True
            await self._writeback_round_trip()
            self.scenarios['WritebackRoundTrip'] = True
            await self._drain_latches_payload()
            self.scenarios['DrainLatchesPayload'] = True

        if self.TEST_LEVEL == 'full':
            # concurrent engines on disjoint address ranges; the shared
            # MemoryModel is audited transaction-by-transaction
            self.set_profile('normal')
            fill_task = cocotb.start_soon(self._fill_soak(
                self.FULL_TXN['full'], base=0x0000, span_lines=2048))
            drain_task = cocotb.start_soon(self._drain_soak(
                self.FULL_TXN['full'], base=0x0800, span_lines=2048))
            await fill_task
            await drain_task
            self.scenarios['FillRandomSoak'] = True
            self.scenarios['DrainRandomSoak'] = True

        # tail: everything drained, nothing dangling
        await self.wait_clocks('clk', 10)
        self._score('inv: no dangling fill burst at end', self._burst_fill,
                    False)
        self._score('inv: no dangling drain burst at end', self._burst_drain,
                    False)
        return self.mismatches == 0

    def get_test_report(self):
        return {
            'checks': self.checks,
            'mismatches': self.mismatches,
            'fills': self.fills,
            'drains': self.drains,
            'scenarios': self.scenarios,
        }
