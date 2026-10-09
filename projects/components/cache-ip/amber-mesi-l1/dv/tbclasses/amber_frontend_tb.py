# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/seangalloway/RTLDesignSherpa
#
# Module: AmberFrontendTB
# Purpose: Testbench for the amber_cpu_frontend GAXI slave (Task 8, MAS
# ch02_blocks/09 + ch03_interfaces/01)

"""
amber_cpu_frontend testbench

CPU-facing GAXI slave bring-up (Task 8): the DUT closure is the harness
amber_frontend_th -- REAL amber_cpu_frontend + REAL amber_control + the
landed tag/data/repl arrays. CPU requests enter through the GAXI
cpu_req_wr_* channel (house GAXIMaster BFM drives it, packed
{addr, we, be, wdata} per MAS ch02/09) and responses are collected on the
cpu_rsp_rd_* channel (house GAXISlave BFM, with policy-controlled
backpressure). The partner FUBs stay timing stubs per D-12 (fill writes
the memory-side beats, drain is a fixed latency, the snoop responder
contract is modeled on the snoop_req/ctrl_crresp/cdvalid pins).

What this suite pins (the frontend's own contract; control behavior is
proven by the amber_control suite):
  * request latch/replay visibility: exactly one control-side req_valid
    pulse per accepted GAXI request, fields stable from accept to
    response; cpu_req_wr_ready only while control is in CTRL_IDLE with
    staging FIFO room (no accept during a miss sequence)
  * response staging (DECISION D-6): cpu_rsp_rd_valid/data registered in
    the gaxi_fifo_sync; data held stable and valid held high under
    cpu_rsp_rd_ready low for arbitrarily many cycles; responses in
    request order (blocking pipeline)
  * data integrity through the closure: read responses return the
    memory-side line content (fill snapshot + write merges); write
    responses echo the request payload (amber_control rsp contract)
  * the snoop-priority detour is invisible at the GAXI boundary: one
    request, one response, correct data
  * a miss (fill + replay) looks like a single GAXI transaction

Golden models carried here (independent copies, kmap-TB rule: no shared
code with the DUT):
  memory-side line content   self.mem -- default pattern + write merges

Levels (TEST_LEVEL):
  gate  -- InitReady + directed hit/miss/upgrade sequences + visibility
  func  -- + response backpressure holds, pipelined responses, snoop
           detour, single-transaction replay
  full  -- + randomized soak (random valid/ready delays), every-cycle
           invariants live (seeds pinned by the repo-root conftest)

Author: RTL Design Sherpa
Created: 2026-10-08
"""

import os
import random

import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.field_config import FieldConfig
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave


# ctrl_state_t codes (amber_pkg) -- kept textual for log messages
ST_IDLE, ST_INIT, ST_LOOKUP, ST_HIT_RD, ST_HIT_WR, ST_MISS_VICTIM, \
    ST_MISS_DRAIN, ST_MISS_FILL, ST_FILL_WRITE, ST_REPLAY, ST_SNOOP, \
    ST_ERROR = range(0xC)

STATE_NAMES = {
    ST_IDLE: 'IDLE', ST_INIT: 'INIT', ST_LOOKUP: 'LOOKUP',
    ST_HIT_RD: 'HIT_RD', ST_HIT_WR: 'HIT_WR', ST_MISS_VICTIM: 'MISS_VICTIM',
    ST_MISS_DRAIN: 'MISS_DRAIN', ST_MISS_FILL: 'MISS_FILL',
    ST_FILL_WRITE: 'FILL_WRITE', ST_REPLAY: 'REPLAY', ST_SNOOP: 'SNOOP',
    ST_ERROR: 'ERROR',
}

# amber_ace_req_t encodings (amber_pkg): fill request classes
ACE_READ_SHARED, ACE_READ_UNIQUE, ACE_CLEAN_UNIQUE = 0, 1, 2

# partner stub timing knobs (handshake timing only, D-12)
FILL_DONE_DELAY = 6          # cycles between last beat and fill_done
DRAIN_LATENCY = None         # set per-geometry: FILL_BEATS + 2


class AmberFrontendTB(TBBase):
    """Scores amber_cpu_frontend's GAXI contract through the real closure."""

    FULL_TXN = {'gate': 0, 'func': 0, 'full': 2500}
    RSP_TIMEOUT_CYCLES = 1000

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        random.seed(self.SEED)

        # geometry (grid varies DATA_WIDTH/LINE_BYTES; addr/sets/ways at
        # the pkg defaults, same convention as the snoop_resp suite)
        self.ADDR_WIDTH = int(os.environ.get('ADDR_WIDTH', '32'))
        self.DATA_WIDTH = int(os.environ.get('DATA_WIDTH', '64'))
        self.LINE_BYTES = int(os.environ.get('LINE_BYTES', '64'))
        self.SETS = 128
        self.WAYS = 4
        self.STRB_W = self.DATA_WIDTH // 8
        self.FILL_BEATS = self.LINE_BYTES // self.STRB_W
        self.SET_BITS = (self.SETS - 1).bit_length()
        self.OFFSET_BITS = (self.LINE_BYTES - 1).bit_length()
        self.BEAT_BITS = (self.FILL_BEATS - 1).bit_length()
        self.SET_MASK = self.SETS - 1
        self.LINE_MASK = (1 << (self.ADDR_WIDTH - self.OFFSET_BITS)) - 1
        self.CPU_REQ_W = self.ADDR_WIDTH + 1 + self.STRB_W + self.DATA_WIDTH

        self.drain_latency = self.FILL_BEATS + 2

        # golden models
        self.mem = {}

        # observation log: (cyc, kind, payload); cyc ticks at negedge
        self.events = []
        self.cyc = 0
        self.stub_victim_way = 0

        # response bookkeeping: slave callback appends here
        self.rsp_log = []

        # EVERY-CYCLE invariant state
        self.inv_rsp_stall = None   # (data,) once valid rose under stall

        # scorekeeping
        self.checks = 0
        self.mismatches = 0
        self.txns = 0
        self.snoops = 0
        self.packets = 0
        self.dropped = 0
        self.scenarios = {}

        self.log.info(f"AmberFrontendTB b{self.DATA_WIDTH} "
                      f"line={self.LINE_BYTES} level={self.TEST_LEVEL} "
                      f"seed={self.SEED}")

    # ------------------------------------------------------------------
    # helpers
    # ------------------------------------------------------------------
    def _score(self, what, got, exp):
        self.checks += 1
        if got != exp:
            self.mismatches += 1
            if self.mismatches <= 30:
                self.log.error(f"CHECK FAIL: {what}: got {got!r} "
                               f"expected {exp!r}")

    def _scenario(self, name):
        self.scenarios[name] = {'checks': self.checks,
                                'mismatches': self.mismatches}

    def _line_of(self, addr):
        return (addr >> self.OFFSET_BITS) & self.LINE_MASK

    def _set_of_line(self, line):
        return line & self.SET_MASK

    def _compose_addr(self, tag, set_idx, beat=0):
        line = (tag << (self.SET_BITS + self.OFFSET_BITS)) \
            | ((set_idx & self.SET_MASK) << self.OFFSET_BITS)
        return line | (beat << (self.STRB_W.bit_length() - 1))

    def _default_line(self, line):
        """Deterministic memory-side content for a never-touched line."""
        return bytes(((line + 0x11 * i) & 0xFF) for i in range(self.LINE_BYTES))

    def _mem_line(self, line):
        if line not in self.mem:
            self.mem[line] = bytearray(self._default_line(line))
        return self.mem[line]

    def _beat_of_line(self, line_data, beat):
        lo = beat * self.STRB_W
        return int.from_bytes(bytes(line_data[lo:lo + self.STRB_W]), 'little')

    def _pack_req(self, addr, we, be, wdata):
        return ((addr & ((1 << self.ADDR_WIDTH) - 1))
                << (1 + self.STRB_W + self.DATA_WIDTH)) \
            | ((we & 1) << (self.STRB_W + self.DATA_WIDTH)) \
            | ((be & ((1 << self.STRB_W) - 1)) << self.DATA_WIDTH) \
            | (wdata & ((1 << self.DATA_WIDTH) - 1))

    # ------------------------------------------------------------------
    # clock/reset/monitor/stubs/BFMs
    # ------------------------------------------------------------------
    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock('clk', freq=period_ns, units='ns')
        d = self.dut

        # house GAXI BFM family on the CPU channels
        req_fields = FieldConfig.from_dict(
            field_dict={'data': {'bits': self.CPU_REQ_W, 'default': 0}},
            lsb_first=True)
        rsp_fields = FieldConfig.from_dict(
            field_dict={'data': {'bits': self.DATA_WIDTH, 'default': 0}},
            lsb_first=True)

        zero_delay = FlexRandomizer(
            {'valid_delay': ([(0, 0)], [1])})
        soak_delay = FlexRandomizer(
            {'valid_delay': ([(0, 0), (1, 3), (4, 10)], [6, 3, 1])})
        master_rand = soak_delay if self.TEST_LEVEL == 'full' else zero_delay

        self.master = GAXIMaster(
            dut=d, title='cpu_req', prefix='',
            clock=d.clk, field_config=req_fields,
            timeout_cycles=self.RSP_TIMEOUT_CYCLES,
            mode='skid', bus_name='cpu_req_wr', pkt_prefix='',
            multi_sig=False, randomizer=master_rand, log=self.log)

        # response channel: randomized ready_delay in the soak, directed
        # policy control otherwise
        if self.TEST_LEVEL == 'full':
            rsp_rand = FlexRandomizer(
                {'ready_delay': ([(0, 0), (1, 5)], [7, 3])})
        else:
            rsp_rand = FlexRandomizer({'ready_delay': ([(0, 0)], [1])})
        self.slave = GAXISlave(
            dut=d, title='cpu_rsp', prefix='',
            clock=d.clk, field_config=rsp_fields,
            timeout_cycles=self.RSP_TIMEOUT_CYCLES,
            mode='skid', bus_name='cpu_rsp_rd', pkt_prefix='',
            multi_sig=False, randomizer=rsp_rand, log=self.log)
        self.slave.add_callback(self._on_rsp)
        # auto-accept by default; the directed backpressure scenarios drop
        # the policy to 'stall' and accept explicitly
        self.slave.set_ready_policy('always')

        # stub pins the BFMs do not own
        d.fill_done.value = 0
        d.drain_done.value = 0
        d.fillbeat_wr_en.value = 0
        d.fillbeat_wr_addr.value = 0
        d.fillbeat_wr_way.value = 0
        d.fillbeat_wr_data.value = 0
        d.fillbeat_wr_be.value = 0
        d.fill_beat_valid.value = 0
        d.fill_beat_idx.value = 0
        d.snoop_req.value = 0
        d.snoop_type.value = 0
        d.snoop_addr.value = 0
        d.cd_ready_in.value = 1
        d.tag_b_set.value = 0
        if hasattr(d, 'mon_time'):
            d.mon_time.value = 0

        await self.assert_reset()
        cocotb.start_soon(self._monitor())
        cocotb.start_soon(self._fill_stub())
        cocotb.start_soon(self._drain_stub())
        cocotb.start_soon(self._victim_way_tracker())
        cocotb.start_soon(self._rsp_stability_invariant())
        await self.wait_clocks('clk', 3)
        await self.deassert_reset()

    async def assert_reset(self):
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        self.dut.rst_n.value = 1

    def _on_rsp(self, packet):
        """GAXISlave callback: one accepted response packet."""
        data = int(getattr(packet, 'fields', {}).get('data', 0))
        self.rsp_log.append((self.cyc, data))

    async def _negedge_settled(self):
        await FallingEdge(self.dut.clk)
        await Timer(500, units='ps')

    async def _negedge(self):
        await FallingEdge(self.dut.clk)

    async def _monitor(self):
        d = self.dut
        prev_state = -1
        prev_rsp_valid = 0
        while True:
            await FallingEdge(d.clk)
            await Timer(100, units='ps')
            self.cyc += 1
            if hasattr(d, 'mon_time'):
                d.mon_time.value = self.cyc
            st = int(d.ctrl_state.value)
            if st != prev_state:
                self.events.append((self.cyc, 'state', st))
                prev_state = st
            if int(d.cpu_req_wr_valid.value) and int(d.cpu_req_wr_ready.value):
                packed = int(d.cpu_req_wr_data.value)
                wdata = packed & ((1 << self.DATA_WIDTH) - 1)
                be = (packed >> self.DATA_WIDTH) & ((1 << self.STRB_W) - 1)
                we = (packed >> (self.DATA_WIDTH + self.STRB_W)) & 1
                addr = (packed >> (self.DATA_WIDTH + self.STRB_W + 1)) \
                    & ((1 << self.ADDR_WIDTH) - 1)
                self.events.append((self.cyc, 'accept',
                                    {'addr': addr, 'we': we, 'be': be,
                                     'wdata': wdata}))
            if int(d.fe_req_valid.value):
                self.events.append((self.cyc, 'fe_req', None))
            if int(d.ctrl_rsp_valid.value):
                self.events.append((self.cyc, 'ctrl_rsp',
                                    int(d.ctrl_rsp_data.value)))
            rsp_valid = int(d.cpu_rsp_rd_valid.value)
            if rsp_valid and not prev_rsp_valid:
                self.events.append((self.cyc, 'rsp_rise',
                                    int(d.cpu_rsp_rd_data.value)))
            if rsp_valid and int(d.cpu_rsp_rd_ready.value):
                self.events.append((self.cyc, 'rsp',
                                    int(d.cpu_rsp_rd_data.value)))
            prev_rsp_valid = rsp_valid
            if int(d.fill_start.value):
                self.events.append((self.cyc, 'fill_start', {
                    'addr': int(d.fill_addr.value),
                    'class': int(d.fill_req_class.value)}))
            if int(d.fill_done.value):
                self.events.append((self.cyc, 'fill_done', None))
            if int(d.drain_start.value):
                self.events.append((self.cyc, 'drain_start', None))
            if int(d.drain_done.value):
                self.events.append((self.cyc, 'drain_done', None))
            if int(d.victim_load.value):
                self.events.append((self.cyc, 'victim_load', {
                    'addr': int(d.victim_addr.value)}))
            if int(d.snoop_req.value) and int(d.snoop_ready.value):
                self.events.append((self.cyc, 'snoop_gnt', {
                    'type': int(d.snoop_type.value)}))

    async def _rsp_stability_invariant(self):
        """EVERY-CYCLE: once cpu_rsp_rd_valid rises it stays high and the
        payload holds byte-stable until the handshake (DECISION D-6:
        response staging must not glitch under backpressure)."""
        d = self.dut
        while True:
            await self._negedge_settled()
            v = int(d.cpu_rsp_rd_valid.value)
            if v:
                data = int(d.cpu_rsp_rd_data.value)
                if self.inv_rsp_stall is None:
                    self.inv_rsp_stall = data
                else:
                    self._score('rsp inv: valid held under backpressure',
                                1, 1)
                    self._score('rsp inv: data stable under backpressure',
                                data, self.inv_rsp_stall)
                if int(d.cpu_rsp_rd_ready.value):
                    self.inv_rsp_stall = None
            else:
                self.inv_rsp_stall = None

    async def _victim_way_tracker(self):
        """The fill stub needs the install way; it observes the same repl
        tap the DUT uses (timing-only modeling, D-12)."""
        while True:
            await self._negedge_settled()
            if int(self.dut.repl_req.value):
                self.stub_victim_way = int(self.dut.repl_victim_way.value)

    async def _fill_stub(self):
        """amber_fill timing model: on fill_start, deliver FILL_BEATS beats
        into the data array (read-data classes only -- CLEAN_UNIQUE carries
        no data), strobing each beat index to control, then fill_done after
        FILL_DONE_DELAY cycles."""
        d = self.dut
        full_be = (1 << self.STRB_W) - 1
        while True:
            await self._negedge_settled()
            if not int(d.fill_start.value):
                continue
            addr = int(d.fill_addr.value)
            cls = int(d.fill_req_class.value)
            set_idx = (addr >> self.OFFSET_BITS) & self.SET_MASK
            if cls != ACE_CLEAN_UNIQUE:
                line = self._line_of(addr)
                line_data = bytes(self._mem_line(line))
                for b in range(self.FILL_BEATS):
                    await self._negedge()
                    d.fillbeat_wr_en.value = 1
                    d.fillbeat_wr_addr.value = (set_idx << self.BEAT_BITS) | b
                    d.fillbeat_wr_way.value = self.stub_victim_way
                    d.fillbeat_wr_data.value = self._beat_of_line(line_data, b)
                    d.fillbeat_wr_be.value = full_be
                    d.fill_beat_valid.value = 1
                    d.fill_beat_idx.value = b
                await self._negedge()
                d.fillbeat_wr_en.value = 0
                d.fill_beat_valid.value = 0
                d.fill_beat_idx.value = 0
            for _ in range(FILL_DONE_DELAY):
                await self._negedge()
            d.fill_done.value = 1
            await self._negedge()
            d.fill_done.value = 0

    async def _drain_stub(self):
        """amber_drain timing model: drain_start -> fixed-latency burst ->
        drain_done pulse."""
        d = self.dut
        while True:
            await self._negedge_settled()
            if not int(d.drain_start.value):
                continue
            for _ in range(self.drain_latency):
                await self._negedge()
            d.drain_done.value = 1
            await self._negedge()
            d.drain_done.value = 0

    # ------------------------------------------------------------------
    # event helpers
    # ------------------------------------------------------------------
    def _slice(self, lo, hi):
        return [e for e in self.events if lo <= e[0] <= hi]

    # ------------------------------------------------------------------
    # one scored transaction through the GAXI BFM
    # ------------------------------------------------------------------
    async def _txn(self, addr, we, be=None, wdata=None, label=''):
        if be is None:
            be = random.randrange(1, 1 << self.STRB_W) if we \
                else (1 << self.STRB_W) - 1
        if wdata is None:
            wdata = random.getrandbits(self.DATA_WIDTH) if we else 0

        line = self._line_of(addr)
        beat = (addr >> (self.STRB_W.bit_length() - 1)) & (self.FILL_BEATS - 1)

        n_accept = len([1 for _, k, _ in self.events if k == 'accept'])
        n_rsp = len(self.rsp_log)

        pkt = self.master.create_packet(
            data=self._pack_req(addr, we, be, wdata))
        await self.master.send(pkt)

        # blocking pipeline: exactly one new accept and one new response
        for _ in range(self.RSP_TIMEOUT_CYCLES):
            accepts = [e for e in self.events if e[1] == 'accept']
            if len(accepts) >= n_accept + 1 and len(self.rsp_log) >= n_rsp + 1:
                break
            await self._negedge_settled()
        accepts = [e for e in self.events if e[1] == 'accept']
        self._score(f"{label} exactly one GAXI accept",
                    len(accepts), n_accept + 1)
        self._score(f"{label} exactly one response", len(self.rsp_log),
                    n_rsp + 1)
        accept_cyc, _, accept_p = accepts[-1]
        rsp_cyc, rsp_data = self.rsp_log[-1]
        self._score(f"{label} accept payload addr", accept_p['addr'], addr)
        self._score(f"{label} accept payload we", accept_p['we'], we)

        # response data vs the memory-side content model
        if we:
            exp_rsp = wdata
        else:
            exp_rsp = self._beat_of_line(self._mem_line(line), beat)
        self._score(f"{label} rsp data", rsp_data, exp_rsp)

        # apply the write merge to the model
        if we:
            lo = beat * self.STRB_W
            ml = self._mem_line(line)
            for i in range(self.STRB_W):
                if be & (1 << i):
                    ml[lo + i] = (wdata >> (8 * i)) & 0xFF

        self.txns += 1
        return accept_cyc, rsp_cyc, rsp_data

    async def _snoop(self, snoop_type, addr, label=''):
        """Model the amber_snoop_resp core-facing contract: req held until
        ready; CD beats consumed (cd_ready_in is tied 1)."""
        d = self.dut
        await self._negedge_settled()
        d.snoop_addr.value = addr
        d.snoop_type.value = snoop_type
        d.snoop_req.value = 1
        while True:
            await self._negedge_settled()
            if int(d.snoop_ready.value):
                break
        d.snoop_req.value = 0
        d.snoop_addr.value = 0
        d.snoop_type.value = 0
        self.snoops += 1

    async def _accept_rsp_when_valid(self, label=''):
        """Response-channel helper for directed backpressure: accept the
        pending response as soon as it is valid, then return to
        auto-accept."""
        d = self.dut
        n_rsp = len(self.rsp_log)
        while len(self.rsp_log) < n_rsp + 1:
            if not int(d.cpu_rsp_rd_ready.value):
                self.slave.set_ready_policy('always')
            await self._negedge_settled()
        self.slave.set_ready_policy('always')
        return self.rsp_log[-1]

    # ------------------------------------------------------------------
    # scenarios
    # ------------------------------------------------------------------
    async def _s_init_ready(self):
        """cpu_req_wr_ready stays low through the INIT walk and rises only
        after every set holds STATE_I (frontend passes control's ready
        through; MAS ch02/09)."""
        d = self.dut
        cycles = 0
        saw_low = 0
        while True:
            await self._negedge_settled()
            cycles += 1
            if cycles > self.SETS * 4 + 100:
                raise RuntimeError("init walk never completed")
            if not int(d.init_busy.value):
                if int(d.cpu_req_wr_ready.value):
                    break
            else:
                saw_low += int(not int(d.cpu_req_wr_ready.value))
                self._score("init: cpu_req_wr_ready low while init busy",
                            int(d.cpu_req_wr_ready.value), 0)
        self._score("init: ready observed low during walk", saw_low > 0, True)
        self._score("init: walk bounded", cycles <= self.SETS + 20, True)

    async def _s_hit_sequence(self):
        """Directed read hits and write hits/upgrade against default lines:
        response data scored against the content model, request/response
        visibility pinned (one accept, one fe_req pulse, one response)."""
        self._scenario('HitSequence')
        base_tag = 0x30
        # read miss (fill) -> read hit -> write hit (S line, upgrade)
        for i, (tag, we) in enumerate([(base_tag, 0), (base_tag, 0),
                                       (base_tag, 1)]):
            addr = self._compose_addr(tag, 5)
            accept_cyc, rsp_cyc, _ = await self._txn(
                addr, we, be=(1 << self.STRB_W) - 1 if we else None,
                wdata=0xA5 << (self.DATA_WIDTH - 8) if we else None,
                label=f'hit{i}')
            sl = self._slice(accept_cyc, rsp_cyc)
            n_fe = len([1 for _, k, _ in sl if k == 'fe_req'])
            self._score(f"hit{i} exactly one fe_req pulse", n_fe, 1)
            states = [p for _, k, p in sl if k == 'state']
            if i == 0:
                self._score("hit0: miss path (FILL_WRITE)",
                            ST_FILL_WRITE in states, True)
            else:
                self._score(f"hit{i}: hit service",
                            (ST_HIT_WR if we else ST_HIT_RD) in states, True)
                self._score(f"hit{i}: no miss machinery",
                            ST_MISS_VICTIM in states
                            and ST_MISS_FILL in states, False)
        # a second write hit on the now-M line (true write hit, no upgrade)
        addr = self._compose_addr(base_tag, 5, beat=1 % self.FILL_BEATS)
        await self._txn(addr, 1, be=0x3, wdata=0x1234, label='hitw')
        # read back the merged bytes (scored inside _txn vs the model)
        await self._txn(self._compose_addr(base_tag, 5), 0, label='hitrb')

    async def _s_miss_sequence(self):
        """Read miss with clean victim and write miss with dirty victim:
        the GAXI boundary sees one request and one response per
        transaction regardless of the internal fill/replay machinery."""
        self._scenario('MissSequence')
        # clean victim: fill one line per way of set 9, then one more
        for w in range(self.WAYS):
            await self._txn(self._compose_addr(0x40 + w, 9), 0,
                            label=f'cl{w}')
        n_ev0 = len(self.events)
        await self._txn(self._compose_addr(0x44, 9), 0, label='clmiss')
        sl = self._slice(self.events[n_ev0][0], self.cyc)
        self._score('clean miss: no drain',
                    any(k == 'drain_start' for _, k, _ in sl), False)
        # dirty victim: write the lines dirty, then miss again
        for w in range(self.WAYS):
            await self._txn(self._compose_addr(0x40 + w, 9), 1,
                            wdata=0xD7 << (self.DATA_WIDTH - 8),
                            label=f'dw{w}')
        n_ev1 = len(self.events)
        await self._txn(self._compose_addr(0x45, 9), 0, label='dwmiss')
        sl = self._slice(self.events[n_ev1][0], self.cyc)
        self._score('dirty miss: drain happened',
                    any(k == 'drain_start' for _, k, _ in sl), True)
        self._score('dirty miss: victim staged',
                    any(k == 'victim_load' for _, k, _ in sl), True)

    async def _s_upgrade_visible_once(self):
        """Write to a Shared line is an upgrade: one GAXI request, one
        response, no fill beats (CLEAN_UNIQUE carries no data)."""
        self._scenario('UpgradeVisibleOnce')
        addr = self._compose_addr(0x50, 11)
        await self._txn(addr, 0, label='up_rd')   # install S (read miss)
        n_ev = len(self.events)
        await self._txn(addr, 1, be=0xF, wdata=0xBEEF, label='up_wr')
        sl = self._slice(self.events[n_ev][0], self.cyc)
        fills = [p for _, k, p in sl if k == 'fill_start']
        self._score('upgrade: exactly one fill_start', len(fills), 1)
        if fills:
            self._score('upgrade: CLEAN_UNIQUE class', fills[0]['class'],
                        ACE_CLEAN_UNIQUE)
        self._score('upgrade: no victim select',
                    any(k == 'victim_load' for _, k, _ in sl), False)

    async def _s_backpressure_held(self):
        """Response held under cpu_rsp_rd_ready low: valid stays high and
        the payload is byte-stable for K cycles before the handshake."""
        self._scenario('BackpressureHeld')
        d = self.dut
        K = 12
        addr = self._compose_addr(0x60, 3)
        # ensure a hit so the response arrives quickly
        await self._txn(addr, 0, label='bp_warm')
        # close the response channel before issuing the measured request
        self.slave.set_ready_policy('stall')
        n_rsp = len(self.rsp_log)
        pkt = self.master.create_packet(
            data=self._pack_req(addr, 0, (1 << self.STRB_W) - 1, 0))
        await self.master.send(pkt)
        # hold ready low and sample K cycles of valid/data
        held = 0
        while True:
            await self._negedge_settled()
            if int(d.cpu_rsp_rd_valid.value):
                break
        exp_data = int(d.cpu_rsp_rd_data.value)
        for _ in range(K):
            self._score('bp: valid held', int(d.cpu_rsp_rd_valid.value), 1)
            self._score('bp: data held', int(d.cpu_rsp_rd_data.value),
                        exp_data)
            held += 1
            await self._negedge_settled()
        self._score('bp: held K cycles', held, K)
        # now accept and finish the transaction
        rsp = await self._accept_rsp_when_valid('bp')
        line = self._line_of(addr)
        beat = (addr >> (self.STRB_W.bit_length() - 1)) & (self.FILL_BEATS - 1)
        self._score('bp: rsp data after hold', rsp[1],
                    self._beat_of_line(self._mem_line(line), beat))
        for _ in range(self.RSP_TIMEOUT_CYCLES):
            if len(self.rsp_log) >= n_rsp + 1:
                break
            await self._negedge_settled()

    async def _s_pipelined_responses(self):
        """Back-to-back requests: while the first response waits
        unaccepted, a second request is accepted and served; responses
        arrive in request order (the D-6 FIFO is depth 2)."""
        self._scenario('PipelinedResponses')
        addr0 = self._compose_addr(0x70, 4)
        addr1 = self._compose_addr(0x71, 4)
        await self._txn(addr0, 0, label='pl_warm0')
        # close the response channel so the first response waits
        self.slave.set_ready_policy('stall')
        # issue request 1 (will miss) and, while its response is stalled,
        # accept request 2
        n_rsp = len(self.rsp_log)
        n_acc = len([1 for _, k, _ in self.events if k == 'accept'])
        pkt1 = self.master.create_packet(
            data=self._pack_req(addr1, 0, (1 << self.STRB_W) - 1, 0))
        await self.master.send(pkt1)
        # wait for the response to be valid and hold it unaccepted
        d = self.dut
        while True:
            await self._negedge_settled()
            if int(d.cpu_rsp_rd_valid.value):
                break
        await self._negedge_settled()
        # request 2 must be accepted while response 1 is still stalled
        pkt2 = self.master.create_packet(
            data=self._pack_req(addr0, 0, (1 << self.STRB_W) - 1, 0))
        send2 = cocotb.start_soon(self.master.send(pkt2))
        for _ in range(self.RSP_TIMEOUT_CYCLES):
            accepts = [e for e in self.events if e[1] == 'accept']
            if len(accepts) >= n_acc + 1:
                break
            await self._negedge_settled()
        self._score('pl: req2 accepted while rsp1 stalled',
                    int(d.cpu_rsp_rd_valid.value)
                    and len(self.rsp_log) == n_rsp, True)
        # now release the bus: both responses arrive in request order
        self.slave.set_ready_policy('always')
        await send2
        for _ in range(self.RSP_TIMEOUT_CYCLES):
            if len(self.rsp_log) >= n_rsp + 2:
                break
            await self._negedge_settled()
        self._score('pl: two responses in order', len(self.rsp_log),
                    n_rsp + 2)
        line1 = self._line_of(addr1)
        beat1 = (addr1 >> (self.STRB_W.bit_length() - 1)) & (self.FILL_BEATS - 1)
        self._score('pl: rsp order data', self.rsp_log[-2][1],
                    self._beat_of_line(self._mem_line(line1), beat1))

    async def _s_snoop_detour(self):
        """Snoop priority is invisible at the GAXI boundary: a request
        presented while a snoop is granted still completes as exactly one
        request / one response with correct data."""
        self._scenario('SnoopDetour')
        addr = self._compose_addr(0x80, 7)
        await self._txn(addr, 0, label='sd_warm')
        # present a snoop for the same line, then immediately a request;
        # the control detours through CTRL_SNOOP and returns to the lookup
        n_rsp = len(self.rsp_log)
        n_acc = len([1 for _, k, _ in self.events if k == 'accept'])
        await self._snoop(0, addr, label='sd_snp')   # READ_SHARED, no stall
        # the snoop above completed before the request; now the overlap
        # case: raise snoop_req and hold it while issuing the request
        d = self.dut
        await self._negedge_settled()
        d.snoop_addr.value = addr
        d.snoop_type.value = 0
        d.snoop_req.value = 1
        await self._negedge_settled()
        pkt = self.master.create_packet(
            data=self._pack_req(addr, 0, (1 << self.STRB_W) - 1, 0))
        send = cocotb.start_soon(self.master.send(pkt))
        # release the snoop once granted
        while True:
            await self._negedge_settled()
            if int(d.snoop_ready.value):
                break
        d.snoop_req.value = 0
        await send
        for _ in range(self.RSP_TIMEOUT_CYCLES):
            if len(self.rsp_log) >= n_rsp + 1:
                break
            await self._negedge_settled()
        accepts = [e for e in self.events if e[1] == 'accept']
        self._score('sd: exactly one accept', len(accepts), n_acc + 1)
        self._score('sd: exactly one response', len(self.rsp_log), n_rsp + 1)
        line = self._line_of(addr)
        beat = (addr >> (self.STRB_W.bit_length() - 1)) & (self.FILL_BEATS - 1)
        self._score('sd: rsp data', self.rsp_log[-1][1],
                    self._beat_of_line(self._mem_line(line), beat))
        # the snoop service must appear around the accept: at full level
        # the master's randomized valid delay can shift the overlap, so
        # the grant may precede the accept
        sl = self._slice(accepts[-1][0] - 60, self.cyc)
        self._score('sd: snoop service on the path',
                    any(k == 'snoop_gnt' for _, k, _ in sl), True)

    async def _s_replay_single_transaction(self):
        """A write miss (fill + D-4 replay) is a single GAXI transaction:
        one accept, one response, and the merged bytes read back
        afterwards."""
        self._scenario('ReplaySingleTransaction')
        addr = self._compose_addr(0x90, 13, beat=2 % self.FILL_BEATS)
        wdata = random.getrandbits(self.DATA_WIDTH)
        accept_cyc, rsp_cyc, _ = await self._txn(addr, 1, be=0xFF, wdata=wdata,
                                                 label='wr_miss')
        sl = self._slice(accept_cyc, rsp_cyc)
        self._score('wr_miss: FILL_WRITE on path',
                    ST_FILL_WRITE in [p for _, k, p in sl if k == 'state'],
                    True)
        self._score('wr_miss: REPLAY on path',
                    ST_REPLAY in [p for _, k, p in sl if k == 'state'], True)
        n_acc = len([1 for _, k, _ in self.events if k == 'accept'])
        self._score('wr_miss: still one accept total at this point',
                    n_acc >= 1, True)
        # read back the same beat: fill data with the write bytes merged
        await self._txn(self._compose_addr(0x90, 13, beat=2 % self.FILL_BEATS),
                        0, label='wr_rb')
        line = self._line_of(addr)
        beat = (addr >> (self.STRB_W.bit_length() - 1)) & (self.FILL_BEATS - 1)
        ml = self._mem_line(line)
        lo = beat * self.STRB_W
        self._score('wr_rb: model merged byte', ml[lo],
                    wdata & 0xFF)

    async def _s_ready_only_idle(self):
        """EVERY-CYCLE invariant during a busy phase: cpu_req_wr_ready
        implies CTRL_IDLE + control ready; during a miss sequence ready
        stays low cycle after cycle (blocking contract, MAS ch02/09)."""
        self._scenario('ReadyOnlyIdle')
        d = self.dut
        # start a miss transaction and sample every cycle until response
        addr = self._compose_addr(0xA0, 21)
        n_rsp = len(self.rsp_log)
        pkt = self.master.create_packet(
            data=self._pack_req(addr, 0, (1 << self.STRB_W) - 1, 0))
        send = cocotb.start_soon(self.master.send(pkt))
        samples = 0
        low_while_busy = 0
        while len(self.rsp_log) < n_rsp + 1:
            await self._negedge_settled()
            ready = int(d.cpu_req_wr_ready.value)
            state = int(d.ctrl_state.value)
            if ready:
                self._score('roi: ready implies IDLE', state, ST_IDLE)
                self._score('roi: ready implies control ready',
                            int(d.ctrl_req_ready.value), 1)
            else:
                if state != ST_IDLE:
                    low_while_busy += 1
            samples += 1
            if samples > self.RSP_TIMEOUT_CYCLES:
                raise RuntimeError('roi: response timeout')
        await send
        self._score('roi: busy phase sampled', samples > 4, True)
        self._score('roi: ready low through non-IDLE',
                    low_while_busy > 0, True)

    async def _s_full_soak(self):
        """Randomized soak: random addresses (mixed hits/misses/upgrades),
        random be/wdata, randomized valid and ready delays; every response
        scored against the content model."""
        self._scenario('FullSoak')
        n = self.FULL_TXN[self.TEST_LEVEL]
        for i in range(n):
            tag = random.randrange(1, 1 << (self.ADDR_WIDTH - self.SET_BITS
                                            - self.OFFSET_BITS))
            set_idx = random.randrange(self.SETS)
            beat = random.randrange(self.FILL_BEATS)
            addr = self._compose_addr(tag, set_idx, beat)
            we = random.random() < 0.5
            await self._txn(addr, we, label=f'soak{i}')
            if i % 500 == 0:
                self.mark_progress(f"soak {i}/{n}")
        # final balance: every accepted request got exactly one response
        n_acc = len([1 for _, k, _ in self.events if k == 'accept'])
        self._score('soak: responses == accepts', len(self.rsp_log), n_acc)

    # ------------------------------------------------------------------
    # reset (used by the monlite present-vs-absent double run)
    # ------------------------------------------------------------------
    async def _reset_dut(self):
        """Assert reset long enough to restart the INIT walk, restart the
        models, and let the BFMs settle. Used between the two runs of the
        present-vs-absent comparison."""
        d = self.dut
        self.slave.set_ready_policy('always')
        await self.assert_reset()
        await self.wait_clocks('clk', 8)
        await self.deassert_reset()
        self.mem = {}
        self.events = []
        self.rsp_log = []
        self.txns = 0
        self.snoops = 0
        self.cyc = 0
        # wait out the INIT walk before stimulus restarts
        while True:
            await self._negedge_settled()
            if not int(d.init_busy.value):
                break

    # ------------------------------------------------------------------
    # run
    # ------------------------------------------------------------------
    async def run(self):
        await self._s_init_ready()
        if self.TEST_LEVEL == 'gate':
            await self._s_hit_sequence()
            await self._s_miss_sequence()
            await self._s_upgrade_visible_once()
            await self._s_ready_only_idle()
        elif self.TEST_LEVEL == 'func':
            await self._s_hit_sequence()
            await self._s_miss_sequence()
            await self._s_upgrade_visible_once()
            await self._s_backpressure_held()
            await self._s_pipelined_responses()
            await self._s_snoop_detour()
            await self._s_replay_single_transaction()
            await self._s_ready_only_idle()
        else:
            await self._s_hit_sequence()
            await self._s_miss_sequence()
            await self._s_upgrade_visible_once()
            await self._s_backpressure_held()
            await self._s_pipelined_responses()
            await self._s_snoop_detour()
            await self._s_replay_single_transaction()
            await self._s_ready_only_idle()
            await self._s_full_soak()
        # global handshake balance
        n_acc = len([1 for _, k, _ in self.events if k == 'accept'])
        n_fe = len([1 for _, k, _ in self.events if k == 'fe_req'])
        self._score('global: fe_req pulses == accepts', n_fe, n_acc)
        self._score('global: responses == accepts', len(self.rsp_log), n_acc)
        return self.mismatches == 0

    def get_test_report(self):
        return {
            'checks': self.checks,
            'mismatches': self.mismatches,
            'txns': self.txns,
            'snoops': self.snoops,
            'packets': self.packets,
            'dropped': self.dropped,
            'scenarios': self.scenarios,
            'seed': self.SEED,
            'level': self.TEST_LEVEL,
        }
