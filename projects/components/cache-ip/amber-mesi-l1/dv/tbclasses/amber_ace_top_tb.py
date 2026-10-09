"""
amber_ace_top testbench

Task 12: the onyx-rig top on ACE masters. One amber_ace_top (amber_core +
amber_ace_issue + the axi4ace_master_rd/wr_monlite transports + the D-7
monbus_arbiter) against a Python model of the onyx D2 manager: the ACE
master pins (AR+ARSNOOP/R, AW+AWSNOOP/W/B, auto-pulsed RACK/WACK) are
closed by hand-rolled GAXI responders over the shared MemoryModel; the ACE
snoop responder port is driven by the house snoop master; the CPU side by
the house GAXI BFM pair. What this suite pins ON TOP of the amber_core
integration contract (the model machinery is inherited from AmberCoreTB):

  * Table 2.8.1 row-by-row on the master pins: a read miss drives AR with
    ARSNOOP=ReadShared; a write miss drives AR with ARSNOOP=ReadUnique; an
    S->M upgrade originates an AW-only CleanUnique (no W beats, B returned
    and swallowed by the ace_issue BID mux); a dirty eviction drives AW
    with AWSNOOP=WriteBack and a W burst carrying the victim bytes; every
    AWSNOOP/ARSNOOP value and the address/burst pairing is captured per
    handshake and cross-checked against the model's transaction ledger.
    (MakeUnique/Evict rows: the control never emits those events -- it
    maps whole-line write misses to ReadUnique+merge and clean evictions
    are silent drops -- so their pin-level evidence is the
    test_amber_ace_issue_rows unit suite; this suite asserts the rig never
    issues them.)
  * AW-only B responses never reach the drain engine (the AWONLY_ID BID
    mux), so WriteBack B credits always retire the right drain.
  * RACK/WACK auto-pulse accounting: one RACK per R burst one cycle after
    the last-beat handshake; one WACK per B handshake.
  * The full inherited contract: init walk, first-hit latency, directed
    sequence (miss/hit/upgrade/merge/dirty-eviction with memory audit),
    directed snoops, randomized oracle lockstep with mid-miss snoops,
    MonBus tally cross-check, congestion drop-and-count, and the framework
    ACE compliance checker fed from the snoop-responder pins.

Geometries: tiny formal config (16 sets / 2 ways) + pkg default (128/4);
64-bit bus / 64 B lines per the macro-ladder convention. Levels per the
house grid: gate / func / full. A USE_MONITOR=0 gate cell per geometry
re-runs the suite asserting observer non-perturbation.

Author: RTL Design Sherpa
Created: 2026-10-09
"""

import os

import cocotb
from cocotb.triggers import FallingEdge, Timer

from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.shared.field_config import FieldConfig
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.ace.ace_compliance_checker import (
    ACEComplianceChecker,
)
from CocoTBFramework.components.ace.ace_field_configs import (
    AXI4ACEFieldConfigHelper,
)
from CocoTBFramework.components.ace.ace_factories import (
    create_axi4ace_snoop_master,
)
from CocoTBFramework.components.ace.ace_transaction import (
    SnoopType,
    CRRESP,
)

from projects.components.cache_ip.amber_mesi_l1.dv.tbclasses.amber_core_tb import (
    AmberCoreTB,
    _parse_packet,
    ST_ERROR,
    EV_DROPPED,
    EV_NAMES,
)

# Table 2.8.1 snoop-field encodings (amber_ace_issue localparams, mirrored
# as the golden)
ARSNOOP_READ_SHARED = 0x1
ARSNOOP_READ_UNIQUE = 0x7
AWSNOOP_CLEAN_UNIQUE = 0x6
AWSNOOP_MAKE_UNIQUE = 0x4
AWSNOOP_WRITE_BACK = 0x3
AWSNOOP_EVICT = 0x5
AWSNOOP_LEGAL = {AWSNOOP_CLEAN_UNIQUE, AWSNOOP_MAKE_UNIQUE,
                 AWSNOOP_WRITE_BACK, AWSNOOP_EVICT}
ARSNOOP_LEGAL = {ARSNOOP_READ_SHARED, ARSNOOP_READ_UNIQUE}

# amber_ace_req_t (amber_pkg) on the coh_req sideband
ACE_READ_SHARED, ACE_READ_UNIQUE, ACE_CLEAN_UNIQUE, ACE_MAKE_UNIQUE, \
    ACE_WRITE_BACK, ACE_EVICT = range(6)

# the ace_issue AWONLY_ID parameter (the AW-only BID tag)
AWONLY_ID = 0x01

_SNOOP_CODES = [int(t) for t in SnoopType]


class AmberAceTopTB(AmberCoreTB):
    """The amber_ace_top rig: one ACE cache against the onyx-D2 manager
    model, scoring the inherited integration contract plus the Table 2.8.1
    master-pin behavior."""

    # the rig top speaks the MAS ch01/02 port names
    CLK_PORT = 'aclk'
    RST_PORT = 'aresetn'
    MON_TIME_PORT = 'i_mon_time'

    @property
    def _tap(self):
        return self.dut.u_core

    def __init__(self, dut, **kwargs):
        super().__init__(dut, **kwargs)
        self.USE_MONITOR = os.environ.get('USE_MONITOR', '1') == '1'

        # the ACE suite runs BOTH directed families (its own Table 2.8.1
        # rows plus the inherited sequence/snoop/latency families), so the
        # directed tag budget needs more headroom than the base span
        # gives; the working set grows accordingly
        self.SPAN = min(max(self.SETS * 24, 64), 12288)
        self.MAX_TAG = (self.SPAN >> self.SET_BITS) - 1

        # master-pin capture ledgers (filled by the manager callbacks)
        self.ar_log = []          # {cyc, addr, len, snoop}
        self.aw_log = []          # {cyc, addr, len, snoop, id}
        self.w_log = []           # [{'beats': [...]}] per completed burst
        self.b_count = 0
        self.rack_count = 0
        self.wack_count = 0
        self._open_wbs = []       # WriteBack AWs awaiting their W burst
        self._w_bursts_pending = []  # completed W bursts awaiting their AW
        self._w_cur_burst = None  # W beats of the burst in flight

        # framework ACE compliance checker (snoop responder pins)
        self.ace_checker = ACEComplianceChecker(log=self.log)
        self._ace_seq = 0
        self._cd_seq = 0
        self._cd_started = False
        self._cur_ac_snoop = None

        # observer drop accounting: report packets carry the saturating
        # count of drops since the previous report (the pair-rig tally
        # rule reconciles against this; the merged bus adds arbiter
        # latency, so pre-congestion drops are possible at rig level)
        self._drop_reports = 0
        self._drops_reported = 0

    # ------------------------------------------------------------------
    # clock/reset/BFMs: the CPU and snoop closures are inherited; the
    # memory side is the onyx-D2 manager model on the ACE master pins
    # ------------------------------------------------------------------
    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock(self.CLK_PORT, freq=period_ns, units='ns')
        d = self.dut
        clk = getattr(d, self.CLK_PORT)

        req_fields = FieldConfig.from_dict(
            field_dict={'data': {'bits': self.CPU_REQ_W, 'default': 0}},
            lsb_first=True)
        rsp_fields = FieldConfig.from_dict(
            field_dict={'data': {'bits': self.BUS_WIDTH, 'default': 0}},
            lsb_first=True)

        zero_delay = FlexRandomizer({'valid_delay': ([(0, 0)], [1])})
        soak_delay = FlexRandomizer(
            {'valid_delay': ([(0, 0), (1, 3), (4, 10)], [6, 3, 1])})
        master_rand = soak_delay if self.TEST_LEVEL == 'full' else zero_delay

        self.master = GAXIMaster(
            dut=d, title='cpu_req', prefix='',
            clock=clk, field_config=req_fields,
            timeout_cycles=self.RSP_TIMEOUT_CYCLES,
            mode='skid', bus_name='cpu_req_wr', pkt_prefix='',
            multi_sig=False, randomizer=master_rand, log=self.log)
        self.slave = GAXISlave(
            dut=d, title='cpu_rsp', prefix='',
            clock=clk, field_config=rsp_fields,
            timeout_cycles=self.RSP_TIMEOUT_CYCLES,
            mode='skid', bus_name='cpu_rsp_rd', pkt_prefix='',
            multi_sig=False,
            randomizer=FlexRandomizer({'ready_delay': ([(0, 0)], [1])}),
            log=self.log)
        self.slave.add_callback(self._on_rsp)
        self.slave.set_ready_policy('always')

        # the onyx-D2 manager model on the ACE master pins. The framework
        # has no front-side ACE slave responder (onyx itself is not built
        # yet) -- the rig stands one up from raw GAXI channels with the ACE
        # field configs, using the plain AXI4 protocol patterns (the snoop
        # field is inert payload to the channel movers).
        self.ar_slave = GAXISlave(
            dut=d, title='AR_mgr', prefix='m_axi_', clock=clk,
            field_config=AXI4ACEFieldConfigHelper.create_ar_field_config(
                8, self.ADDR_WIDTH, 1),
            pkt_prefix='ar', multi_sig=True,
            protocol_type='axi4_ar_slave', log=self.log)
        self.r_master = GAXIMaster(
            dut=d, title='R_mgr', prefix='m_axi_', clock=clk,
            field_config=AXI4ACEFieldConfigHelper.create_r_field_config(
                8, self.BUS_WIDTH, 1),
            pkt_prefix='r', multi_sig=True,
            protocol_type='axi4_r_master', log=self.log,
            super_debug=True)
        self.aw_slave = GAXISlave(
            dut=d, title='AW_mgr', prefix='m_axi_', clock=clk,
            field_config=AXI4ACEFieldConfigHelper.create_aw_field_config(
                8, self.ADDR_WIDTH, 1),
            pkt_prefix='aw', multi_sig=True,
            protocol_type='axi4_aw_slave', log=self.log)
        self.w_slave = GAXISlave(
            dut=d, title='W_mgr', prefix='m_axi_', clock=clk,
            field_config=AXI4ACEFieldConfigHelper.create_w_field_config(
                self.BUS_WIDTH, 1),
            pkt_prefix='w', multi_sig=True,
            protocol_type='axi4_w_slave', log=self.log)
        self.b_master = GAXIMaster(
            dut=d, title='B_mgr', prefix='m_axi_', clock=clk,
            field_config=AXI4ACEFieldConfigHelper.create_b_field_config(
                8, 1),
            pkt_prefix='b', multi_sig=True,
            protocol_type='axi4_b_master', log=self.log)
        self.ar_slave.add_callback(self._on_ar_accept)
        self.aw_slave.add_callback(self._on_aw_accept)
        self.w_slave.add_callback(self._on_w_beat)

        # ACE snoop master on the snoop responder port
        self.snoop_master = create_axi4ace_snoop_master(
            dut=d, clock=clk, prefix='m_axi_', log=self.log,
            ifc_name='sn', addr_width=self.ADDR_WIDTH,
            data_width=self.BUS_WIDTH)['interface']

        # monbus
        d.mon_ready.value = 1

        # deterministic memory content across the working set
        for line in range(self.SPAN):
            self.memory_model.write(self._base_of(line),
                                    bytearray(self._default_line(line)))

        await self.assert_reset()
        cocotb.start_soon(self._monitor())
        cocotb.start_soon(self._monbus_ready_driver())
        cocotb.start_soon(self._rackwack_observer())
        await self.wait_clocks(self.CLK_PORT, 3)
        await self.deassert_reset()
        self.set_profile('fast')

    # ------------------------------------------------------------------
    # manager model: AR -> R burst from memory; AW -> WriteBack (W+B) or
    # AW-only (B immediately, no W)
    # ------------------------------------------------------------------
    def _fields(self, packet):
        return getattr(packet, 'fields', {}) or {}

    def _on_ar_accept(self, packet):
        f = self._fields(packet)
        addr = int(f.get('addr', 0))
        length = int(f.get('len', 0)) + 1
        snoop = int(f.get('snoop', 0))
        rid = int(f.get('id', 0))
        self.ar_log.append({'cyc': self.cyc, 'addr': addr,
                            'len': length, 'snoop': snoop})
        self._score("AR: line-aligned address", addr & (self.LINE_BYTES - 1),
                    0)
        self._score("AR: whole-line burst", length, self.FILL_BEATS)
        self._score("AR: snoop is a D2 read type", snoop in ARSNOOP_LEGAL,
                    True)
        cocotb.start_soon(self._serve_read(rid, addr, length))

    async def _serve_read(self, rid, addr, length):
        packets = []
        for i in range(length):
            data = self.memory_model.read(addr + i * self.STRB_W,
                                          self.STRB_W)
            packets.append(self.r_master.create_packet(
                id=rid, data=int.from_bytes(bytes(data), 'little'),
                resp=0, last=1 if i == length - 1 else 0, user=0))
        await self.r_master.send_burst(packets)

    def _on_aw_accept(self, packet):
        f = self._fields(packet)
        addr = int(f.get('addr', 0))
        length = int(f.get('len', 0)) + 1
        snoop = int(f.get('snoop', 0))
        awid = int(f.get('id', 0))
        self.aw_log.append({'cyc': self.cyc, 'addr': addr,
                            'len': length, 'snoop': snoop, 'id': awid})
        self._score("AW: line-aligned address", addr & (self.LINE_BYTES - 1),
                    0)
        self._score("AW: whole-line burst", length, self.FILL_BEATS)
        self._score("AW: snoop is a D2 write type", snoop in AWSNOOP_LEGAL,
                    True)
        if snoop == AWSNOOP_WRITE_BACK:
            # the W burst may already be complete (the transport's AW and
            # W skids are independent and the engine enters D_W the cycle
            # its AW is accepted -- a stalled m_axi AW lets the whole W
            # burst pass it): pair by ORDER, not by arrival
            self._open_wbs.append({'addr': addr, 'len': length, 'id': awid})
            self._pair_wb_burst()
        else:
            # AW-only transaction (CleanUnique / MakeUnique / Evict): the
            # manager answers B straight off the AW; no W data follows.
            cocotb.start_soon(self._send_b(awid))

    def _on_w_beat(self, packet):
        f = self._fields(packet)
        data = int(f.get('data', 0))
        last = int(f.get('last', 0))
        if self._w_cur_burst is None:
            self._w_cur_burst = []
        self._w_cur_burst.append(data)
        if last:
            self._w_bursts_pending.append(self._w_cur_burst)
            self._w_cur_burst = None
            self._pair_wb_burst()

    def _pair_wb_burst(self):
        while self._open_wbs and self._w_bursts_pending:
            wb = self._open_wbs.pop(0)
            beats = self._w_bursts_pending.pop(0)
            self.w_log.append({'beats': beats})
            self._score("W: whole-line victim burst", len(beats), wb['len'])
            for i, beat in enumerate(beats):
                self.memory_model.write(
                    wb['addr'] + i * self.STRB_W,
                    bytearray(beat.to_bytes(self.STRB_W, 'little')))
            cocotb.start_soon(self._send_b(wb['id']))

    async def _send_b(self, bid):
        await self.b_master.send(self.b_master.create_packet(
            id=bid, resp=0, user=0))
        self.b_count += 1

    # ------------------------------------------------------------------
    # monitor: the base tap-routed monitor + RACK/WACK pulses + the ACE
    # compliance taps on the snoop responder pins
    # ------------------------------------------------------------------
    async def _rackwack_observer(self):
        d = self.dut
        clk = getattr(d, self.CLK_PORT)
        prev = (0, 0)
        while True:
            await FallingEdge(clk)
            await Timer(100, units='ps')
            rack = int(d.m_axi_rack.value)
            wack = int(d.m_axi_wack.value)
            if rack and not prev[0]:
                self.rack_count += 1
            if wack and not prev[1]:
                self.wack_count += 1
            prev = (rack, wack)

    async def _monitor(self):
        # the base monitor (state entries, accepts, coh_req taps, snoop
        # grant model-step, monbus tally) plus the compliance taps
        d = self.dut
        clk = getattr(d, self.CLK_PORT)
        prev_state = -1
        while True:
            await FallingEdge(clk)
            await Timer(100, units='ps')
            self.cyc += 1
            getattr(d, self.MON_TIME_PORT).value = self.cyc
            self.ace_checker.tick()

            st = int(d.ctrl_state.value)
            if st != prev_state:
                self.events.append((self.cyc, 'state', st))
                self._on_state_entry(st)
                prev_state = st

            if int(d.cpu_req_wr_valid.value) and int(d.cpu_req_wr_ready.value):
                packed = int(d.cpu_req_wr_data.value)
                wdata = packed & ((1 << self.BUS_WIDTH) - 1)
                be = (packed >> self.BUS_WIDTH) & ((1 << self.STRB_W) - 1)
                we = (packed >> (self.BUS_WIDTH + self.STRB_W)) & 1
                addr = (packed >> (self.BUS_WIDTH + self.STRB_W + 1)) \
                    & ((1 << self.ADDR_WIDTH) - 1)
                self.events.append((self.cyc, 'accept',
                                    {'addr': addr, 'we': we, 'be': be,
                                     'wdata': wdata}))

            if int(self._tap.coh_req_valid.value):
                self.coh_req_count += 1
                self.events.append((self.cyc, 'coh_req', {
                    'addr': int(self._tap.coh_req_addr.value),
                    'type': int(self._tap.coh_req_type.value)}))

            if int(self._tap.u_snoop.ctrl_snoop_req.value) \
                    and int(self._tap.u_control.ctrl_snoop_ready.value):
                self._on_snoop_grant(st)

            if int(d.mon_valid.value) and int(d.mon_ready.value):
                p = _parse_packet(int(d.mon_packet.value))
                if p['unit_id'] == 1:   # amber_monlite stream only (the
                    self.pkt_counts[p['event_code']] += 1   # rd/wr monlite
                    if p['event_code'] == EV_DROPPED:       # packets share
                        self._drop_reports += 1             # the bus)
                        self._drops_reported += p['data'] & 0xFF

            self._ace_compliance_taps()

    def _ace_compliance_taps(self):
        """Feed the framework ACE compliance checker from the snoop
        responder pins (the pair-rig idiom, one cache)."""
        d = self.dut
        if int(d.m_axi_acvalid.value) and int(d.m_axi_acready.value):
            snoop = int(d.m_axi_acsnoop.value)
            self._cur_ac_snoop = SnoopType(snoop) \
                if snoop in _SNOOP_CODES else None
        if int(d.m_axi_cdvalid.value) and int(d.m_axi_cdready.value):
            if not self._cd_started:
                self._cd_started = True
                exp = self.grant_log[-1] if self.grant_log else None
                if exp is not None and (exp['exp_crresp'] >> 0) & 1:
                    self.ace_checker.set_expected_cd_beats(self.FILL_BEATS)
            last = int(d.m_axi_cdlast.value)
            self.ace_checker.check_cd_order(self._cd_seq, last)
            if last:
                self._cd_seq += 1
                self._cd_started = False
        if int(d.m_axi_crvalid.value) and int(d.m_axi_crready.value):
            crresp = CRRESP(int(d.m_axi_crresp.value))
            stype = self._cur_ac_snoop
            self.ace_checker.check_cr_order(self._ace_seq)
            if stype is not None:
                self.ace_checker.check_crresp_validity(crresp, stype)
            self._ace_seq += 1

    # ------------------------------------------------------------------
    # MonBus tally: the merged bus adds arbiter+skid latency, so the
    # observer can drop pre-congestion; the pair-rig rule reconciles
    # totals against the reported drop count. USE_MONITOR=0 re-runs
    # assert observer silence.
    # ------------------------------------------------------------------
    def _check_tally(self):
        if not self.USE_MONITOR:
            for ev in EV_NAMES:
                self._score(f"nomon: {EV_NAMES[ev]} packets silent",
                            self.pkt_counts[ev], 0)
            self._score("nomon: no drop reports",
                        self._drop_reports, 0)
            self._score("nomon: dropped_count stays zero",
                        int(self._tap.mon_dropped.value), 0)
            return
        if self._drops_reported == 0:
            # no observer drops: the per-class stream is exact
            for ev in EV_NAMES:
                if ev == EV_DROPPED:
                    continue
                self._score(f"monbus tally {EV_NAMES[ev]}",
                            self.pkt_counts[ev], self.tally[ev])
        else:
            # drops: the per-class breakdown is unrecoverable, the TOTAL
            # reconciles exactly
            got = sum(self.pkt_counts[ev] for ev in EV_NAMES
                      if ev != EV_DROPPED) + self._drops_reported
            exp = sum(self.tally[ev] for ev in EV_NAMES if ev != EV_DROPPED)
            self._score(f"monbus tally reconciled with "
                        f"{self._drops_reported} drops", got, exp)

    # ------------------------------------------------------------------
    # Table 2.8.1 pin-level cross-check against the coherence ledger
    # ------------------------------------------------------------------
    def _coh_req_counts(self):
        counts = {t: 0 for t in range(6)}
        for _, kind, p in self.events:
            if kind == 'coh_req':
                counts[p['type']] += 1
        return counts

    def _check_ace_pins(self):
        cr = self._coh_req_counts()
        rs_ars = [e for e in self.ar_log
                  if e['snoop'] == ARSNOOP_READ_SHARED]
        ru_ars = [e for e in self.ar_log
                  if e['snoop'] == ARSNOOP_READ_UNIQUE]
        wb_aws = [e for e in self.aw_log
                  if e['snoop'] == AWSNOOP_WRITE_BACK]
        cu_aws = [e for e in self.aw_log
                  if e['snoop'] == AWSNOOP_CLEAN_UNIQUE]
        mu_aws = [e for e in self.aw_log
                  if e['snoop'] == AWSNOOP_MAKE_UNIQUE]
        ev_aws = [e for e in self.aw_log
                  if e['snoop'] == AWSNOOP_EVICT]

        # one AR per fill launch, snoop matching the launch class
        self._score("pins: ReadShared ARs == READ_SHARED launches",
                    len(rs_ars), cr[ACE_READ_SHARED])
        self._score("pins: ReadUnique ARs == READ_UNIQUE launches",
                    len(ru_ars), cr[ACE_READ_UNIQUE])
        self._score("pins: one AR per fill launch",
                    len(self.ar_log),
                    cr[ACE_READ_SHARED] + cr[ACE_READ_UNIQUE])
        # one WriteBack AW per drain launch
        self._score("pins: WriteBack AWs == WRITE_BACK launches",
                    len(wb_aws), cr[ACE_WRITE_BACK])
        # one AW-only CleanUnique per upgrade launch
        self._score("pins: CleanUnique AWs == CLEAN_UNIQUE launches",
                    len(cu_aws), cr[ACE_CLEAN_UNIQUE])
        # MakeUnique / Evict: the control never emits them at rig level
        self._score("pins: no MakeUnique at rig level", len(mu_aws), 0)
        self._score("pins: no Evict at rig level", len(ev_aws), 0)
        # the manager answered every AW (WB + AW-only) with a B, and every
        # B earned exactly one WACK
        self._score("pins: one B per AW", self.b_count, len(self.aw_log))
        self._score("pins: one WACK per B", self.wack_count, self.b_count)
        # one RACK per AR burst
        self._score("pins: one RACK per AR", self.rack_count, len(self.ar_log))
        # W bursts pair only with WriteBack AWs
        self._score("pins: one W burst per WriteBack",
                    len(self.w_log), len(wb_aws))
        # AW-only CleanUnique: W beats exist only as write-back victim
        # data -- the total beat count is exactly WB count x whole line
        total_beats = sum(len(b['beats']) for b in self.w_log)
        self._score("pins: W beats only carry write-backs",
                    total_beats, len(wb_aws) * self.FILL_BEATS)

    def _check_ace_compliance(self):
        rep = self.ace_checker.get_compliance_report()
        self._score("ACE compliance: no violations",
                    rep['total_violations'], 0)
        if rep['total_violations']:
            self.log.error(f"ACE violations: {rep['violations']}")

    # ------------------------------------------------------------------
    # directed scenario: the Table 2.8.1 rows end-to-end (unit-suite
    # companion; MakeUnique/Evict rows are asserted absent here)
    # ------------------------------------------------------------------
    async def _s_ace_table_rows(self):
        sset = 3 % self.SETS
        # (a) read miss, shared intent -> ReadShared
        t = self._dtag()
        base = self._compose_addr(t, sset)
        n_ar = len(self.ar_log)
        await self._txn(base, 0, label='t_rs')
        e = self.ar_log[n_ar]
        self._score("t_rs: arsnoop", e['snoop'], ARSNOOP_READ_SHARED)
        self._score("t_rs: araddr line base", e['addr'],
                    self._base_of(self._line_of(base)))

        # (b) write miss, exclusive intent -> ReadUnique (fetch + merge)
        t = self._dtag()
        base = self._compose_addr(t, sset)
        n_ar = len(self.ar_log)
        await self._txn(base, 1, be=(1 << self.STRB_W) - 1,
                        wdata=0x5A5A_0000_0000_0000
                        & ((1 << self.BUS_WIDTH) - 1), label='t_ru')
        e = self.ar_log[n_ar]
        self._score("t_ru: arsnoop", e['snoop'], ARSNOOP_READ_UNIQUE)
        await self._txn(base, 0, label='t_ru_rb')

        # (c) write to Shared line -> AW-only CleanUnique, no W beats
        t = self._dtag()
        base = self._compose_addr(t, sset)
        line = self._line_of(base)
        await self._txn(base, 0, label='t_cu_rd')
        n_aw = len(self.aw_log)
        n_w = sum(len(b['beats']) for b in self.w_log)
        n_b = self.b_count
        n_wack = self.wack_count
        await self._txn(base, 1, be=0x9,
                        wdata=0x00C7_0000_0000_0000
                        & ((1 << self.BUS_WIDTH) - 1), label='t_cu')
        e = self.aw_log[n_aw]
        self._score("t_cu: awsnoop", e['snoop'], AWSNOOP_CLEAN_UNIQUE)
        self._score("t_cu: awaddr line base", e['addr'],
                    self._base_of(line))
        self._score("t_cu: AW carries the AW-only id", e['id'], AWONLY_ID)
        self._score("t_cu: no W beats with the AW-only",
                    sum(len(b['beats']) for b in self.w_log), n_w)
        # the manager's B and the auto-pulsed WACK follow asynchronously
        # (the cache never waits for them): poll, then score
        for _ in range(self.RSP_TIMEOUT_CYCLES):
            if self.b_count >= n_b + 1 and self.wack_count >= n_wack + 1:
                break
            await self._negedge_settled()
        self._score("t_cu: manager returned B", self.b_count, n_b + 1)
        self._score("t_cu: WACK auto-pulsed for the AW-only B",
                    self.wack_count, n_wack + 1)
        await self._txn(base, 0, label='t_cu_rb')

        # (d) dirty eviction -> WriteBack carrying the victim line
        vtags = [self._dtag() for _ in range(self.WAYS)]
        for w, tag in enumerate(vtags):
            a = self._compose_addr(tag, sset)
            await self._txn(a, 0, label=f't_wb_r{w}')
            await self._txn(a, 1, be=(1 << self.STRB_W) - 1,
                            wdata=(0xB0 + w) * 0x0101_0101_0101_0101
                            & ((1 << self.BUS_WIDTH) - 1),
                            label=f't_wb_w{w}')
        victims = {}
        for (s, w), line in self.tags.items():
            if s == sset and self.slot_state.get((s, w)) == 'M':
                victims[line] = bytes(self.cache_data[line])
        n_aw = len(self.aw_log)
        n_wburst = len(self.w_log)
        await self._txn(self._compose_addr(self._dtag(), sset), 0,
                        label='t_wb_evict')
        e = self.aw_log[n_aw]
        self._score("t_wb: awsnoop", e['snoop'], AWSNOOP_WRITE_BACK)
        self._score("t_wb: one W burst", len(self.w_log), n_wburst + 1)
        # the W beats carry the evicted lines' merged bytes: audit memory
        for line, content in victims.items():
            if self._installed_state(line) != 'I':
                continue
            self._score(f"t_wb: victim {line:#x} written back",
                        self._mem_line(line), content)

        self._scenario('AceTableRows')

    # ------------------------------------------------------------------
    # top-level run
    # ------------------------------------------------------------------
    async def run(self):
        await self._s_init_walk()
        await self._s_first_hit_latency()
        await self._s_ace_table_rows()
        await self._s_directed_sequence()
        await self._s_snoop_sequence()

        if self.TEST_LEVEL in ('func', 'full'):
            await self._random_lockstep(self.FULL_TXN[self.TEST_LEVEL])
            self._scenario('RandomOracleLockstep')

        # settle: the merged MonBus carries arbiter+skid latency beyond
        # the observer queue the core TB scores against, so the last
        # packets of the final scenario may still be in flight when the
        # scenario returns -- drain before the tally cross-check
        await self.wait_clocks(self.CLK_PORT, 30)

        # cross-checks on everything observed so far
        self._check_tally()
        self._check_coh_req()
        self._check_ace_pins()
        self._check_ace_compliance()
        self._scenario('AcePinCrossCheck')

        if self.TEST_LEVEL in ('func', 'full'):
            await self._s_monbus_congestion()

        # quiescence: nothing dangling
        await self.wait_clocks(self.CLK_PORT, 10)
        self._score("quiescent: no monbus valid at end",
                    int(self.dut.mon_valid.value), 0)
        self._score("quiescent: ctrl not in ERROR",
                    int(self.dut.ctrl_state.value) == ST_ERROR, False)
        return self.mismatches == 0

    def get_test_report(self):
        report = super().get_test_report()
        report.update({
            'ars': len(self.ar_log),
            'aws': len(self.aw_log),
            'w_bursts': len(self.w_log),
            'bs': self.b_count,
            'racks': self.rack_count,
            'wacks': self.wack_count,
            'ace_compliance': self.ace_checker.get_compliance_report(),
        })
        return report
