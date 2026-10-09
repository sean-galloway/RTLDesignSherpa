"""
amber_eviction_macro testbench -- macro suite 3: eviction/writeback group

Task 9.5 macro composition: the DUT is the wrapper
amber_eviction_macro_test -- REAL amber_control (with the victim depth-1
leaf) + landed tag/data/repl arrays + REAL amber_drain on its house
axi4_master_wr transport, memory side closed by the house AXI4 slave
responder on the wrapper's m_axi AW/W/B pins. Fill stays a timing stub
(D-12, the control suite's fill model); snoops enter on the
control-facing pins.

The class reuses the landed control TB machinery (AmberControlTB: golden
models, monitors, oracle lockstep scorer, the victim-buffer EVERY-CYCLE
invariants, the victim snoop suite) with the golden memory made
write-through into the responder MemoryModel. The drain partner stub is
retired: drain_done is an engine output now, and the drain window the
mid-drain snoop compositions need is widened with a delayed-B responder
profile instead of the stub's fixed latency.

Macro-specific pins (what the stub could not check):
  * WritebackRoundTrip (gate): a dirty eviction drives the real AW/W/B
    burst -- awaddr/awlen/awsize/awburst observed at m_axi, exactly
    FILL_BEATS W beats, B handshake STRICTLY before drain_done, payload
    audit in the MemoryModel, refetch returns the written-back bytes;
  * VictimBufferDirected (func): the inherited VictimBufferHandshake
    window endpoints, with the leaf holding through the REAL drain;
  * SnoopDrainingVictim / SnoopStaleVictimMidFill (func): the inherited
    compositions, the drain kept outstanding with a delayed-B profile;
  * DrainBackpressureDrain (func): a dirty eviction through the slow
    responder profile (AW/W ready stalls + B latency) -- payload intact;
  * EvictionSoak (func/full): randomized write-heavy traffic over a
    bounded working set -- many dirty victims through the real engine.

Levels (TEST_LEVEL):
  gate  -- InitWalk + WritebackRoundTrip
  func  -- + VictimBufferDirected + the victim snoop compositions +
           DrainBackpressureDrain + EvictionSoak
  full  -- deeper soak (sign-off scale)

Author: RTL Design Sherpa
Created: 2026-10-08
"""

import random

import cocotb
from cocotb.triggers import Timer

from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.axi4.axi4_factories import (
    create_axi4_slave_wr,
)

from projects.components.cache_ip.amber_mesi_l1.dv.golden.amber_fsm_oracle import (
    step as oracle_step,
)
from projects.components.cache_ip.amber_mesi_l1.dv.tbclasses.amber_control_tb import (
    AmberControlTB,
    ST_MISS_DRAIN,
)

AXBURST_INCR = 0b01

# B-channel delay range that keeps a drain outstanding well past a mid-
# drain snoop service (~20 cycles); mirrors the stub-era widened-latency
# discipline with the REAL engine
B_WINDOW_DELAY = (24, 40)


class _WriteThroughMem(dict):
    """Golden memory dict that writes through to the responder
    MemoryModel on every assignment (see the miss_fill macro TB)."""

    def __init__(self, mm, base_of):
        super().__init__()
        self._mm = mm
        self._base_of = base_of

    def __setitem__(self, line, data):
        super().__setitem__(line, data)
        self._mm.write(self._base_of(line), bytearray(data))


class AmberEvictionMacroTB(AmberControlTB):
    """Eviction/writeback macro: real drain engine + transport in the loop."""

    SOAK_TXN = {'gate': 0, 'func': 2500, 'full': 10_000}

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

        # memory side: the house AXI4 write responder closes the wrapper's
        # m_axi AW/W/B pins; the golden model writes through to it
        self.memory_model = MemoryModel(
            num_lines=1 << 20,
            bytes_per_line=self.STRB_W,
            log=self.log,
        )
        self.mem = _WriteThroughMem(self.memory_model,
                                    lambda line: (line & self.LINE_MASK)
                                    << self.OFFSET_BITS)
        wr = create_axi4_slave_wr(
            dut=dut, clock=dut.clk, prefix='m_axi', log=self.log,
            id_width=8, addr_width=self.ADDR_WIDTH,
            data_width=self.STRB_W * 8, user_width=1,
            memory_model=self.memory_model)
        self.aw_slave = wr['AW']
        self.w_slave = wr['W']
        self.b_master = wr['B']
        self._profile_name = 'fast'
        self.set_profile(self._profile_name)
        self._wide_b = False
        self.log.info("AmberEvictionMacroTB: eviction group with the real "
                      "drain engine + axi4_master_wr in the loop")

    # ------------------------------------------------------------------
    # golden memory + responder profiles
    # ------------------------------------------------------------------
    def _mem_line(self, line):
        if line not in self.mem:
            self.mem[line] = bytearray(self._default_line(line))
        return self.mem[line]

    async def _req_issue(self, addr, we, be, wdata, label=''):
        self._mem_line(self._line_of(addr))
        return await super()._req_issue(addr, we, be, wdata, label)

    def set_profile(self, name):
        self._profile_name = name
        cfg = self.PROFILES[name]
        self.aw_slave.set_randomizer(FlexRandomizer({'ready_delay': cfg['ready']}))
        self.w_slave.set_randomizer(FlexRandomizer({'ready_delay': cfg['ready']}))
        self.b_master.set_randomizer(FlexRandomizer({'valid_delay': cfg['resp']}))

    def _wide_b_window(self):
        """Keep the next drain outstanding: B delayed past any mid-drain
        snoop service (the stub widened self.drain_latency; the real
        engine's B return is the only knob)."""
        self._wide_b = True
        self.b_master.set_randomizer(FlexRandomizer(
            {'valid_delay': ([B_WINDOW_DELAY], [1.0])}))

    def _restore_b_window(self):
        if self._wide_b:
            self._wide_b = False
            self.set_profile(self._profile_name)

    # ------------------------------------------------------------------
    # setup: the drain is REAL -- no drain_done drive, no drain stub; the
    # fill stub stays (fill is group 2's engine)
    # ------------------------------------------------------------------
    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock('clk', freq=period_ns, units='ns')
        d = self.dut
        d.req_valid.value = 0
        d.req_addr.value = 0
        d.req_we.value = 0
        d.req_be.value = 0
        d.req_wdata.value = 0
        d.fill_done.value = 0
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
        d.cd_ready_in.value = 0
        d.tag_b_set.value = 0
        await self.assert_reset()
        cocotb.start_soon(self._monitor())
        cocotb.start_soon(self._monitor_axi_wr())
        cocotb.start_soon(self._fill_stub())
        cocotb.start_soon(self._victim_way_tracker())
        cocotb.start_soon(self._victim_invariant())
        cocotb.start_soon(self._pf_invariant())
        await self.wait_clocks('clk', 3)
        await self.deassert_reset()

    # ------------------------------------------------------------------
    # monitor: AW / W / B handshake stamps (writeback scoring)
    # ------------------------------------------------------------------
    async def _monitor_axi_wr(self):
        d = self.dut
        while True:
            await self._negedge_settled()
            if int(d.m_axi_awvalid.value) and int(d.m_axi_awready.value):
                self.events.append((self.cyc, 'aw', {
                    'addr': int(d.m_axi_awaddr.value),
                    'len': int(d.m_axi_awlen.value),
                    'size': int(d.m_axi_awsize.value),
                    'burst': int(d.m_axi_awburst.value),
                }))
            if int(d.m_axi_wvalid.value) and int(d.m_axi_wready.value):
                self.events.append((self.cyc, 'w_beat', {
                    'data': int(d.m_axi_wdata.value),
                    'last': int(d.m_axi_wlast.value),
                }))
            if int(d.m_axi_bvalid.value) and int(d.m_axi_bready.value):
                self.events.append((self.cyc, 'b_done', {
                    'resp': int(d.m_axi_bresp.value),
                }))

    # ------------------------------------------------------------------
    # gate pin: a dirty eviction drives the real AW/W/B burst; payload
    # audited in the MemoryModel; B strictly before drain_done
    # ------------------------------------------------------------------
    async def _writeback_round_trip(self):
        sd = self.SETS // 2
        v_addr = self._compose_addr(0x40, sd)
        line_v = self._line_of(v_addr)
        self._mem_line(line_v)          # default content both sides
        await self._txn(v_addr, 1, wdata=0xC001D00DFEEDFACE,
                        label='wrt:wr_v')               # V -> M
        victim_content = bytes(self.cache_data[line_v])
        for i in range(1, self.WAYS):
            await self._txn(self._compose_addr(0x40 + i, sd), 0,
                            label=f'wrt:fill[{i}]')

        tap0 = len(self.events)
        accept = await self._req_issue(self._compose_addr(0x48, sd), 0,
                                       (1 << self.STRB_W) - 1, 0,
                                       'wrt:evict')
        _, _ = await self._wait_tap('drain_done')
        accept, rsp_cyc, _ = await self._req_await_rsp(accept, 'wrt:rsp')
        sl = [e for e in self.events[tap0:] if e[0] > accept]

        aws = [p for _, k, p in sl if k == 'aw']
        ws = [p for _, k, p in sl if k == 'w_beat']
        bs = [p for _, k, p in sl if k == 'b_done']
        dds = [c for c, k, _ in sl if k == 'drain_done']
        self._score("wrt: exactly one AW burst", len(aws), 1)
        if aws:
            self._score("wrt: AW line-aligned",
                        aws[0]['addr'] & (self.LINE_BYTES - 1), 0)
            self._score("wrt: AW addr is the victim line",
                        aws[0]['addr'] >> self.OFFSET_BITS, line_v)
            self._score("wrt: AW len", aws[0]['len'], self.FILL_BEATS - 1)
            self._score("wrt: AW size", aws[0]['size'],
                        self.STRB_W.bit_length() - 1)
            self._score("wrt: AW burst INCR", aws[0]['burst'], AXBURST_INCR)
        self._score("wrt: W beat count", len(ws), self.FILL_BEATS)
        self._score("wrt: W last only on the final beat",
                    [p['last'] for p in ws],
                    [1 if i == self.FILL_BEATS - 1 else 0
                     for i in range(self.FILL_BEATS)])
        # W payload == the staged (pre-eviction) cache content
        for i, p in enumerate(ws):
            self._score(f"wrt: W beat{i} data", p['data'],
                        self._beat_of_line(victim_content, i))
        self._score("wrt: exactly one B", len(bs), 1)
        if bs:
            self._score("wrt: B resp OKAY", bs[0]['resp'], 0)
        if dds:
            first_dd = dds[0]
            b_before = all(c < first_dd for c, k, _ in sl if k == 'b_done')
            self._score("wrt: B before drain_done", b_before, True)
        # engine-level ordering: drain_done strictly after the B handshake
        b_cyc = next((c for c, k, _ in sl if k == 'b_done'), None)
        dd_cyc = next((c for c, k, _ in sl if k == 'drain_done'), None)
        self._score("wrt: drain_done observed", dd_cyc is not None, True)
        if b_cyc is not None and dd_cyc is not None:
            self._score("wrt: drain_done after B", dd_cyc > b_cyc, True)

        # the generic scorer owns the transaction machinery + model replay
        line_new = self._line_of(self._compose_addr(0x48, sd))
        set_idx = self._set_of_line(line_new)
        res = oracle_step(self.line_state.get(line_new, 'I'), 'CPU_RD')
        rsp_data = next((p for _, k, p in sl if k == 'rsp'), None)
        self._score_slice(self._compose_addr(0x48, sd), line_new, set_idx, 0,
                          0, (1 << self.STRB_W) - 1, 0, res, rsp_data, sl,
                          'wrt')
        self.txns += 1

        # payload audit + refetch round trip through the real W channel
        self._score("wrt: victim retired to memory",
                    bytes(self._mem_line(line_v)), victim_content)
        await self._txn(v_addr, 0, label='wrt:refetch')
        self._score("wrt: refetch returns the drained data",
                    self.line_state.get(line_v), 'S')
        self.log.info("WritebackRoundTrip directed done (real AW/W/B burst)")

    # ------------------------------------------------------------------
    # func pins
    # ------------------------------------------------------------------
    async def _drain_backpressure_drain(self):
        # a dirty eviction with AW/W ready stalls + B latency: the engine
        # must hold the staged payload and still land it intact
        sb = self.SETS // 4
        v_addr = self._compose_addr(0x44, sb)
        line_v = self._line_of(v_addr)
        self._mem_line(line_v)
        await self._txn(v_addr, 1, wdata=0x5CA1AB1ED00DFEED,
                        label='dbp:wr_v')
        victim_content = bytes(self.cache_data[line_v])
        for i in range(1, self.WAYS):
            await self._txn(self._compose_addr(0x44 + i, sb), 0,
                            label=f'dbp:fill[{i}]')
        self.set_profile('slow')
        tap0 = len(self.events)
        accept = await self._req_issue(self._compose_addr(0x4C, sb), 0,
                                       (1 << self.STRB_W) - 1, 0, 'dbp:evict')
        _, _ = await self._wait_tap('drain_done')
        accept, rsp_cyc, _ = await self._req_await_rsp(accept, 'dbp:rsp')
        self.set_profile('fast')
        sl = [e for e in self.events[tap0:] if e[0] > accept]
        ws = [p for _, k, p in sl if k == 'w_beat']
        self._score("dbp: W beat count under backpressure", len(ws),
                    self.FILL_BEATS)
        for i, p in enumerate(ws):
            self._score(f"dbp: W beat{i} payload held", p['data'],
                        self._beat_of_line(victim_content, i))
        b_cyc = next((c for c, k, _ in sl if k == 'b_done'), None)
        dd_cyc = next((c for c, k, _ in sl if k == 'drain_done'), None)
        if b_cyc is not None and dd_cyc is not None:
            self._score("dbp: drain_done after B (backpressured)",
                        dd_cyc > b_cyc, True)
        line_new = self._line_of(self._compose_addr(0x4C, sb))
        set_idx = self._set_of_line(line_new)
        res = oracle_step(self.line_state.get(line_new, 'I'), 'CPU_RD')
        rsp_data = next((p for _, k, p in sl if k == 'rsp'), None)
        self._score_slice(self._compose_addr(0x4C, sb), line_new, set_idx, 0,
                          0, (1 << self.STRB_W) - 1, 0, res, rsp_data, sl,
                          'dbp')
        self.txns += 1
        self._score("dbp: victim retired to memory",
                    bytes(self._mem_line(line_v)), victim_content)
        self.log.info("DrainBackpressureDrain directed done")

    async def _victim_snoop_suite(self):
        # the inherited compositions keep the drain outstanding through a
        # delayed-B window instead of the retired stub-latency knob
        self._wide_b_window()
        try:
            await super()._victim_snoop_suite()
        finally:
            self._restore_b_window()

    async def _victim_snoop_directed(self):
        # SnoopDrainingVictim + SnoopStaleVictimMidFill from the inherited
        # victim snoop suite (the buffer-bypass compositions)
        await self._victim_snoop_suite()

    async def _eviction_soak(self):
        n = self.SOAK_TXN[self.TEST_LEVEL]
        pool_tags = 4 * self.WAYS + 2
        for i in range(n):
            if random.random() < 0.3:
                self.set_profile(random.choice(list(self.PROFILES)))
            s = random.randrange(self.SETS)
            t = random.randrange(pool_tags)
            line = (t << (self.SET_BITS + self.OFFSET_BITS)) \
                | (s << self.OFFSET_BITS)
            beat = random.randrange(self.FILL_BEATS)
            addr = line | (beat << (self.STRB_W.bit_length() - 1))
            # write-heavy mix: most victims arrive dirty
            we = 1 if random.random() < 0.7 else 0
            await self._txn(addr, 1 if we else 0, label=f'esoak[{i}]')
            if i % 1000 == 0:
                self.mark_progress(f"eviction soak {i}/{n}")
        self.set_profile('fast')
        self.log.info(f"eviction soak done ({n} transactions)")

    # ------------------------------------------------------------------
    async def run(self) -> bool:
        await self._check_init()
        self.scenarios['InitWalk'] = True
        self.scenarios['StrayReqInInit'] = True
        await self._writeback_round_trip()
        self.scenarios['WritebackRoundTrip'] = True
        if self.TEST_LEVEL in ('func', 'full'):
            await self._victim_buffer_handshake()
            self.scenarios['VictimBufferHandshake'] = True
            await self._victim_snoop_directed()
            self.scenarios['SnoopDrainingVictim'] = True
            self.scenarios['SnoopStaleVictimMidFill'] = True
            await self._drain_backpressure_drain()
            self.scenarios['DrainBackpressureDrain'] = True
            await self._eviction_soak()
            self.scenarios['EvictionSoak'] = True
        # the EVERY-CYCLE victim-buffer invariant ran throughout
        self.scenarios['VictimLoadWhileBusyNever'] = True
        return self.mismatches == 0
