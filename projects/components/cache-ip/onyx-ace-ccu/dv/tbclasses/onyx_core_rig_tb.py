# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: onyx_core_rig_tb
# Purpose: the core-alone testbench (onyx TASK-001 step 5): onyx_ccu with N
#   BFM caches and a BFM memory, on onyx_core_rig_tb.sv.
#
# Subsystem: onyx (cache-ip)
"""The core-alone testbench: onyx_ccu against N BFM caches.

Each cache is a MESI model built on the framework BFMs -- AXI4MasterRead /
AXI4MasterWrite for its memory side, AXI4ACESnoopSlave (custom handler) for
AC/CR/CD -- plus the D-8 request and retire sidebands, driven per cycle.
Memory is AXI4SlaveRead / AXI4SlaveWrite over one MemoryModel.  Unlike the
pair rig (real jet-prime caches), the caches here issue every request
class onyx decodes, including amber's WriteClean, and N runs 2..4.

The cache model's obligations are onyx's cache-side contract (onyx HAS
ch04; jet-prime delta 02 / 05):

- a fill (READ_NOT_SHARED_DIRTY -> S, READ_UNIQUE -> M) or an upgrade
  (CLEAN_UNIQUE, S -> M) is one request pulse and one AR, in launch order;
  a fill's ID is its MSHR entry, the upgrade's is MSHR_COUNT; the retire
  pulse names the ID after the last beat;
- one transaction per line per cache (no new op on a busy line);
- a snoop is answered per the house matrix (l1_pkg amber_snoop_crresp) at
  the cache's state when the responder takes it; a snoop that invalidates
  a Shared line whose upgrade is waiting kills the upgrade (jet-prime's
  killed-upgrade rule: the upgrade completes to Invalid, the store is not
  done);
- writes go out one at a time per cache, in order; a write is STARTED
  when it is handed to the BFM (its AW follows within the profile's valid
  delay) -- jet-prime's drain start;
- a write-back victim answers the first snoop that takes the line with
  DataTransfer + PassDirty from its buffer, and Invalid after that; if its
  drain had not started, that snoop ends it (no drain), otherwise it
  drains (jet-prime BUG-002);
- a WriteClean line (amber TASK-004: the dirty line is written and kept)
  is busy until its BRESP and answers snoops as Modified until then -- a
  clean answer would let a later read fetch memory before the WriteClean
  lands (onyx holds a write to a line while a slot on it gathers); a
  snoop that takes the line before the WriteClean started ends it;
- EVICT pulses for clean lines, which allocate nothing.

Checks (all counted; the test fails on any mismatch or a zero count):
data on every load hit, fill and snoop data beat against the golden (the
last value stored to the line); single-writer on every install; at the
end, every cache's lines flushed and memory equal to the golden on every
line.
"""
import os
import random
from collections import deque
from typing import Dict, List, Optional

import cocotb
from cocotb.triggers import FallingEdge, RisingEdge

from CocoTBFramework.components.ace.ace_interfaces import AXI4ACESnoopSlave
from CocoTBFramework.components.ace.ace_transaction import CRRESP, CacheState, SnoopType
from CocoTBFramework.components.axi4.axi4_interfaces import (
    AXI4MasterRead,
    AXI4MasterWrite,
    AXI4SlaveRead,
    AXI4SlaveWrite,
)
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.shared.memory_model import MemoryModel
from TBClasses.shared.tbbase import TBBase

from projects.components.cache_ip.onyx_ace_ccu.dv.tbclasses.onyx_snoop_gather_tb import amber_crresp

# l1_pkg ACE request classes (the D-8 sideband's coh_req_type)
REQ_RU, REQ_CU, REQ_WB, REQ_EVICT, REQ_RNSD, REQ_WC = 0b001, 0b010, 0b100, 0b101, 0b110, 0b111

I, S, E, M = CacheState.INVALID, CacheState.SHARED, CacheState.EXCLUSIVE, CacheState.MODIFIED  # noqa: E741 (MESI)

MSHR_COUNT = 3          # fill IDs 0..2; the upgrade's ID is 3 (four launches <= PEND_DEPTH)
WRITE_ID = 0


class _Cache:
    """One BFM cache's model state."""

    def __init__(self, port: int):
        self.port = port
        self.state: Dict[int, CacheState] = {}
        self.data: Dict[int, List[int]] = {}
        self.busy: set = set()                 # lines with a transaction of this cache in flight
        self.free_ids: List[int] = list(range(MSHR_COUNT))
        self.upgrade: Optional[dict] = None    # {'line', 'killed'}
        self.victims: Dict[int, dict] = {}     # line -> its write record (WB not yet BRESP'd)
        self.wclean: Dict[int, dict] = {}      # line -> its write record (WriteClean not yet BRESP'd)
        self.wq: deque = deque()               # write records not yet handed to the BFM
        self.inflight = 0

    def st(self, line: int) -> CacheState:
        return self.state.get(line, I)


class OnyxCoreRigTB(TBBase):
    """onyx_ccu alone, N BFM caches, BFM memory."""

    PROFILES = {
        'fast':   {'valid': ([(0, 0)], [1.0]), 'ready': ([(0, 0)], [1.0])},
        'normal': {'valid': ([(0, 0), (1, 3)], [0.7, 0.3]), 'ready': ([(0, 0), (1, 3)], [0.8, 0.2])},
        'stress': {'valid': ([(0, 0), (1, 4), (5, 12)], [0.5, 0.35, 0.15]),
                   'ready': ([(0, 0), (1, 4), (5, 12)], [0.5, 0.35, 0.15])},
    }
    OPS_PER_PORT = {'gate': 150, 'func': 600, 'full': 2000}

    def __init__(self, dut):
        super().__init__(dut)
        self.dut = dut
        self.n = int(os.environ.get('TEST_N_PORTS', '2'))
        self.aw = int(os.environ.get('TEST_ADDR_WIDTH', '32'))
        self.dw = int(os.environ.get('TEST_DATA_WIDTH', '64'))
        self.lb = int(os.environ.get('TEST_LINE_BYTES', '64'))
        self.level = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.profile = os.environ.get('TEST_PROFILE', 'normal')
        self.n_lines = int(os.environ.get('TEST_HOT_LINES', '8'))
        self.clk_period = int(os.environ.get('TEST_CLK_PERIOD', '10'))
        self.seed = int(os.environ.get('SEED', '0'))
        self.rng = random.Random(self.seed)
        self.beats = self.lb * 8 // self.dw
        self.bb = self.dw // 8
        self.mask = (1 << self.dw) - 1
        self.base = 0x1000                       # the hot lines live at base .. base + n_lines * lb
        self.lines = [self.base + i * self.lb for i in range(self.n_lines)]
        self.ops = int(os.environ.get('TEST_OPS', str(self.OPS_PER_PORT.get(self.level, 150))))

        # memory: the model backs [0, base + n_lines * lb); random initial lines
        mem_bytes = self.base + self.n_lines * self.lb
        preset = [self.rng.randrange(256) for _ in range(mem_bytes)]
        self.mem = MemoryModel(num_lines=mem_bytes // self.bb, bytes_per_line=self.bb,
                               log=self.log, preset_values=preset)
        self.golden: Dict[int, List[int]] = {ln: self._bytes_to_beats(preset[ln:ln + self.lb])
                                             for ln in self.lines}

        kw = dict(data_width=self.dw, addr_width=self.aw, id_width=8, user_width=1)
        self.mem_rd = AXI4SlaveRead(dut, dut.clk, 'mem_', log=self.log, ifc_name='mem',
                                    memory_model=self.mem, interleave_r=True, **kw)
        self.mem_wr = AXI4SlaveWrite(dut, dut.clk, 'mem_', log=self.log, ifc_name='mem',
                                     memory_model=self.mem, **kw)
        self.rd: List[AXI4MasterRead] = []
        self.wr: List[AXI4MasterWrite] = []
        self.sn: List[AXI4ACESnoopSlave] = []
        self.caches: List[_Cache] = []
        for p in range(self.n):
            self.rd.append(AXI4MasterRead(dut, dut.clk, f'c{p}_', log=self.log, ifc_name=f'c{p}',
                                          pipelined=True, timeout_cycles=200000, **kw))
            self.wr.append(AXI4MasterWrite(dut, dut.clk, f'c{p}_', log=self.log, ifc_name=f'c{p}',
                                           pipelined=True, timeout_cycles=200000, **kw))
            sn = AXI4ACESnoopSlave(dut, dut.clk, f'c{p}_', log=self.log, ifc_name=f'c{p}',
                                   data_width=self.dw, addr_width=self.aw)
            sn.set_handler(self._make_snoop_handler(p))
            self.sn.append(sn)
            self.caches.append(_Cache(p))
        # an AR can wait out other ports' transactions on its line, and a
        # cache's own earlier launches: far longer than the channels' 1000-
        # cycle default; a real hang is the no-progress watchdog's
        for p in range(self.n):
            for ch in (self.rd[p].ar_channel, self.wr[p].aw_channel, self.wr[p].w_channel,
                       self.sn[p].cr_channel, self.sn[p].cd_channel):
                ch.timeout_cycles = 200000
        for ch in (self.mem_rd.r_channel, self.mem_wr.b_channel):
            ch.timeout_cycles = 200000
        self.watchdog_cycles = 20000
        self._req_q: List[List[tuple]] = [[] for _ in range(self.n)]
        self._done_q: List[List[int]] = [[] for _ in range(self.n)]

        self.stats = {k: 0 for k in (
            'checks', 'mismatches', 'loads_hit', 'stores_hit', 'fills_rnsd', 'fills_ru',
            'upgrades', 'upgrades_killed', 'writebacks', 'writecleans', 'evicts',
            'snoops', 'snoops_dt', 'snoops_victim', 'snoops_wclean', 'snoops_upgrade_kill',
            'swmr_checks', 'grants', 'flush_writebacks', 'memory_lines_checked',
            'writes_ended')}
        self.errors: List[str] = []
        self.trace: List[tuple] = []           # (ns, port, event, line): dumped for a failing line
        self._apply_profile(self.profile)
        self.log.info(f"OnyxCoreRigTB: N={self.n} DW={self.dw} LB={self.lb} beats={self.beats} "
                      f"lines={self.n_lines} ops/port={self.ops} profile={self.profile} "
                      f"level={self.level} seed={self.seed}")

    # ------------------------------------------------------------------
    # the three mandatory methods
    # ------------------------------------------------------------------
    async def setup_clocks_and_reset(self):
        self._drive_sidebands_idle()
        await self.start_clock('clk', self.clk_period, 'ns')
        await self.assert_reset()
        await self.wait_clocks('clk', 10)
        await self.deassert_reset()
        await self.wait_clocks('clk', 5)

    async def assert_reset(self):
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        self.dut.rst_n.value = 1

    # ------------------------------------------------------------------
    # helpers
    # ------------------------------------------------------------------
    def _bytes_to_beats(self, b) -> List[int]:
        return [int.from_bytes(bytes(b[i * self.bb:(i + 1) * self.bb]), 'little')
                for i in range(self.beats)]

    def _apply_profile(self, name: str):
        cfg = self.PROFILES[name]
        val, rdy = cfg['valid'], cfg['ready']
        for p in range(self.n):
            self.rd[p].ar_channel.set_randomizer(FlexRandomizer({'valid_delay': val}))
            self.rd[p].r_channel.set_randomizer(FlexRandomizer({'ready_delay': rdy}))
            self.wr[p].aw_channel.set_randomizer(FlexRandomizer({'valid_delay': val}))
            self.wr[p].w_channel.set_randomizer(FlexRandomizer({'valid_delay': val}))
            self.wr[p].b_channel.set_randomizer(FlexRandomizer({'ready_delay': rdy}))
            self.sn[p].ac_channel.set_randomizer(FlexRandomizer({'ready_delay': rdy}))
            self.sn[p].cr_channel.set_randomizer(FlexRandomizer({'valid_delay': val}))
            self.sn[p].cd_channel.set_randomizer(FlexRandomizer({'valid_delay': val}))
        self.mem_rd.ar_channel.set_randomizer(FlexRandomizer({'ready_delay': rdy}))
        self.mem_rd.r_channel.set_randomizer(FlexRandomizer({'valid_delay': val}))
        self.mem_wr.aw_channel.set_randomizer(FlexRandomizer({'ready_delay': rdy}))
        self.mem_wr.w_channel.set_randomizer(FlexRandomizer({'ready_delay': rdy}))
        self.mem_wr.b_channel.set_randomizer(FlexRandomizer({'valid_delay': val}))

    def _ev(self, p: int, what: str, line: int):
        self.trace.append((cocotb.utils.get_sim_time('ns'), p, what, line))

    def _fail(self, msg: str, line: Optional[int] = None):
        self.stats['mismatches'] += 1
        if len(self.errors) < 20:
            self.log.error(msg)
            if line is not None:
                for t, p, what, ln in [e for e in self.trace if e[3] == line][-24:]:
                    self.log.error(f"    {t:>10} ns  port {p}  {what}")
        self.errors.append(msg)

    def _check_data(self, what: str, port: int, line: int, got: List[int]):
        self.stats['checks'] += 1
        exp = self.golden[line]
        if list(got) != list(exp):
            diff = [i for i in range(self.beats) if got[i] != exp[i]] if len(got) == self.beats else 'len'
            self._fail(f"{what}: port {port} line 0x{line:x} data differs from the golden "
                       f"(beats {diff}) got={[hex(x) for x in got]} exp={[hex(x) for x in exp]}", line)

    def _check_swmr(self, port: int, line: int, st: CacheState):
        """Single writer: an E/M install has no other valid copy; an S install no E/M copy."""
        self.stats['swmr_checks'] += 1
        for c in self.caches:
            if c.port == port:
                continue
            other = c.st(line)
            live_victim = line in c.victims and not c.victims[line]['passed']
            if st in (E, M) and (other != I or live_victim):
                self._fail(f"SWMR: port {port} installs {st.name} on 0x{line:x} while port "
                           f"{c.port} holds {other.name}{' (+victim)' if live_victim else ''}", line)
            if st == S and (other in (E, M) or live_victim):
                self._fail(f"SWMR: port {port} installs S on 0x{line:x} while port {c.port} "
                           f"holds {other.name}{' (+victim)' if live_victim else ''}", line)

    # ------------------------------------------------------------------
    # sidebands: one request and one retire pulse per port per cycle
    # ------------------------------------------------------------------
    def _drive_sidebands_idle(self):
        for p in range(self.n):
            getattr(self.dut, f'c{p}_coh_req_valid').value = 0
            getattr(self.dut, f'c{p}_coh_req_addr').value = 0
            getattr(self.dut, f'c{p}_coh_req_type').value = 0
            getattr(self.dut, f'c{p}_coh_done_valid').value = 0
            getattr(self.dut, f'c{p}_coh_done_id').value = 0

    async def _sideband_driver(self):
        while True:
            await FallingEdge(self.dut.clk)
            for p in range(self.n):
                if self._req_q[p]:
                    addr, typ = self._req_q[p].pop(0)
                    getattr(self.dut, f'c{p}_coh_req_valid').value = 1
                    getattr(self.dut, f'c{p}_coh_req_addr').value = addr
                    getattr(self.dut, f'c{p}_coh_req_type').value = typ
                else:
                    getattr(self.dut, f'c{p}_coh_req_valid').value = 0
                if self._done_q[p]:
                    getattr(self.dut, f'c{p}_coh_done_valid').value = 1
                    getattr(self.dut, f'c{p}_coh_done_id').value = self._done_q[p].pop(0)
                else:
                    getattr(self.dut, f'c{p}_coh_done_valid').value = 0

    async def _grant_counter(self):
        """Counts grants; traces the RTL-side handshakes per line (grant,
        AC / CR per port, memory AR / AW) for the failure dump."""
        d = self.dut
        lm = ~(self.lb - 1)
        idle = 0
        while True:
            await RisingEdge(d.clk)
            if not int(d.rst_n.value):
                continue
            moved = (int(d.dbg_grant.value)
                     or (int(d.mem_rvalid.value) and int(d.mem_rready.value))
                     or (int(d.mem_bvalid.value) and int(d.mem_bready.value)))
            pending = any(c.inflight for c in self.caches)
            idle = 0 if (moved or not pending) else idle + 1
            if idle >= self.watchdog_cycles:
                self._fail(f"no progress for {idle} cycles with work outstanding "
                           f"(inflight {[c.inflight for c in self.caches]}, "
                           f"live slots {int(d.dbg_busy_slots.value)})")
                raise AssertionError(f"onyx_core_rig: hang -- {self.errors[-1]}")
            if int(d.dbg_grant.value):
                self.stats['grants'] += 1
                self._ev(int(d.dbg_grant_dir.value), 'RTL grant', int(d.dbg_grant_addr.value) & lm)
            for p in range(self.n):
                if int(getattr(d, f'c{p}_acvalid').value) and int(getattr(d, f'c{p}_acready').value):
                    self._ev(p, f"RTL AC accepted (snoop {int(getattr(d, f'c{p}_acsnoop').value):#x})",
                             int(getattr(d, f'c{p}_acaddr').value) & lm)
            if int(d.mem_arvalid.value) and int(d.mem_arready.value):
                self._ev(-1, f"RTL memory AR id {int(d.mem_arid.value)}", int(d.mem_araddr.value) & lm)
            if int(d.mem_awvalid.value) and int(d.mem_awready.value):
                self._ev(-1, 'RTL memory AW', int(d.mem_awaddr.value) & lm)

    # ------------------------------------------------------------------
    # the snoop responder
    # ------------------------------------------------------------------
    def _make_snoop_handler(self, p: int):
        def handler(addr: int, snoop: SnoopType, _state: CacheState):
            return self._snoop(p, addr & ~(self.lb - 1), snoop)
        return handler

    def _snoop(self, p: int, line: int, snoop: SnoopType):
        c = self.caches[p]
        self.stats['snoops'] += 1
        self._ev(p, f"snoop {snoop.name} at {c.st(line).name}"
                    f"{' victim' if line in c.victims else ''}{' wclean' if line in c.wclean else ''}", line)
        vic = c.victims.get(line)
        if vic is not None and not vic['passed']:
            # a write-back victim: DT + PD from the buffer, then gone; an
            # unstarted drain ends here (jet-prime BUG-002)
            self.stats['snoops_victim'] += 1
            crresp = amber_crresp(M, snoop)
            if crresp.data_transfer:
                vic['passed'] = True
                if not vic['started']:
                    self._cancel_write(p, vic)
                return self._answer(p, line, snoop, crresp, vic['data'])
            if snoop == SnoopType.MAKE_INVALID:
                self._fail(f"port {p}: MakeInvalid hit write-back victim 0x{line:x} "
                           f"(no peer can hold it S while it was Modified)", line)
                vic['passed'] = True
            return crresp, None
        st = c.st(line)
        wcr = c.wclean.get(line)
        if wcr is not None and st == M:
            self.stats['snoops_wclean'] += 1
        crresp = amber_crresp(st, snoop)
        data = list(c.data[line]) if crresp.data_transfer else None
        if snoop == SnoopType.READ_SHARED:
            nxt = S if st != I else I
        else:                                  # READ_UNIQUE, MAKE_INVALID
            nxt = I
        if st == M and snoop == SnoopType.MAKE_INVALID:
            self._fail(f"port {p}: MakeInvalid snoop of Modified line 0x{line:x} -- the dirty "
                       f"data is dropped (no DataTransfer is legal for MakeInvalid)", line)
        if nxt == I and st != I:
            if c.upgrade is not None and c.upgrade['line'] == line and not c.upgrade['killed']:
                c.upgrade['killed'] = True
                self.stats['snoops_upgrade_kill'] += 1
            c.state[line] = I
            c.data.pop(line, None)
        elif nxt == S and st != S:
            c.state[line] = S
        if wcr is not None and st == M and nxt != M and not wcr['started']:
            self._cancel_write(p, wcr)             # the line passed on dirty: nothing to clean
        return self._answer(p, line, snoop, crresp, data)

    def _answer(self, p: int, line: int, snoop: SnoopType, crresp: CRRESP, data):
        ok, msg = crresp.validate_for_snoop(snoop)
        self.stats['checks'] += 1
        if not ok:
            self._fail(f"port {p}: illegal CRRESP for {snoop.name}: {msg}")
        if data is not None:
            self.stats['snoops_dt'] += 1
            self._check_data(f"snoop {snoop.name} supply", p, line, data)
        return crresp, data

    # ------------------------------------------------------------------
    # cache operations
    # ------------------------------------------------------------------
    REQ_NAMES = {REQ_RU: 'READ_UNIQUE', REQ_CU: 'CLEAN_UNIQUE', REQ_WB: 'WRITE_BACK',
                 REQ_EVICT: 'EVICT', REQ_RNSD: 'READ_NOT_SHARED_DIRTY', REQ_WC: 'WRITE_CLEAN'}

    def _launch_req(self, p: int, line: int, typ: int):
        self._ev(p, f"launch {self.REQ_NAMES[typ]} (at {self.caches[p].st(line).name})", line)
        self._req_q[p].append((line, typ))

    async def _fill(self, p: int, line: int, typ: int, store_beat: Optional[int], mid: int):
        c = self.caches[p]
        data = await self.rd[p].read_transaction(line, burst_len=self.beats, id=mid)
        self._check_data('fill ' + ('READ_UNIQUE' if typ == REQ_RU else 'READ_NOT_SHARED_DIRTY'),
                         p, line, data)
        st = M if typ == REQ_RU else S
        self._ev(p, f"fill done -> {st.name}", line)
        self._check_swmr(p, line, st)
        c.state[line], c.data[line] = st, list(data)
        if store_beat is not None:
            self._store(p, line, store_beat)
        self._done_q[p].append(mid)
        await RisingEdge(self.dut.clk)
        c.free_ids.append(mid)
        c.busy.discard(line)
        c.inflight -= 1

    async def _upgrade(self, p: int, line: int, store_beat: int):
        c = self.caches[p]
        await self.rd[p].read_transaction(line, burst_len=1, id=MSHR_COUNT)
        self._ev(p, f"upgrade done{' (killed -> I)' if c.upgrade['killed'] else ' -> M'}", line)
        if c.upgrade['killed']:
            self.stats['upgrades_killed'] += 1        # the line stays Invalid; the store is not done
        elif line not in c.data:
            self._fail(f"model: port {p} upgrade of 0x{line:x} completed unkilled with no line data "
                       f"(state {c.st(line).name})", line)
        else:
            self._check_swmr(p, line, M)
            c.state[line] = M
            self._store(p, line, store_beat)
        self._done_q[p].append(MSHR_COUNT)
        await RisingEdge(self.dut.clk)
        c.upgrade = None
        c.busy.discard(line)
        c.inflight -= 1

    def _queue_write(self, p: int, line: int, data: List[int], typ: int) -> dict:
        c = self.caches[p]
        rec = {'line': line, 'data': list(data), 'typ': typ, 'started': False, 'passed': False}
        self._ev(p, f"queue {self.REQ_NAMES[typ]}", line)
        c.wq.append(rec)
        c.busy.add(line)
        c.inflight += 1
        return rec

    def _cancel_write(self, p: int, rec: dict):
        c = self.caches[p]
        self._ev(p, f"{self.REQ_NAMES[rec['typ']]} ended by a snoop before it started", rec['line'])
        self.stats['writes_ended'] += 1
        c.wq.remove(rec)
        self._retire_write(p, rec)

    def _retire_write(self, p: int, rec: dict):
        c = self.caches[p]
        (c.victims if rec['typ'] == REQ_WB else c.wclean).pop(rec['line'], None)
        c.busy.discard(rec['line'])
        c.inflight -= 1

    async def _writer(self, p: int):
        """Hands this cache's writes to the BFM one at a time, in order."""
        c = self.caches[p]
        while True:
            while not c.wq:
                await RisingEdge(self.dut.clk)
            rec = c.wq.popleft()
            rec['started'] = True
            line, typ, data = rec['line'], rec['typ'], rec['data']
            self._launch_req(p, line, typ)
            await self.wr[p].write_transaction(line, data, id=WRITE_ID)
            self._ev(p, f"{self.REQ_NAMES[typ]} BRESP", line)
            # at its BRESP the write is in memory: an absorption of the same
            # line waits for an older write-back (onyx BUG-003) and a newer
            # owner's write-back waits for the absorption
            self.stats['checks'] += 1
            landed = self._bytes_to_beats(bytes(self.mem.read(line, self.lb)))
            if landed != data:
                self._fail(f"port {p}: {self.REQ_NAMES[typ]} of 0x{line:x} BRESP'd but memory "
                           f"does not hold its data", line)
            if typ == REQ_WC and c.st(line) == M:
                c.state[line] = E                     # clean now: memory holds it
            self._retire_write(p, rec)

    def _store(self, p: int, line: int, beat: int):
        c = self.caches[p]
        val = self.rng.getrandbits(self.dw)
        self._ev(p, f"store beat {beat}", line)
        c.data[line][beat] = val
        self.golden[line] = list(c.data[line])
        c.state[line] = M

    def _start_fill(self, p: int, line: int, typ: int, store_beat: Optional[int]):
        # the launch is decided, recorded and pulsed NOW: a snoop handled
        # before the coroutine runs must see it (a fill is pre-AR, an
        # upgrade killable)
        c = self.caches[p]
        mid = c.free_ids.pop(0)
        c.busy.add(line)
        c.inflight += 1
        self._launch_req(p, line, typ)
        cocotb.start_soon(self._fill(p, line, typ, store_beat, mid))

    def _start_upgrade(self, p: int, line: int, store_beat: int):
        c = self.caches[p]
        c.upgrade = {'line': line, 'killed': False}
        c.busy.add(line)
        c.inflight += 1
        self._launch_req(p, line, REQ_CU)
        cocotb.start_soon(self._upgrade(p, line, store_beat))

    def _issue(self, p: int, op: str, line: int) -> bool:
        """Start one operation on a non-busy line; False when it cannot go now."""
        c = self.caches[p]
        st = c.st(line)
        beat = self.rng.randrange(self.beats)
        if op == 'load':
            if st != I:
                self.stats['loads_hit'] += 1
                self._check_data('load hit', p, line, c.data[line])
                return True
            if not c.free_ids:
                return False
            self.stats['fills_rnsd'] += 1
            self._start_fill(p, line, REQ_RNSD, None)
            return True
        if op == 'store':
            if st in (E, M):
                self.stats['stores_hit'] += 1
                self._store(p, line, beat)
                return True
            if st == S:
                if c.upgrade is not None:
                    return False
                self.stats['upgrades'] += 1
                self._start_upgrade(p, line, beat)
                return True
            if not c.free_ids:
                return False
            self.stats['fills_ru'] += 1
            self._start_fill(p, line, REQ_RU, beat)
            return True
        if op == 'evict':
            if st == M:
                self.stats['writebacks'] += 1
                c.victims[line] = self._queue_write(p, line, c.data[line], REQ_WB)
                c.state[line] = I
                c.data.pop(line, None)
                return True
            if st in (S, E):
                self.stats['evicts'] += 1
                c.state[line] = I
                c.data.pop(line, None)
                if self.rng.random() < 0.5:
                    self._launch_req(p, line, REQ_EVICT)
                return True
            return True
        if op == 'writeclean':
            if st != M:
                return True
            self.stats['writecleans'] += 1
            c.wclean[line] = self._queue_write(p, line, c.data[line], REQ_WC)
            return True
        raise ValueError(op)

    async def _port_worker(self, p: int, n_ops: int):
        c = self.caches[p]
        weights = (('load', 40), ('store', 35), ('evict', 15), ('writeclean', 10))
        names = [w[0] for w in weights]
        wts = [w[1] for w in weights]
        done = 0
        while done < n_ops:
            await RisingEdge(self.dut.clk)
            if self.rng.random() < 0.3:
                continue
            line = self.rng.choice(self.lines)
            if line in c.busy:
                continue
            op = self.rng.choices(names, wts)[0]
            if self._issue(p, op, line):
                done += 1
        while c.inflight:
            await RisingEdge(self.dut.clk)

    async def _flush(self, p: int):
        """Write back every Modified line (the end-of-test memory check)."""
        c = self.caches[p]
        for line in list(self.lines):
            while line in c.busy:
                await RisingEdge(self.dut.clk)
            if c.st(line) == M:
                self.stats['flush_writebacks'] += 1
                self._issue(p, 'evict', line)
                await RisingEdge(self.dut.clk)
        while c.inflight:
            await RisingEdge(self.dut.clk)

    def _check_memory(self):
        for line in self.lines:
            got = self._bytes_to_beats(bytes(self.mem.read(line, self.lb)))
            self.stats['memory_lines_checked'] += 1
            self._check_data('final memory', -1, line, got)

    # ------------------------------------------------------------------
    # the run
    # ------------------------------------------------------------------
    async def run(self) -> bool:
        cocotb.start_soon(self._sideband_driver())
        cocotb.start_soon(self._grant_counter())
        for p in range(self.n):
            cocotb.start_soon(self._writer(p))
        workers = [cocotb.start_soon(self._port_worker(p, self.ops)) for p in range(self.n)]
        for w in workers:
            await w
        flushes = [cocotb.start_soon(self._flush(p)) for p in range(self.n)]
        for f in flushes:
            await f
        await self.wait_clocks('clk', 50)
        busy = int(self.dut.dbg_busy_slots.value)
        if busy:
            self._fail(f"{busy} transaction slots still live at the end")
        self._check_memory()
        s = self.stats
        for key in ('checks', 'grants', 'fills_rnsd', 'fills_ru', 'upgrades', 'writebacks',
                    'writecleans', 'snoops', 'snoops_dt', 'memory_lines_checked'):
            if s[key] == 0:
                self._fail(f"coverage: '{key}' is zero")
        self.log.info(f"OnyxCoreRigTB stats: {s}")
        return s['mismatches'] == 0

    def get_test_report(self) -> dict:
        return dict(self.stats)
