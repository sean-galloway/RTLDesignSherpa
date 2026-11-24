# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: onyx_pair_rig_tb
# Purpose: jet-prime's pair-rig testbench with two additions for onyx -- the
#   D9 observer's MonBus (mon2) is counted per event code and checked
#   against the testbench's own fabric model, and the D1 ACE-Lite IO port
#   is driven by the RDS-DV ACE master BFMs as a third requester of the
#   fabric model.
#
# Subsystem: onyx (cache-ip)
"""The pair-rig testbench, onyx flavor.

`JetPairRigTB` drives both CPUs, keeps the two-cache lockstep model with the
fabric rules and scores the ACE channels; it reads `u_fabric`'s debug taps,
which onyx keeps.  This subclass adds the two things onyx has that the
fabric did not.

**The IO port (D1).**  `AXI4ACEMasterRead` / `AXI4ACEMasterWrite` on the
harness's `io_*` pins issue ReadOnce / ReadNoSnoop and WriteUnique /
WriteLineUnique / WriteNoSnoop.  The fabric model gains a third requester
(index 2 = N_PORTS): the IO's slot transactions are queued by the driver
before the AR / AW is presented and popped at the grant like a cache's
sideband pulses; its snoops go to BOTH caches, so the resolution is kept
per peer and the verdict is their OR; the IO's data is scored on the wire
at RLAST (the supplier's line from the DT peer, else the memory model as it
stood at the memory AR); its writes land in the memory model beat by beat
at the W handshake (the same cycle the sdpram takes them), so the memory
audit covers them.  The per-requester hooks of the base model
(`_mon_snoop_grant`, `_on_ace_channels`, `_on_fab_grant`, `_on_mem_ar`,
`_on_mem_r`, `_on_slot_free`) are re-implemented here for N_REQ = 3; the
per-cache resolution itself is the base's, line for line.

Directed IO scenarios ride the gate: ReadOnce against M (the house table
passes the line dirty and invalidates: the IO sees the cache's bytes, the
absorption lands), against E (DT, the holder to S), against S (no DT: the
memory's bytes), against nothing; WriteUnique against M (CleanInvalid:
absorb, then the IO's partial strobes land on top, the cache's re-read
sees both), WriteLineUnique against two sharers, WriteUnique against E;
WriteNoSnoop / ReadNoSnoop; a read and a write in flight together, and a
read behind a write of its own line.  The random soak (func / full) adds
an IO loop beside the two CPU loops: ReadOnce anywhere, the other kinds in
the IO's own region (the top tag row of the span, which the CPU loops
avoid -- a non-shareable access to a line a cache holds dirty is
software's contract, not the manager's).

**The observer (D9).**  It counts the packets on `mon2` by event code and,
at the end, requires

- the exact counters (onyx_counters) equal the model: transactions ==
  grants, memory reads == memory ARs, absorptions, reads wasted (a memory
  read issued for a slot a peer then supplied) == dropped reads, lines
  supplied == forwarded lines;
- every MonBus class count is bounded by its counter, and the shortfall
  across classes is accounted for by the observer's own drop reports (the
  payload of each PktTypeError packet is the events lost): the observer
  is honest about what it could not carry, and loses nothing silently.

With USE_MONITOR=0 the observer must be silent.
"""
import os
import random
import sys
from collections import deque

import cocotb
from cocotb.triggers import FallingEdge, RisingEdge, Timer

from CocoTBFramework.components.ace.ace_interfaces import AXI4ACEMasterRead, AXI4ACEMasterWrite
from CocoTBFramework.components.ace.ace_transaction import ARSnoop, AWSnoop, CRRESP, SnoopType
from CocoTBFramework.components.ace.ace_field_configs import (
    DOMAIN_NON_SHAREABLE,
    DOMAIN_OUTER_SHAREABLE,
)
from projects.components.cache_ip.common_ip.dv.golden.l1_fsm_oracle import step as oracle_step

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                '..', '..', '..', 'jet-prime-mesi-l1', 'dv', 'tbclasses'))
import projects.components.cache_ip.jet_prime_mesi_l1.dv.tbclasses.jet_prime_pair_rig_tb as jp  # noqa: E402
from projects.components.cache_ip.jet_prime_mesi_l1.dv.tbclasses.jet_prime_pair_rig_tb import (  # noqa: E402
    JetPairRigTB,
)

ONYX_EV = {0x20: 'TXN_START', 0x22: 'GATHER_DONE', 0x23: 'MEM_READ',
           0x24: 'READ_WASTED', 0x25: 'ABSORB', 0x26: 'WRITEBACK', 0x27: 'LOCK_WAIT'}
PKT_TYPE_ERROR = 0x0

# the IO port is requester N_PORTS of the table (two caches here)
N_PORTS = 2
IO = N_PORTS
N_REQ = N_PORTS + 1
# onyx_pkg: the IO's grant classes in the l1_pkg request-class code space
CLS_IO_READ, CLS_IO_WRITE = 7, 5
# the IO's snoops (IHI0022 ACSNOOP; the house decode in l1_snoop_resp)
FAB_SNOOP_RO = 0x0   # ReadOnce
FAB_SNOOP_CI = 0x9   # CleanInvalid
SNOOP_NAME_BY_FAB = {**jp.SNOOP_NAME_BY_FAB,
                     FAB_SNOOP_RO: 'SNOOP_READ_ONCE', FAB_SNOOP_CI: 'SNOOP_CLEAN_INVALID'}
FAB_SNOOP_BY_TYPE = {**jp.FAB_SNOOP_BY_TYPE,
                     CLS_IO_READ: FAB_SNOOP_RO, CLS_IO_WRITE: FAB_SNOOP_CI}
FRAMEWORK_SNOOPS = {**jp.FRAMEWORK_SNOOPS,
                    'SNOOP_READ_ONCE': SnoopType.READ_ONCE,
                    'SNOOP_CLEAN_INVALID': SnoopType.CLEAN_INVALID}
CRRESP_DT, CRRESP_PD = jp.CRRESP_DT, jp.CRRESP_PD


class OnyxPairRigTB(JetPairRigTB):
    """JetPairRigTB plus the onyx observer check."""

    def __init__(self, dut, **kwargs):
        super().__init__(dut, **kwargs)
        self.onyx_mon = {name: 0 for name in ONYX_EV.values()}
        self.onyx_mon_drop_reports = 0
        self.onyx_mon_other = 0
        self.onyx_mon_total = 0
        self.onyx_mon_lost = 0          # the drop reports' payloads summed
        self.onyx_mon_port_hits = [0] * N_REQ   # per-requester packets (TXN_START, GATHER_DONE, READ_WASTED, LOCK_WAIT, the IO's WRITEBACK)
        # the observer's masks (the ocelus layers), from the cell's env: a set
        # perf_mask bit drops that class (bit = code[3:0]); a set port_mask
        # bit drops the events attributed to that port; enable 0 = silent
        self.mon_enable = int(os.environ.get('ONYX_MON_ENABLE', '1'), 0)
        self.mon_perf_mask = int(os.environ.get('ONYX_MON_PERF_MASK', '0'), 0)
        self.mon_port_mask = int(os.environ.get('ONYX_MON_PORT_MASK', '0'), 0)
        # the content filter: ONYX_MON_WIN='low:high' (inclusive, hex) enables
        # the observer's address window; the TB tracks every event's
        # transaction address itself (grant address per slot, AW address,
        # the waiting candidate's address) and counts the in-window events
        # per class as the observer's expected stream
        win = os.environ.get('ONYX_MON_WIN', '')
        self.mon_win = tuple(int(x, 0) for x in win.split(':')) if win else None
        self.exp_all = {name: 0 for name in ONYX_EV.values()}   # every event, by class
        self.exp_win = {name: 0 for name in ONYX_EV.values()}   # the in-window events

        # the IO port as the fabric model's third requester
        self.ft_queue = [[] for _ in range(N_REQ)]
        self.stats['grants'] = [0] * N_REQ
        self.io_stats = {'reads': 0, 'reads_sh': 0, 'rd_dt': 0, 'rd_pd': 0,
                         'writes': 0, 'writes_sh': 0, 'wr_dt': 0, 'beats_scored': 0,
                         'nosnoop_grants': 0}   # ReadNoSnoop slots: no peers, hence no GATHER_DONE
        self.IO_LINES = self.SETS                      # the IO's own region: the span's top tag row
        self.IO_BASE_LINE = self.SPAN - self.IO_LINES
        self.io_pass = deque()        # WriteNoSnoop contexts awaiting their AW (no slot)
        self.io_aw_cur = None         # the IO write whose W beats are landing
        self.io_rd = None
        self.io_wr = None
        self._io_id = 0
        self.IO_TXN = {'gate': 0, 'func': 80, 'full': 400}

    def _class_masked(self, name):
        code = {v: k for k, v in ONYX_EV.items()}[name]
        return not self.mon_enable or bool(self.mon_perf_mask & (1 << (code & 0xF)))

    async def setup_clocks_and_reset(self):
        self.dut.mon2_ready.value = 1
        d = self.dut
        d.mon2_cfg_enable.value = self.mon_enable
        d.mon2_cfg_perf_enable.value = 1
        d.mon2_cfg_error_enable.value = 1
        d.mon2_cfg_pkt_mask.value = 0
        d.mon2_cfg_perf_mask.value = self.mon_perf_mask
        d.mon2_cfg_error_mask.value = 0
        d.mon2_cfg_port_mask.value = self.mon_port_mask
        d.mon2_cfg_addr_win_enable.value = 1 if self.mon_win else 0
        d.mon2_cfg_addr_win_low.value = self.mon_win[0] if self.mon_win else 0
        d.mon2_cfg_addr_win_high.value = self.mon_win[1] if self.mon_win else 0
        self.log.info(f"onyx observer masks: enable={self.mon_enable} perf_mask=0x{self.mon_perf_mask:04x} "
                      f"port_mask=0b{self.mon_port_mask:03b} window={self.mon_win}")
        await super().setup_clocks_and_reset()
        # the IO port's masters (the ACE field set on AR / AW: snoop, domain,
        # bar); RRESP is the 4-bit ACE field the harness zero-extends
        self.io_rd = AXI4ACEMasterRead(dut=d, clock=d.clk, prefix='io_', log=self.log,
                                       id_width=8, addr_width=self.ADDR_WIDTH,
                                       data_width=self.BUS_WIDTH, user_width=1,
                                       timeout_cycles=self.RSP_TIMEOUT_CYCLES)
        self.io_wr = AXI4ACEMasterWrite(dut=d, clock=d.clk, prefix='io_', log=self.log,
                                        id_width=8, addr_width=self.ADDR_WIDTH,
                                        data_width=self.BUS_WIDTH, user_width=1,
                                        timeout_cycles=self.RSP_TIMEOUT_CYCLES)
        cocotb.start_soon(self._watch_onyx_mon())
        cocotb.start_soon(self._watch_onyx_events())
        cocotb.start_soon(self._watch_io())

    def _in_win(self, addr):
        return self.mon_win is None or (self.mon_win[0] <= addr <= self.mon_win[1])

    async def _watch_onyx_events(self):
        """Count the unit's events per class, all and in-window, from the
        harness's event taps: the model of what the observer must emit."""
        d = self.dut
        n_slots = 1 << len(d.oc_grant_slot)
        slot_win = [False] * n_slots
        lw_active = [False] * N_REQ
        lw_win = [False] * N_REQ

        def bump(name, inside):
            self.exp_all[name] += 1
            if inside:
                self.exp_win[name] += 1

        while True:
            await RisingEdge(d.clk)
            if int(d.oc_evt_grant.value):
                s = int(d.oc_grant_slot.value)
                slot_win[s] = self._in_win(int(d.oc_grant_addr.value))
                bump('TXN_START', slot_win[s])
            gather = int(d.oc_evt_gather.value)
            wasted = int(d.oc_evt_read_wasted.value)
            for p in range(2):
                if (gather >> p) & 1 or (wasted >> p) & 1:
                    s = int(d.oc_evt_gather_slot[p].value)
                    if (gather >> p) & 1:
                        bump('GATHER_DONE', slot_win[s])
                    if (wasted >> p) & 1:
                        bump('READ_WASTED', slot_win[s])
            if int(d.oc_evt_mem_ar.value):
                s = int(d.mem_arid.value) & (n_slots - 1)
                bump('MEM_READ', slot_win[s])
            if int(d.oc_evt_absorb.value):
                bump('ABSORB', slot_win[int(d.oc_evt_absorb_slot.value)])
            if int(d.oc_evt_wb.value):
                bump('WRITEBACK', self._in_win(int(d.mem_awaddr.value)))
            lw = int(d.oc_evt_lock_wait.value)
            for p in range(N_REQ):
                if (lw >> p) & 1:
                    if not lw_active[p]:
                        lw_active[p] = True
                        lw_win[p] = self._in_win(int(d.oc_evt_lock_wait_addr[p].value))
                elif lw_active[p]:
                    lw_active[p] = False
                    bump('LOCK_WAIT', lw_win[p])

    async def _watch_onyx_mon(self):
        d = self.dut
        while True:
            await RisingEdge(d.clk)
            if int(d.mon2_valid.value) and int(d.mon2_ready.value):
                pkt = int(d.mon2_packet.value)
                self.onyx_mon_total += 1
                ptype = (pkt >> 124) & 0xF
                code = (pkt >> 97) & 0xFF
                if ptype == PKT_TYPE_ERROR:
                    self.onyx_mon_drop_reports += 1
                    self.onyx_mon_lost += pkt & 0xFF
                elif code in ONYX_EV:
                    self.onyx_mon[ONYX_EV[code]] += 1
                    data = pkt & ((1 << 64) - 1)
                    if code == 0x20:            # TXN_START: [RQ_W-1:0] requester (2 caches + the IO: 2 bits)
                        self.onyx_mon_port_hits[data & 0x3] += 1
                    elif code in (0x22, 0x24):  # GATHER_DONE / READ_WASTED: [15:12] answering port
                        self.onyx_mon_port_hits[(data >> 12) & 0xF] += 1
                    elif code == 0x27:          # LOCK_WAIT: [7:0] waiting requester
                        self.onyx_mon_port_hits[data & 0xFF] += 1
                    elif code == 0x26 and (data & 0x3) == IO:   # WRITEBACK: the IO's write carries its requester
                        self.onyx_mon_port_hits[IO] += 1
                else:
                    self.onyx_mon_other += 1

    async def run(self):
        """The base's directed scenarios, the IO's directed scenarios, the
        soak (with the IO loop), then the base's quiescence and audits --
        the base run() is unrolled here so the IO scenarios sit before
        the soak and the memory audit covers them."""
        await self._s_init_walk()
        await self._s_pass_dirty_forwarding()
        await self._s_upgrade_invalidates_peer()
        await self._s_dirty_eviction_writeback()
        await self._s_e_downgrade_read_shared()
        await self._s_simultaneous_misses()
        await self._s_ships_in_the_night()
        await self._s_deep_pipelined_misses()
        await self._s_io_read_once()
        await self._s_io_write_unique()
        await self._s_io_concurrent()
        if self.TEST_LEVEL in ('func', 'full'):
            await self._random_lockstep(self.FULL_TXN[self.TEST_LEVEL])
            await self._hot_set_contention(self.FULL_TXN[self.TEST_LEVEL])
            self._scenario('HotSetContention')
            if self.USE_MONITOR == 0:
                self._scenario('MonbusPresentVsAbsent')
        await self._quiescence()
        self._check_fabric_stats()
        await self._memory_audit()
        ok = self.mismatches == 0
        # let the observer drain its holders and queue and emit a final drop
        # report before the account is taken
        await self.wait_clocks('clk', 64)
        m = self.onyx_mon
        s = self.stats
        grants = sum(s['grants'])
        d = self.dut
        cnt = {k: int(getattr(d, f'cnt_{k}').value)
               for k in ('txn', 'supplied', 'mem_read', 'read_wasted', 'absorb', 'wb')}
        self.onyx_cnt = cnt
        # the counters are exact against the model (independent of USE_MONITOR)
        self._score("onyx counters: txn == grants", cnt['txn'], grants)
        self._score("onyx counters: mem_read == memory ARs", cnt['mem_read'], s['mem_ar'])
        self._score("onyx counters: absorb == absorptions", cnt['absorb'], s['absorbs'])
        self._score("onyx counters: read_wasted == reads dropped", cnt['read_wasted'], s['r_dropped'])
        self._score("onyx counters: supplied == forwarded lines", cnt['supplied'], s['dt_forwards'])
        # the TB's own event count (from the taps) equals the counters: the
        # window model is anchored to the exact instrument
        ea = self.exp_all
        for ev, ck in (('TXN_START', 'txn'), ('MEM_READ', 'mem_read'), ('READ_WASTED', 'read_wasted'),
                       ('ABSORB', 'absorb'), ('WRITEBACK', 'wb')):
            self._score(f"onyx taps: {ev} events == counter", ea[ev], cnt[ck])
        # every grant with peers gathers once; a ReadNoSnoop has no peers
        self._score("onyx taps: GATHER_DONE events == grants with peers", ea['GATHER_DONE'],
                    grants - self.io_stats['nosnoop_grants'])
        if self.USE_MONITOR and self.mon_enable:
            # the observer sees every in-window event the taps saw, less what
            # it reported lost; every class it carries is bounded by that; a
            # class the perf mask drops is never seen and never lost; with
            # the window off the bound is the counter itself
            short = 0
            for ev in ONYX_EV.values():
                exp = self.exp_win[ev]
                if self._class_masked(ev):
                    self._score(f"onyx observer: masked {ev} silent", m[ev], 0)
                    continue
                self._score(f"onyx observer: {ev} <= its in-window count", m[ev] <= exp, True)
                short += exp - m[ev]
            if self.mon_win:
                self.log.info(f"onyx observer window {self.mon_win}: in-window {self.exp_win} of {ea}")
            lost = self.onyx_mon_lost + int(d.mon2_dropped.value)
            if self.mon_port_mask:
                # a masked port's events are dropped at the source, neither
                # carried nor lost: the shortfall is not accounted, the
                # masked port is never seen
                for p in range(N_REQ):
                    if self.mon_port_mask & (1 << p):
                        self._score(f"onyx observer: masked port {p} never seen",
                                    self.onyx_mon_port_hits[p], 0)
            else:
                # a loss not yet reported sits in dropped_count
                self._score("onyx observer: shortfall accounted by drop reports",
                            short <= lost, True)
                if short > lost:
                    self.log.error(f"onyx observer: shortfall {short} > lost {lost} "
                                   f"(reported {self.onyx_mon_lost}, residual {int(d.mon2_dropped.value)}); "
                                   f"mon {m} counters {cnt}")
            self._score("onyx observer: no foreign code", self.onyx_mon_other, 0)
            self.log.info(f"onyx observer: {self.onyx_mon_total} packets, {self.onyx_mon_drop_reports} "
                          f"drop reports for {self.onyx_mon_lost} lost events; "
                          f"port hits {self.onyx_mon_port_hits}; counters {cnt}; events {ea}")
        elif self.USE_MONITOR:
            # cfg_mon_enable 0: nothing transmitted, nothing counted as lost
            self._score("onyx observer disabled: silent", self.onyx_mon_total, 0)
            self._score("onyx observer disabled: nothing lost", int(d.mon2_dropped.value), 0)
        else:
            self._score("nomon: onyx observer silent", self.onyx_mon_total, 0)
        return ok and self.mismatches == 0


    # ==================================================================
    # The IO port (D1): the fabric model's third requester
    # ==================================================================
    def _ft_on_line(self, line, exclude=None):
        """The live transaction on this line of any requester but
        `exclude` (the per-line rule makes it unique)."""
        for g in range(N_REQ):
            if g == exclude:
                continue
            ft = self.ft_live.get((g, line))
            if ft is not None:
                return ft
        return None

    def _ft_npeer(self, ft):
        """Peers a transaction snoops: a cache's N-1, the IO's N (shareable)
        or none."""
        if ft['dir'] != IO:
            return N_PORTS - 1
        return N_PORTS if ft['shareable'] else 0

    def _mem_bytes(self, addr, n):
        out = bytearray()
        a = addr
        while len(out) < n:
            line = self._line_of(a)
            off = a & (self.LINE_BYTES - 1)
            take = min(n - len(out), self.LINE_BYTES - off)
            out += self.mem[line][off:off + take]
            a += take
        return bytes(out)

    def _mem_merge_beat(self, beat_addr, wdata, wstrb):
        """A W beat lands in the memory model: the bus-aligned window at
        beat_addr, the strobed bytes only."""
        base = beat_addr & ~(self.STRB_W - 1)
        line = self._line_of(base)
        off = base & (self.LINE_BYTES - 1)
        for i in range(self.STRB_W):
            if (wstrb >> i) & 1:
                self.mem[line][off + i] = (wdata >> (8 * i)) & 0xFF

    def _rand_addr(self, rng):
        """The CPU loops keep out of the IO's region (the span's top tag
        row): a non-shareable IO access to a line a cache holds dirty is
        software's contract, which the random soak does not sign."""
        line = rng.randrange(self.IO_BASE_LINE)
        beat = rng.randrange(self.FILL_BEATS)
        return self._base_of(line) + beat * self.STRB_W

    # ---------------- the IO watcher: the port's own handshakes
    async def _watch_io(self):
        d = self.dut
        f = d.u_fabric
        dbg = int(os.environ.get('ONYX_IO_DEBUG', '0'))
        while True:
            await FallingEdge(d.clk)
            await Timer(100, units='ps')
            if dbg:
                ac = int(f.evt_ac.value)
                g = int(f.dbg_grant.value)
                cr = (int(d.s0_crvalid.value) & int(d.s0_crready.value)) | ((int(d.s1_crvalid.value) & int(d.s1_crready.value)) << 1)
                if ac or g or cr or (int(d.io_arvalid.value) and int(d.io_arready.value)):
                    self.log.info(
                        f"IODBG c{self.cyc} grant {g} dir {int(f.dbg_grant_dir.value)} slot {int(f.dbg_grant_slot.value)} "
                        f"cls {int(f.evt_grant_cls.value)} npeer {int(f.w_grant_npeer.value)} ac {ac:02b} "
                        f"acslot {int(f.w_ac_slot[0].value)}/{int(f.w_ac_slot[1].value)} cr {cr:02b} "
                        f"snihead {int(f.w_sni_head[0].value)}/{int(f.w_sni_head[1].value)} "
                        f"snq {int(f.r_snq_cnt[0].value)}/{int(f.r_snq_cnt[1].value)} sni {int(f.r_sni_cnt[0].value)}/{int(f.r_sni_cnt[1].value)} "
                        f"acleft {[int(f.r_ac_left[i].value) for i in range(4)]} crleft {[int(f.r_cr_left[i].value) for i in range(4)]} "
                        f"vld {int(f.dbg_slot_vld.value):#x} ioar {int(d.io_arvalid.value)}{int(d.io_arready.value)}")
            # AR take: the live IO read's AR is the one presented
            if int(d.io_arvalid.value) and int(d.io_arready.value):
                ft = self.ft_live.get((IO, self._line_of(int(d.io_araddr.value))))
                if ft is None or ft.get('kind') != 'rd':
                    self._score("io: AR taken with no live IO read on its line",
                                int(d.io_araddr.value), None)
                else:
                    self._score(f"io{ft['cyc']}: AR fields as issued",
                                (int(d.io_arid.value), int(d.io_araddr.value), int(d.io_arlen.value),
                                 int(d.io_arsize.value)),
                                (ft['id'], ft['addr'], ft['nbeats'] - 1, ft['size']))
                    ft['ar_taken'] = True
            # R beats: collected, scored at RLAST
            if int(d.io_rvalid.value) and int(d.io_rready.value):
                rid = int(d.io_rid.value)
                ft = None
                for g_line, cand in self.ft_live.items():
                    if g_line[0] == IO and cand.get('kind') == 'rd' and cand.get('ar_taken'):
                        ft = cand
                if ft is None:
                    self._score("io: R beat with no live IO read", rid, None)
                else:
                    ft['beats'].append(int(d.io_rdata.value))
                    self._score(f"io{ft['cyc']}: RID", rid, ft['id'])
                    self._score(f"io{ft['cyc']}: RRESP OKAY", int(d.io_rresp.value) & 0x3, 0)
                    if int(d.io_rlast.value):
                        self._score(f"io{ft['cyc']}: RLAST on beat {ft['nbeats']}",
                                    len(ft['beats']), ft['nbeats'])
                        self._score_io_read(ft)
                        ft['rlast'] = True
                    elif len(ft['beats']) >= ft['nbeats']:
                        self._score(f"io{ft['cyc']}: beats past the burst without RLAST", 1, 0)
            # AW take: a WriteUnique's slot (live) or a WriteNoSnoop (queued)
            if int(d.io_awvalid.value) and int(d.io_awready.value):
                addr = int(d.io_awaddr.value)
                ft = self.ft_live.get((IO, self._line_of(addr)))
                if ft is not None and ft.get('kind') == 'wr':
                    self._score(f"io{ft['cyc']}: WriteUnique AW forwarded only once gathered"
                                f" and absorbed",
                                (len(ft['cr_peers']) == self._ft_npeer(ft),
                                 (not ft.get('pd')) or ft.get('absorbed', False)), (True, True))
                    ft['aw_taken'] = True
                    self.io_aw_cur = ft
                elif self.io_pass:
                    ft = self.io_pass.popleft()
                    self._score(f"io{ft['cyc']}: WriteNoSnoop AW as issued", addr, ft['addr'])
                    ft['aw_taken'] = True
                    self.io_aw_cur = ft
                else:
                    self._score("io: AW taken with no IO write pending", addr, None)
                if self.io_aw_cur is not None:
                    self._score(f"io{self.io_aw_cur['cyc']}: AW fields as issued",
                                (int(d.io_awid.value), addr, int(d.io_awlen.value), int(d.io_awsize.value)),
                                (self.io_aw_cur['id'], self.io_aw_cur['addr'],
                                 self.io_aw_cur['nbeats'] - 1, self.io_aw_cur['size']))
                    self.io_aw_cur['beat_next'] = 0
            # W beats land in the memory model as the sdpram takes them
            if int(d.io_wvalid.value) and int(d.io_wready.value):
                ft = self.io_aw_cur
                if ft is None:
                    self._score("io: W beat with no AW taken", 1, 0)
                else:
                    k = ft['beat_next']
                    beat_addr = ft['addr'] + (k << ft['size'])
                    self._mem_merge_beat(beat_addr, int(d.io_wdata.value), int(d.io_wstrb.value))
                    ft['beat_next'] = k + 1
                    if int(d.io_wlast.value):
                        self._score(f"io{ft['cyc']}: WLAST on beat {ft['nbeats']}", k + 1, ft['nbeats'])
                        ft['w_done'] = True
            # an absorption's BRESP for an IO slot: its line is in memory
            if int(d.oc_evt_absorb.value):
                for g_line, cand in self.ft_live.items():
                    if g_line[0] == IO and cand.get('slot') == int(d.oc_evt_absorb_slot.value):
                        cand['absorbed'] = True
            # B: the write is done; a WriteUnique's slot frees after it
            if int(d.io_bvalid.value) and int(d.io_bready.value):
                ft = self.io_aw_cur
                if ft is None or not ft.get('w_done'):
                    self._score("io: B with no completed IO write", 1, 0)
                else:
                    self._score(f"io{ft['cyc']}: BID", int(d.io_bid.value), ft['id'])
                    self._score(f"io{ft['cyc']}: BRESP OKAY", int(d.io_bresp.value), 0)
                    ft['b_seen'] = True
                    self.io_aw_cur = None

    def _score_io_read(self, ft):
        """The IO read's beats against the expectation: the supplier's line
        (DT) from the AR's offset, else the memory model as it stood at
        the memory AR."""
        got = ft['beats']
        exp = []
        if ft['shareable'] and ft.get('dt'):
            src = ft['data_actual']
            off = ft['addr'] & (self.LINE_BYTES - 1)
            for k in range(ft['nbeats']):
                lo = off + k * self.STRB_W
                exp.append(int.from_bytes(bytes(src[lo:lo + self.STRB_W]), 'little'))
            what = "the supplier's line"
        else:
            snap = ft.get('mem_snap')
            if snap is None:
                self._score(f"io{ft['cyc']}: read data with no memory snapshot (no memory AR?)", 1, 0)
                return
            bb = 1 << ft['size']
            for k in range(ft['nbeats']):
                a = ft['addr'] + k * bb
                lane = a & (self.STRB_W - 1)
                chunk = snap[k * bb:(k + 1) * bb]
                exp.append(int.from_bytes(chunk, 'little') << (8 * lane))
            what = "memory at the AR"
        self._score(f"io{ft['cyc']}: read data == {what} ({ft['nbeats']} beats @ {ft['addr']:#x})",
                    [hex(x) for x in got], [hex(x) for x in exp])
        self.io_stats['beats_scored'] += len(got)

    # ---------------- the fabric-layer hooks, three requesters
    def _on_fab_grant(self, g, addr, slot):
        line = self._line_of(addr)
        if g != IO:
            self._score(f"grant{g} line={line:#x}: no live IO transaction on the line",
                        (IO, line) in self.ft_live, False)
            return super()._on_fab_grant(g, addr, slot)
        cls = int(self.dut.u_fabric.evt_grant_cls.value)
        ft = None
        for cand in self.ft_queue[IO]:
            if cand['cls'] == cls and cand['line'] == line:
                ft = cand
                break
        if ft is None:
            self._score(f"io grant class {cls} line={line:#x}: no IO request queued for it",
                        [(c['cls'], hex(c['line'])) for c in self.ft_queue[IO]], None)
            return
        self.ft_queue[IO].remove(ft)
        self._score(f"io{ft['cyc']}: no live transaction on the line",
                    self._ft_on_line(line) is not None, False)
        ft.update({'slot': slot, 'grant_cyc': self.cyc, 'ac_peers': set(), 'cr_peers': set(),
                   'peer_res': {}, 'resolution': None, 'data_actual': None, 'dt': False, 'pd': False,
                   'mem_ar': False, 'mem_done': False, 'rack': True, 'cd_beats': 0,
                   'ac_done': False, 'cr_done': False})
        if self._ft_npeer(ft) == 0:
            ft['resolution'] = 0
            ft['ac_done'] = ft['cr_done'] = True
            self.io_stats['nosnoop_grants'] += 1
        self.ft_live[(IO, line)] = ft
        self._score(f"io{ft['cyc']}: slot {slot} free at the grant", slot in self.slot_ft, False)
        self.slot_ft[slot] = ft
        self.stats['grants'][IO] += 1
        self.stats['max_live'] = max(self.stats['max_live'], len(self.ft_live))

    def _on_mem_ar(self, arid, addr):
        ft = self.slot_ft.get(arid)
        if ft is None or ft['dir'] != IO:
            return super()._on_mem_ar(arid, addr)
        self._score(f"io{ft['cyc']}: memory AR is the IO's own",
                    (addr, int(self.dut.u_fabric.mem_arlen.value), int(self.dut.u_fabric.mem_arsize.value)),
                    (ft['addr'], ft['nbeats'] - 1, ft['size']))
        self._score(f"io{ft['cyc']}: memory AR once", ft['mem_ar'], False)
        self._score(f"io{ft['cyc']}: no memory read for an IO write", ft['kind'], 'rd')
        self._score(f"io{ft['cyc']}: memory AR only after every peer accepted its AC",
                    len(ft['ac_peers']), self._ft_npeer(ft))
        if ft['cr_done'] and ft['dt'] and ft.get('mar_pres', self.cyc) > ft.get('cr_cyc', -1):
            self._score(f"io{ft['cyc']}: memory AR first presented after a DataTransfer verdict", 1, 0)
        ft['mem_ar'] = True
        ft['mem_snap'] = self._mem_bytes(ft['addr'], ft['nbeats'] << ft['size'])

    def _on_mem_r(self, rid, last):
        ft = self.slot_ft.get(rid)
        if ft is None or ft['dir'] != IO:
            return super()._on_mem_r(rid, last)
        # the beats are consumed once the verdict is in, or dropped as soon as
        # a DataTransfer is known (one peer's CR decides, the other's may be
        # outstanding -- the IO snoops two)
        self._score(f"io{ft['cyc']}: memory beat consumed after the verdict or a known DataTransfer",
                    ft['cr_done'] or ft['dt'], True)
        if last:
            ft['mem_done'] = True
            if ft['dt']:
                self.stats['r_dropped'] += 1

    def _on_slot_free(self, slot):
        ft = self.slot_ft.get(slot)
        if ft is None or ft['dir'] != IO:
            return super()._on_slot_free(slot)
        self.slot_ft.pop(slot)
        self.ft_live.pop((IO, ft['line']), None)
        npeer = self._ft_npeer(ft)
        self._score(f"io{ft['cyc']}: slot freed with every peer answered", len(ft['peer_res']), npeer)
        if ft['kind'] == 'rd':
            self._score(f"io{ft['cyc']}: slot freed after the IO's last beat", ft.get('rlast', False), True)
            if ft['dt']:
                self._score(f"io{ft['cyc']}: DataTransfer read's memory read dropped or suppressed",
                            ft['mem_ar'] == ft['mem_done'], True)
                if not ft['mem_ar']:
                    self.stats['ar_suppressed'] += 1
                self.stats['dt_forwards'] += 1
                self.io_stats['rd_dt'] += 1
                if ft['pd']:
                    self.io_stats['rd_pd'] += 1
            else:
                self._score(f"io{ft['cyc']}: memory read completed", (ft['mem_ar'], ft['mem_done']), (True, True))
                self.stats['pass_throughs'] += 1
        else:
            self._score(f"io{ft['cyc']}: slot freed after the IO's BRESP", ft.get('b_seen', False), True)
            self._score(f"io{ft['cyc']}: an IO write reads no memory", ft['mem_ar'], False)
            if ft['dt']:
                # the gather supplied a line (absorbed, never read): the
                # counters' "supplied" and the dropped-or-suppressed identity
                self.stats['dt_forwards'] += 1
                self.stats['ar_suppressed'] += 1
                self.io_stats['wr_dt'] += 1

    def _mon_snoop_grant(self, c, a, uc):
        """A snoop granted inside cache c, resolved against the model in the
        RTL's match order (the base's resolution, line for line), then
        recorded on the live transaction of ANY other requester on the
        line.  An IO transaction snoops both caches: its resolution is per
        peer and its verdict their OR; a cache's is the base's."""
        side = self.sides[c]
        addr = int(uc.sn_addr_i.value)
        line = self._line_of(addr)
        name = jp.NAME_BY_CODE[int(uc.sn_type_i.value)]
        got_crresp = int(uc.sn_crresp_o.value)
        side.snoops += 1

        try:
            rtl_src = (f"wb={int(uc.w_src_wb.value)} mshr={int(uc.w_src_mshr.value)} "
                       f"arr={int(uc.w_src_array.value)} ref={int(uc.w_sn_ref.value)} "
                       f"pre_ar={int(uc.w_mshr_pre_ar.value)}")
        except AttributeError:
            rtl_src = '?'
        self._dbg(line, f"snoop grant c{c} {name} crresp={got_crresp:#x} rtl[{rtl_src}] "
                  f"model wb={line in side.wb} passed={line in side.wb_passed} "
                  f"entry={line in side.entries} upgr={side.upgr['valid'] and side.upgr['line'] == line} "
                  f"state={self._installed_state(side, line)}")
        cd = None
        if line in side.wb and line not in side.wb_passed:
            # the base's WB rule (jet-prime BUG-002): the entry passes the
            # line on and ends, or -- its drain started -- drains and
            # answers no further snoop
            res = oracle_step('M', name)
            side.wb_grants += 1
            if (res.crresp >> CRRESP_DT) & 1:
                cd = side.wb[line]
            if side.draining == line:
                side.wb_passed.add(line)
            else:
                del side.wb[line]
                side.wb_order.remove(line)
                side.ended += 1
        elif line in side.entries:
            e = side.entries[line]
            if not e['ar']:
                res = oracle_step('I', name)
                side.pre_ar_answers += 1
            else:
                side.pf_grants += 1
                if e['cls'] == jp.JET_CLS_RU:
                    res = oracle_step('IM', name, pending=e['pend'])
                else:
                    st = 'IS_I' if e['pend'] == 'I' else 'IS'
                    res = oracle_step(st, name, fill='S',
                                      pending=None if e['pend'] == 'I' else e['pend'])
                crresp = res.crresp
                if len(e['beats']) < self.FILL_BEATS:
                    crresp &= jp.CRRESP_NO_DT_MASK
                if e['pend'] != 'I':
                    if res.next_state == 'IS_I':
                        e['pend'] = 'I'
                    else:
                        e['pend'] = res.pending
                res = res._replace(crresp=crresp)
                if (crresp >> CRRESP_DT) & 1:
                    cd = e['src']
        elif (side.upgr['valid'] and line == side.upgr['line']
              and not side.upgr['killed']):
            # (a killed upgrade's line was invalidated by the snoop
            # that killed it: a later snoop resolves on the array, I)
            res = oracle_step('S', name)
            if res.next_state != 'S':
                side.exp_sn_tagwr.append({
                    'line': line, 'set': side.upgr['set'],
                    'way': side.upgr['way'], 'next': res.next_state})
                if res.next_state == 'I':
                    side.upgr['killed'] = True
                    side.kill_count += 1
        else:
            set_idx = self._set_of_line(line)
            way = self._hit_way(side, set_idx, line)
            ref = 'I'
            if way is not None and not self._claimed(side, set_idx, way):
                ref = side.slot_state.get((set_idx, way), 'I')
            res = oracle_step(ref, name)
            if (res.crresp >> CRRESP_DT) & 1:
                cd = self._way_content(side, set_idx, way, line) \
                    if way is not None else self._mem_line(line)
            if ref != 'I' and res.next_state != ref:
                side.exp_sn_tagwr.append({
                    'line': line, 'set': set_idx, 'way': way,
                    'next': res.next_state})

        self._score(f"snoop{c} {name} line={line:#x} crresp (grant)", got_crresp, res.crresp)

        ft = self._ft_on_line(line, exclude=c)
        if ft is None:
            self._score(f"snoop{c} line={line:#x}: no live fabric transaction of another "
                        f"requester on this line", 1, 0)
            return
        dt = (res.crresp >> CRRESP_DT) & 1
        pd = (res.crresp >> CRRESP_PD) & 1
        if ft['dir'] == IO:
            if c in ft['peer_res']:
                self._score(f"io{ft['cyc']}: snooped twice by cache{c}", 1, 0)
            ft['peer_res'][c] = res.crresp
            if dt:
                self._score(f"io{ft['cyc']}: a second DataTransfer (MESI: one holder E/M)", ft['dt'], False)
                ft['dt'] = True
                ft['data_actual'] = cd
                if pd:
                    ft['pd'] = True
                    self.mem[line] = bytearray(cd)
                    self.stats['absorbs'] += 1
            if len(ft['peer_res']) == self._ft_npeer(ft):
                verdict = 0
                for v in ft['peer_res'].values():
                    verdict |= v
                ft['resolution'] = verdict
                if not ft['dt']:
                    ft['data_actual'] = self._mem_line(line)
            return
        if ft['resolution'] is not None:
            self._score(f"ft{ft['cyc']}: snooped twice", 1, 0)
        ft['resolution'] = res.crresp
        if dt:
            ft['data_actual'] = cd
            if pd:
                self.mem[line] = bytearray(cd)
                self.stats['absorbs'] += 1
        else:
            ft['data_actual'] = self._mem_line(line)
        req_side = self.sides[ft['dir']]
        e = req_side.entries.get(ft['line'])
        if e is not None:
            e['src'] = ft['data_actual']

    def _on_ace_channels(self, c):
        """The fabric<->cache c ACE responder channels (the base's scoring,
        with the live transaction looked up across all requesters and the
        IO's bookkeeping per peer)."""
        d = self.dut
        acvalid = int(getattr(d, f's{c}_acvalid').value)
        acready = int(getattr(d, f's{c}_acready').value)
        cdvalid = int(getattr(d, f's{c}_cdvalid').value)
        cdready = int(getattr(d, f's{c}_cdready').value)
        crvalid = int(getattr(d, f's{c}_crvalid').value)
        crready = int(getattr(d, f's{c}_crready').value)

        if acvalid and acready:
            snoop = int(getattr(d, f's{c}_acsnoop').value)
            acaddr = int(getattr(d, f's{c}_acaddr').value)
            line = self._line_of(acaddr)
            ft = self._ft_on_line(line, exclude=c)
            if ft is None:
                self._score(f"AC at cache{c} line={line:#x}: no live fabric transaction of "
                            f"another requester", 1, 0)
            else:
                if ft['dir'] == IO:
                    self._score(f"io{ft['cyc']}: cache{c} snooped once", c in ft['ac_peers'], False)
                    ft['ac_peers'].add(c)
                    ft['ac_done'] = len(ft['ac_peers']) == self._ft_npeer(ft)
                else:
                    self._score(f"ft{ft['cyc']}: snooped once", ft['ac_done'], False)
                    ft['ac_done'] = True
                ft['snoop_type'] = FRAMEWORK_SNOOPS.get(SNOOP_NAME_BY_FAB.get(snoop))
                self._score(f"ft{ft['cyc']}: acsnoop", snoop, FAB_SNOOP_BY_TYPE[ft['type']])
                self._score(f"ft{ft['cyc']}: acaddr line-aligned", acaddr & (self.LINE_BYTES - 1), 0)
                self.ft_snq[c].append(ft)
                self._score(f"ft{ft['cyc']}: snoops outstanding at cache{c} within SNOOP_INFLIGHT",
                            len(self.ft_snq[c]) <= self.SNOOP_INFLIGHT, True)
        head = self.ft_snq[c][0] if self.ft_snq[c] else None
        head_base = self._base_of(head['line']) if head is not None else 0
        head_type = head.get('snoop_type') if head is not None else None

        def head_res():
            if head is None:
                return None
            if head['dir'] == IO:
                return head['peer_res'].get(c)
            return head.get('resolution')

        if cdvalid and cdready:
            self._cd_beats[c] += 1
            if not self._cd_started[c]:
                self._cd_started[c] = True
                res = head_res()
                if res is not None and (res >> CRRESP_DT) & 1:
                    self.ace_checkers[c].set_expected_cd_beats(self.FILL_BEATS)
            last = int(getattr(d, f's{c}_cdlast').value)
            self.ace_checkers[c].check_cd_order(self._cd_seq[c], last, head_base, head_type)
            if last:
                self._cd_seq[c] += 1
                self._cd_started[c] = False
        if crvalid and crready:
            crresp = int(getattr(d, f's{c}_crresp').value)
            if head is None:
                self._score(f"CR at cache{c} with no snoop outstanding", 1, 0)
            else:
                self.ft_snq[c].pop(0)
                res = head_res()
                self._score(f"ft{head['cyc']}: crresp (cache{c})", crresp, res)
                exp_beats = self.FILL_BEATS if res is not None and (res >> CRRESP_DT) & 1 else 0
                self._score(f"ft{head['cyc']}: cd beats", self._cd_beats[c], exp_beats)
                if head['dir'] == IO:
                    head['cr_peers'].add(c)
                    head['cr_done'] = len(head['cr_peers']) == self._ft_npeer(head)
                else:
                    head['cr_done'] = True
                head['cr_cyc'] = self.cyc
            self.ace_checkers[c].check_cr_order(self._ace_seq[c], head_base, head_type)
            if head_type is not None:
                self.ace_checkers[c].check_crresp_validity(CRRESP(crresp), head_type, head_base)
            self._ace_seq[c] += 1
            self._cd_beats[c] = 0

    def _check_fabric_stats(self):
        self._score("fabric: no live transaction left", list(self.ft_live.keys()), [])
        self._score("fabric: no request left queued", [len(q) for q in self.ft_queue], [0] * N_REQ)
        self._score("fabric: no snoop left outstanding", [len(q) for q in self.ft_snq], [0, 0])
        self._score("fabric: pending queue never overflowed", int(self.dut.u_fabric.r_pend_ovf.value), 0)
        self._score("fabric: at least one coherence grant", sum(self.stats['grants']) > 0, True)
        self._score("fabric: every DataTransfer fill's memory read was dropped or suppressed",
                    self.stats['r_dropped'] + self.stats['ar_suppressed'], self.stats['dt_forwards'])
        self._score("io: no WriteNoSnoop left awaiting its AW", len(self.io_pass), 0)
        self._score("io: no IO write left mid-burst", self.io_aw_cur, None)
        for c in range(2):
            rep = self.ace_checkers[c].get_compliance_report()
            self._score(f"ACE compliance violations (cache{c})", rep['total_violations'], 0)
        if self.USE_MONITOR == 0:
            for c in range(2):
                self._score(f"nomon{c}: observer silent", self._mon_pkts[c], 0)

    async def _quiescence(self):
        await super()._quiescence()
        f = self.dut.u_fabric
        self._score("quiescent: no IO read in flight", int(f.r_ior_busy.value), 0)
        self._score("quiescent: no IO write in flight", int(f.r_iow_busy.value), 0)

    # ---------------- the IO driver
    def _io_ctx(self, kind, addr, nbeats, size, shareable, cls, label):
        self._io_id = (self._io_id + 1) & 0xFF
        return {'cyc': self.cyc, 'dir': IO, 'line': self._line_of(addr), 'type': cls, 'cls': cls,
                'kind': kind, 'addr': addr, 'nbeats': nbeats, 'size': size, 'shareable': shareable,
                'id': self._io_id, 'label': label, 'beats': [], 'resolution': None,
                'data_actual': None, 'dt': False, 'pd': False, 'ac_peers': set(), 'cr_peers': set(),
                'peer_res': {}, 'mem_ar': False, 'mem_done': False}

    async def _io_read(self, addr, nbeats, shareable, label=''):
        """One IO read: ReadOnce (shareable) or ReadNoSnoop; full-width INCR
        beats.  Queued for the model before the AR is presented; its data
        is scored on the wire."""
        self._dbg(self._line_of(addr), f"IO read issue {label} sh={shareable} n={nbeats}")
        size = self.STRB_W.bit_length() - 1
        ctx = self._io_ctx('rd', addr, nbeats, size, shareable, CLS_IO_READ, label)
        self.ft_queue[IO].append(ctx)
        self.io_stats['reads'] += 1
        if shareable:
            self.io_stats['reads_sh'] += 1
        try:
            data = await self.io_rd.read_transaction(
                address=addr, burst_len=nbeats, snoop_type=ARSnoop.READ_ONCE,
                domain=DOMAIN_OUTER_SHAREABLE if shareable else DOMAIN_NON_SHAREABLE, id=ctx['id'])
        except Exception:
            await self._io_hang_trace(label)
            raise
        self._score(f"io{ctx['cyc']}: the BFM received the burst", len(data), nbeats)
        return data

    async def _io_hang_trace(self, label):
        d = self.dut
        f = d.u_fabric
        for _ in range(4):
            await self._negedge_settled()
            self.log.info(
                f"IO HANG {label} c{self.cyc}: slots {int(f.dbg_slot_vld.value):#x} "
                f"ior_busy {int(f.r_ior_busy.value)} ior_slot {int(f.r_ior_slot.value)} "
                f"iow_busy {int(f.r_iow_busy.value)} arw {int(f.r_arw_vld.value):03b} "
                f"io_ar {int(d.io_arvalid.value)}{int(d.io_arready.value)} "
                f"io_r {int(d.io_rvalid.value)}{int(d.io_rready.value)} "
                f"io_aw {int(d.io_awvalid.value)}{int(d.io_awready.value)} "
                f"mem_ar {int(f.mem_arvalid.value)}{int(f.mem_arready.value)} id {int(f.mem_arid.value)} "
                f"mem_r {int(f.mem_rvalid.value)}{int(f.mem_rready.value)} rid {int(f.mem_rid.value)} "
                f"mar_vld {int(f.r_mar_vld.value)} rpl {int(f.r_rpl_vld.value):03b} "
                f"wstate {int(f.r_wstate.value)} wsel {int(f.r_w_sel.value)} "
                f"s0 ac{int(d.s0_acvalid.value)}{int(d.s0_acready.value)} cr{int(d.s0_crvalid.value)} "
                f"s1 ac{int(d.s1_acvalid.value)}{int(d.s1_acready.value)} cr{int(d.s1_crvalid.value)} "
                f"sni {int(f.r_sni_cnt[0].value)}/{int(f.r_sni_cnt[1].value)} "
                f"snq {int(f.r_snq_cnt[0].value)}/{int(f.r_snq_cnt[1].value)} "
                f"live {[(k[0], hex(k[1])) for k in self.ft_live]}")
            for sl in range(len(f.r_vld)):
                if (int(f.dbg_slot_vld.value) >> sl) & 1:
                    self.log.info(
                        f"IO HANG slot {sl}: dir {int(f.r_dir[sl].value)} type {int(f.r_type[sl].value)} "
                        f"line {int(f.r_line[sl].value):#x} ar_taken {int(f.r_ar_taken.value) >> sl & 1} "
                        f"nodata {int(f.r_nodata.value) >> sl & 1} ac_left {int(f.r_ac_left[sl].value)} "
                        f"cr_left {int(f.r_cr_left[sl].value)} dt {int(f.r_dt.value) >> sl & 1} "
                        f"mem_issued {int(f.r_mem_issued.value) >> sl & 1} mem_done {int(f.r_mem_done.value) >> sl & 1} "
                        f"rpl_done {int(f.r_rpl_done.value) >> sl & 1} rack {int(f.r_rack.value) >> sl & 1} "
                        f"iow {int(f.r_iow.value) >> sl & 1}")

    async def _io_write(self, addr, beats, shareable, strb=None, line_unique=False, label=''):
        """One IO write: WriteUnique / WriteLineUnique (shareable) or
        WriteNoSnoop; full-width INCR beats with one strobe for the burst.
        A shareable write is queued for the model (it takes a slot); a
        non-shareable one awaits its AW on the pass-through queue."""
        self._dbg(self._line_of(addr), f"IO write issue {label} sh={shareable} lu={line_unique}")
        size = self.STRB_W.bit_length() - 1
        cls = CLS_IO_WRITE
        ctx = self._io_ctx('wr', addr, len(beats), size, shareable, cls, label)
        if strb is None:
            strb = (1 << self.STRB_W) - 1
        ctx['strb'] = strb
        if shareable:
            self.ft_queue[IO].append(ctx)
            self.io_stats['writes_sh'] += 1
        else:
            self.io_pass.append(ctx)
        self.io_stats['writes'] += 1
        snoop = AWSnoop.WRITE_LINE_UNIQUE if line_unique else AWSnoop.WRITE_UNIQUE
        res = await self.io_wr.write_transaction(
            address=addr, data=list(beats), burst_len=len(beats), snoop_type=snoop,
            domain=DOMAIN_OUTER_SHAREABLE if shareable else DOMAIN_NON_SHAREABLE,
            id=ctx['id'], strb=strb)
        if not res.get('success'):
            await self._io_hang_trace(label)
        self._score(f"io{ctx['cyc']}: write response OKAY", res.get('success'), True)
        return res

    async def _io_settle(self, n=16):
        for _ in range(n):
            await self._negedge_settled()

    # ---------------- directed IO scenarios (gate)
    async def _s_io_read_once(self):
        """ReadOnce against M (the house table: pass dirty, invalidate),
        E (DT, the holder to S), S (no DT, the memory's bytes) and nothing;
        ReadNoSnoop in the IO's region."""
        s0, s1 = self.sides
        n = self.FILL_BEATS
        # (a) M: the IO reads the cache's dirty bytes, the line is absorbed
        #     and the holder invalidated
        addr = self._compose_addr(self._dtag(), 5 % self.SETS)
        line = self._line_of(addr)
        wdata = 0xA5A5_5A5A_0F0F_F0F0 & ((1 << self.BUS_WIDTH) - 1)
        await self._txn(0, addr, 1, be=(1 << self.STRB_W) - 1, wdata=wdata, label='io_a_wr')
        self._score("io a: cache0 line M", self._installed_state(s0, line), 'M')
        content = bytes(self._content(s0, line))
        abs0, dt0 = self.stats['absorbs'], self.stats['dt_forwards']
        data = await self._io_read(addr, n, True, 'io_a_rd')
        self._score("io a: ReadOnce returned the holder's line",
                    [hex(x) for x in data], [hex(self._beat_of_line(content, b)) for b in range(n)])
        await self._io_settle()
        self._score("io a: the dirty line absorbed", self.stats['absorbs'], abs0 + 1)
        self._score("io a: one DataTransfer", self.stats['dt_forwards'], dt0 + 1)
        self._score("io a: memory holds the holder's bytes", bytes(self.mem[line]), content)
        self._score("io a: cache0 invalidated (M x ReadOnce -> I)", self._installed_state(s0, line), 'I')
        # the cache's re-read misses and fills the absorbed line from memory
        await self._txn(0, addr, 0, label='io_a_rb')
        self._score("io a: cache0 re-read sees its own bytes", self.rsp_log[0][-1][1],
                    self._beat_of_line(content, 0))
        # (b) E: DT, no PD; the holder downgrades to S.  Two beats from the
        #     middle of the line (the IO's offset and length within it)
        addr = self._compose_addr(self._dtag(), 6 % self.SETS)
        line = self._line_of(addr)
        await self._txn(0, addr, 0, label='io_b_r0')
        set_idx = self._set_of_line(line)
        way = self._hit_way(s0, set_idx, line)
        tag_word = self.dut.u_jet0.u_coh.u_tag.g_way[way].mem[set_idx]
        tag_word.value = ((line >> self.SET_BITS) << 3) | 2   # 2 = E (the quiescent promotion backdoor)
        s0.slot_state[(set_idx, way)] = 'E'
        content = bytes(self._content(s0, line))
        abs0 = self.stats['absorbs']
        beat0 = min(2, n - 2)
        data = await self._io_read(addr + beat0 * self.STRB_W, 2, True, 'io_b_rd')
        self._score("io b: ReadOnce two beats from the E holder",
                    [hex(x) for x in data], [hex(self._beat_of_line(content, beat0 + k)) for k in range(2)])
        await self._io_settle()
        self._score("io b: nothing absorbed (clean)", self.stats['absorbs'], abs0)
        self._score("io b: cache0 downgraded E->S", int(tag_word.value) & 7, jp.STATE_CODE['S'])
        s0.slot_state[(set_idx, way)] = 'S'
        # (c) S/S: no DataTransfer; the memory supplies; the holders keep S
        addr = self._compose_addr(self._dtag(), 7 % self.SETS)
        line = self._line_of(addr)
        await self._txn(0, addr, 0, label='io_c_r0')
        await self._txn(1, addr, 0, label='io_c_r1')
        self._score("io c: both S", (self._installed_state(s0, line), self._installed_state(s1, line)), ('S', 'S'))
        dt0 = self.stats['dt_forwards']
        data = await self._io_read(addr, n, True, 'io_c_rd')
        self._score("io c: ReadOnce from memory", [hex(x) for x in data],
                    [hex(self._beat_of_line(self.mem[line], b)) for b in range(n)])
        await self._io_settle()
        self._score("io c: no DataTransfer", self.stats['dt_forwards'], dt0)
        self._score("io c: holders keep S", (self._installed_state(s0, line), self._installed_state(s1, line)), ('S', 'S'))
        # (d) nothing holds it: memory, one beat
        addr = self._compose_addr(self._dtag(), 8 % self.SETS)
        data = await self._io_read(addr + self.STRB_W, 1, True, 'io_d_rd')
        self._score("io d: ReadOnce of an unheld line", hex(data[0]),
                    hex(self._beat_of_line(self.mem[self._line_of(addr)], 1)))
        # (e) ReadNoSnoop in the IO's region: no snoop, the memory's bytes
        line = self.IO_BASE_LINE
        addr = self._base_of(line)
        g0 = list(self.stats['grants'])
        snoops0 = s0.snoops + s1.snoops
        data = await self._io_read(addr, n, False, 'io_e_rd')
        self._score("io e: ReadNoSnoop from memory", [hex(x) for x in data],
                    [hex(self._beat_of_line(self.mem[line], b)) for b in range(n)])
        await self._io_settle()
        self._score("io e: it took a slot", self.stats['grants'][IO], g0[IO] + 1)
        self._score("io e: it snooped nobody", s0.snoops + s1.snoops, snoops0)
        self._scenario('IoReadOnce')

    async def _s_io_write_unique(self):
        """WriteUnique against M (CleanInvalid: the dirty line absorbed,
        the IO's strobed bytes on top, the holder invalidated and its
        re-read sees both), WriteLineUnique against two sharers, WriteUnique
        against E; WriteNoSnoop and ReadNoSnoop in the IO's region."""
        s0, s1 = self.sides
        n = self.FILL_BEATS
        full = (1 << self.STRB_W) - 1
        # (a) M + partial WriteUnique
        addr = self._compose_addr(self._dtag(), 9 % self.SETS)
        line = self._line_of(addr)
        wdata = 0x1122_3344_5566_7788 & ((1 << self.BUS_WIDTH) - 1)
        await self._txn(0, addr, 1, be=full, wdata=wdata, label='iow_a_wr')
        self._score("io w-a: cache0 line M", self._installed_state(s0, line), 'M')
        content = bytearray(self._content(s0, line))
        abs0 = self.stats['absorbs']
        half = (1 << (self.STRB_W // 2)) - 1          # the low half of beat 1
        iod = 0xDEAD_BEEF_CAFE_F00D & ((1 << self.BUS_WIDTH) - 1)
        await self._io_write(addr + self.STRB_W, [iod], True, strb=half, label='iow_a')
        await self._io_settle()
        exp = bytearray(content)
        for i in range(self.STRB_W // 2):
            exp[self.STRB_W + i] = (iod >> (8 * i)) & 0xFF
        self._score("io w-a: the dirty line absorbed first", self.stats['absorbs'], abs0 + 1)
        self._score("io w-a: memory = holder's line with the IO's strobed bytes", bytes(self.mem[line]), bytes(exp))
        self._score("io w-a: cache0 invalidated (CleanInvalid)", self._installed_state(s0, line), 'I')
        await self._txn(0, addr + self.STRB_W, 0, label='iow_a_rb')
        self._score("io w-a: cache0 re-read sees the merged beat", self.rsp_log[0][-1][1],
                    self._beat_of_line(exp, 1))
        # (b) S/S + WriteLineUnique: both invalidated, cache1 re-reads the IO's line
        addr = self._compose_addr(self._dtag(), 10 % self.SETS)
        line = self._line_of(addr)
        await self._txn(0, addr, 0, label='iow_b_r0')
        await self._txn(1, addr, 0, label='iow_b_r1')
        beats = [((0x0101_0101_0101_0101 * (b + 1)) ^ 0x5A5A) & ((1 << self.BUS_WIDTH) - 1) for b in range(n)]
        abs0, dt0 = self.stats['absorbs'], self.stats['dt_forwards']
        await self._io_write(addr, beats, True, line_unique=True, label='iow_b')
        await self._io_settle()
        self._score("io w-b: nothing absorbed, no DataTransfer", (self.stats['absorbs'], self.stats['dt_forwards']), (abs0, dt0))
        self._score("io w-b: both sharers invalidated",
                    (self._installed_state(s0, line), self._installed_state(s1, line)), ('I', 'I'))
        exp_line = b''.join(b.to_bytes(self.STRB_W, 'little') for b in beats)
        self._score("io w-b: memory = the IO's line", bytes(self.mem[line]), exp_line)
        await self._txn(1, addr + 3 * self.STRB_W % self.LINE_BYTES, 0, label='iow_b_rb')
        self._score("io w-b: cache1 re-read sees the IO's beat", self.rsp_log[1][-1][1], beats[3 % n])
        # (c) E + WriteUnique: the holder invalidates without data
        addr = self._compose_addr(self._dtag(), 11 % self.SETS)
        line = self._line_of(addr)
        await self._txn(0, addr, 0, label='iow_c_r0')
        set_idx = self._set_of_line(line)
        way = self._hit_way(s0, set_idx, line)
        tag_word = self.dut.u_jet0.u_coh.u_tag.g_way[way].mem[set_idx]
        tag_word.value = ((line >> self.SET_BITS) << 3) | 2
        s0.slot_state[(set_idx, way)] = 'E'
        dt0 = self.stats['dt_forwards']
        await self._io_write(addr, [0x7777_7777_7777_7777 & ((1 << self.BUS_WIDTH) - 1)], True, label='iow_c')
        await self._io_settle()
        self._score("io w-c: no DataTransfer from E on CleanInvalid", self.stats['dt_forwards'], dt0)
        self._score("io w-c: E holder invalidated", int(tag_word.value) & 7, jp.STATE_CODE['I'])
        s0.slot_state[(set_idx, way)] = 'I'
        await self._txn(0, addr, 0, label='iow_c_rb')
        self._score("io w-c: cache0 re-read sees the IO's beat", self.rsp_log[0][-1][1],
                    self._beat_of_line(self.mem[line], 0))
        # (d) WriteNoSnoop then ReadNoSnoop and ReadOnce of the same bytes
        line = self.IO_BASE_LINE + 1
        addr = self._base_of(line)
        g0 = self.stats['grants'][IO]
        beats = [(0xF0F0_0F0F_1234_5678 + b) & ((1 << self.BUS_WIDTH) - 1) for b in range(n)]
        await self._io_write(addr, beats, False, label='iow_d')
        await self._io_settle()
        self._score("io w-d: WriteNoSnoop took no slot", self.stats['grants'][IO], g0)
        self._score("io w-d: memory = the IO's line",
                    bytes(self.mem[line]), b''.join(b.to_bytes(self.STRB_W, 'little') for b in beats))
        data = await self._io_read(addr, n, False, 'iow_d_rns')
        self._score("io w-d: ReadNoSnoop reads it back", [hex(x) for x in data], [hex(b) for b in beats])
        data = await self._io_read(addr, n, True, 'iow_d_ro')
        self._score("io w-d: ReadOnce reads it back (no holder)", [hex(x) for x in data], [hex(b) for b in beats])
        self._scenario('IoWriteUnique')

    async def _s_io_concurrent(self):
        """A read and a write in flight together (different lines), then a
        read behind a write of its own line (the per-line lock orders them:
        the read returns the written bytes)."""
        n = self.FILL_BEATS
        la = self.IO_BASE_LINE + 2
        lb = self.IO_BASE_LINE + 3
        beats = [(0xC0DE_0000_0000_0000 | b) & ((1 << self.BUS_WIDTH) - 1) for b in range(n)]
        t_rd = cocotb.start_soon(self._io_read(self._base_of(la), n, True, 'ioc_rd'))
        t_wr = cocotb.start_soon(self._io_write(self._base_of(lb), beats, True, label='ioc_wr'))
        data = await t_rd
        await t_wr
        self._score("io cc: read of line A unaffected by the write of line B",
                    [hex(x) for x in data], [hex(self._beat_of_line(self.mem[la], b)) for b in range(n)])
        await self._io_settle()
        self._score("io cc: line B written", bytes(self.mem[lb]),
                    b''.join(b.to_bytes(self.STRB_W, 'little') for b in beats))
        # the same line: the write first, the read waits for its lock
        beats2 = [(0xBEEF_0000_0000_0000 | (b << 8)) & ((1 << self.BUS_WIDTH) - 1) for b in range(n)]
        t_wr = cocotb.start_soon(self._io_write(self._base_of(lb), beats2, True, label='ioc_wr2'))
        await self._negedge_settled()
        t_rd = cocotb.start_soon(self._io_read(self._base_of(lb), n, True, 'ioc_rd2'))
        await t_wr
        data = await t_rd
        self._score("io cc: the read behind the write of its line returns the written bytes",
                    [hex(x) for x in data], [hex(b) for b in beats2])
        await self._io_settle()
        self._scenario('IoConcurrent')

    # ---------------- the random IO loop beside the CPU loops
    async def _io_loop(self, n, rng, coh_lines=None):
        """The IO's soak.  coh_lines (the hot phase): its coherent kinds
        (ReadOnce, WriteUnique, WriteLineUnique) go to those cache lines;
        the non-snooping kinds stay in its own region either way."""
        full = (1 << self.STRB_W) - 1
        for i in range(n):
            r = rng.random()
            nb = rng.randrange(1, self.FILL_BEATS + 1)
            if r < 0.40:
                # ReadOnce anywhere (the caches' lines included)
                line = rng.choice(coh_lines) if coh_lines else rng.randrange(self.SPAN)
                b0 = rng.randrange(self.FILL_BEATS - nb + 1)
                await self._io_read(self._base_of(line) + b0 * self.STRB_W, nb, True, f'io_r{i}')
            elif r < 0.60:
                line = self.IO_BASE_LINE + rng.randrange(self.IO_LINES)
                b0 = rng.randrange(self.FILL_BEATS - nb + 1)
                await self._io_read(self._base_of(line) + b0 * self.STRB_W, nb, False, f'io_rn{i}')
            else:
                line = self.IO_BASE_LINE + rng.randrange(self.IO_LINES)
                if coh_lines and r < 0.90:
                    line = rng.choice(coh_lines)
                b0 = rng.randrange(self.FILL_BEATS - nb + 1)
                beats = [rng.getrandbits(self.BUS_WIDTH) for _ in range(nb)]
                if r < 0.80:
                    await self._io_write(self._base_of(line) + b0 * self.STRB_W, beats, True,
                                         strb=rng.randrange(1, full + 1), label=f'io_wu{i}')
                elif r < 0.90:
                    beats = [rng.getrandbits(self.BUS_WIDTH) for _ in range(self.FILL_BEATS)]
                    await self._io_write(self._base_of(line), beats, True, line_unique=True, label=f'io_wl{i}')
                else:
                    await self._io_write(self._base_of(line) + b0 * self.STRB_W, beats, False,
                                         strb=rng.randrange(1, full + 1), label=f'io_wn{i}')
            for _ in range(rng.randrange(3)):
                await self._negedge_settled()

    async def _random_lockstep(self, n):
        rng0 = random.Random((self.SEED << 1) | 0)
        rng1 = random.Random((self.SEED << 1) | 1)
        rng2 = random.Random((self.SEED << 2) | 2)
        t0 = cocotb.start_soon(self._cpu_loop(0, n, rng0))
        t1 = cocotb.start_soon(self._cpu_loop(1, n, rng1))
        t2 = cocotb.start_soon(self._io_loop(self.IO_TXN[self.TEST_LEVEL], rng2))
        await t0
        await t1
        await t2
        self._scenario('RandomDualCpuPlusIo')

    async def _hot_set_contention(self, n):
        """The base's hot phase plus the IO on the same lines: ReadOnce,
        WriteUnique and WriteLineUnique to lines the caches hold dirty, in
        their WB buffers, or mid-drain (onyx ISSUE-002: until the cache
        side stopped draining a passed-on victim, the soak kept the IO's
        writes in its own region)."""
        lines = self._hot_lines()
        hot = self._hot_addr_fn(lines)
        rng0 = random.Random(((self.SEED << 1) | 0) ^ 0x5EED)
        rng1 = random.Random(((self.SEED << 1) | 1) ^ 0x5EED)
        rng2 = random.Random(((self.SEED << 2) | 2) ^ 0x5EED)
        t0 = cocotb.start_soon(self._cpu_loop(0, n, rng0, hot, 0.7))
        t1 = cocotb.start_soon(self._cpu_loop(1, n, rng1, hot, 0.7))
        t2 = cocotb.start_soon(self._io_loop(self.IO_TXN[self.TEST_LEVEL],
                                             rng2, coh_lines=lines))
        await t0
        await t1
        await t2

    def get_test_report(self):
        rep = super().get_test_report()
        rep['onyx_mon'] = dict(self.onyx_mon, drop_reports=self.onyx_mon_drop_reports,
                               lost=self.onyx_mon_lost, other=self.onyx_mon_other,
                               total=self.onyx_mon_total, port_hits=self.onyx_mon_port_hits,
                               enable=self.mon_enable, perf_mask=self.mon_perf_mask,
                               port_mask=self.mon_port_mask, window=self.mon_win,
                               events=dict(self.exp_all), in_window=dict(self.exp_win))
        rep['onyx_cnt'] = getattr(self, 'onyx_cnt', {})
        rep['onyx_io'] = dict(self.io_stats)
        return rep
