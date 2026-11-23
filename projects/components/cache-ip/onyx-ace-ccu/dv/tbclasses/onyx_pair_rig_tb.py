# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: onyx_pair_rig_tb
# Purpose: jet-prime's pair-rig testbench with one addition for onyx -- the
#   D9 observer's MonBus (mon2) is counted per event code and checked
#   against the testbench's own fabric model.
#
# Subsystem: onyx (cache-ip)
"""The pair-rig testbench, onyx flavor.

`JetPairRigTB` drives both CPUs, keeps the two-cache lockstep model with the
fabric rules and scores the ACE channels; it reads `u_fabric`'s debug taps,
which onyx keeps.  This subclass adds the one thing onyx has that the fabric
did not: an observer.  It counts the packets on `mon2` by event code and,
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
import sys

import cocotb
from cocotb.triggers import RisingEdge

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                '..', '..', '..', 'jet-prime-mesi-l1', 'dv', 'tbclasses'))
from projects.components.cache_ip.jet_prime_mesi_l1.dv.tbclasses.jet_prime_pair_rig_tb import (  # noqa: E402
    JetPairRigTB,
)

ONYX_EV = {0x20: 'TXN_START', 0x22: 'GATHER_DONE', 0x23: 'MEM_READ',
           0x24: 'READ_WASTED', 0x25: 'ABSORB', 0x26: 'WRITEBACK', 0x27: 'LOCK_WAIT'}
PKT_TYPE_ERROR = 0x0


class OnyxPairRigTB(JetPairRigTB):
    """JetPairRigTB plus the onyx observer check."""

    def __init__(self, dut, **kwargs):
        super().__init__(dut, **kwargs)
        self.onyx_mon = {name: 0 for name in ONYX_EV.values()}
        self.onyx_mon_drop_reports = 0
        self.onyx_mon_other = 0
        self.onyx_mon_total = 0
        self.onyx_mon_lost = 0          # the drop reports' payloads summed
        self.onyx_mon_port_hits = [0, 0]   # per-port packets (TXN_START, GATHER_DONE, READ_WASTED, LOCK_WAIT)
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
                      f"port_mask=0b{self.mon_port_mask:02b} window={self.mon_win}")
        await super().setup_clocks_and_reset()
        cocotb.start_soon(self._watch_onyx_mon())
        cocotb.start_soon(self._watch_onyx_events())

    def _in_win(self, addr):
        return self.mon_win is None or (self.mon_win[0] <= addr <= self.mon_win[1])

    async def _watch_onyx_events(self):
        """Count the unit's events per class, all and in-window, from the
        harness's event taps: the model of what the observer must emit."""
        d = self.dut
        n_slots = 1 << len(d.oc_grant_slot)
        slot_win = [False] * n_slots
        lw_active = [False, False]
        lw_win = [False, False]

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
            for p in range(2):
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
                    if code == 0x20:            # TXN_START: [PORT_W-1:0] requesting port (2 ports: bit 0)
                        self.onyx_mon_port_hits[data & 0x1] += 1
                    elif code in (0x22, 0x24):  # GATHER_DONE / READ_WASTED: [15:12] answering port
                        self.onyx_mon_port_hits[(data >> 12) & 0xF] += 1
                    elif code == 0x27:          # LOCK_WAIT: [7:0] waiting port
                        self.onyx_mon_port_hits[data & 0xFF] += 1
                else:
                    self.onyx_mon_other += 1

    async def run(self):
        ok = await super().run()
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
        self._score("onyx taps: GATHER_DONE events == grants", ea['GATHER_DONE'], grants)
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
                for p in range(2):
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

    def get_test_report(self):
        rep = super().get_test_report()
        rep['onyx_mon'] = dict(self.onyx_mon, drop_reports=self.onyx_mon_drop_reports,
                               lost=self.onyx_mon_lost, other=self.onyx_mon_other,
                               total=self.onyx_mon_total, port_hits=self.onyx_mon_port_hits,
                               enable=self.mon_enable, perf_mask=self.mon_perf_mask,
                               port_mask=self.mon_port_mask, window=self.mon_win,
                               events=dict(self.exp_all), in_window=dict(self.exp_win))
        rep['onyx_cnt'] = getattr(self, 'onyx_cnt', {})
        return rep
