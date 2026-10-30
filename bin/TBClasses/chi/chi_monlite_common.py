# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: chi_monlite_common
# Purpose: Role-independent half of the chi_{rnf,hnf}_port_monlite testbenches
#
# Documentation: docs/markdown/rtl-amba/monitor/chi_monitor_lite.md
# Subsystem: amba
# Author: sean galloway
# Created: 2026-10-30
"""MonbusSlave on the ocelus bus, a passive FUB sampler feeding the
spec-level model (chi_monlite_model), and the counted verdict.

The layering is the CXS one (bin/TBClasses/cxs/cxs_monlite_tb.py): the
endpoint testbench (CHIRnfPortTB / CHIHnfPortTB) drives the port with the
framework CHI BFMs; this mixin adds the monitor expectations. Packets are
decoded with the shared decoder (TBClasses.monbus.parse); the payload fields
are then read per the layout table in chi_monlite_model.

Every claim is a count in ``self.counts``; :meth:`final_verdict` fails any
required count that is zero, so a phase that silently did nothing cannot pass.
"""

import os

from cocotb.triggers import ClockCycles, FallingEdge, RisingEdge
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

from TBClasses.chi.chi_monlite_model import (
    PT_COMPL,
    PT_CREDIT,
    PT_ERR,
    PT_TMO,
    ChiMonModel,
    Ev,
    episodes,
    match,
    unpack,
)
from TBClasses.monbus import CHIErrorCode, CHITimeoutCode, ProtocolType, parse
from TBClasses.monbus.monbus_slave import MonbusSlave
from TBClasses.monbus.monbus_types import create_monitor_packet

TS_PATTERN = 0x0123_4567_89AB_CDEF
FREQ_MHZ = int(os.environ.get('ACLK_MHZ', '100'))
EV_DROPPED = int(CHIErrorCode.CHI_ERR_EVENT_DROPPED)


class MonliteMixin:
    """Monitor-side machinery. The host class supplies TAP / BP_CHANNELS."""

    TAP = {}
    BP_CHANNELS = ()
    UNIT_ID = 0x0B
    AGENT_ID = 0x00D0

    def _init_monlite(self):
        self.max_txn = int(os.environ.get('MAX_TRANSACTIONS', '8'))
        self.max_snp = int(os.environ.get('MAX_SNOOPS', '4'))
        self.out_depth = int(os.environ.get('OUT_DEPTH', '4'))
        self.model = ChiMonModel(self.cfg_rn, self.max_txn, self.max_snp)
        self.mbus = None
        self.mon_errors = []
        self.cyc = 0
        self.series = {k: [] for k in ('starved', 'bp', 'tx', 'rx')}
        self.enabled = True
        self._pe_prev = 0
        self.absorbed = []
        self.err_pkts = 0
        self.txn_base = 0
        self.snp_base = 0
        self._prev_lat_check = None

    # ---- pins -----------------------------------------------------------------
    def _monlite_pins(self):
        d = self.dut
        d.cam_clear.value = 0
        d.cfg_monitor_enable.value = 1
        for n in ('error', 'timeout', 'compl', 'channel', 'stream'):
            getattr(d, f'cfg_{n}_enable').value = 1
        d.cfg_credit_enable.value = 0
        d.cfg_timeout_cycles.value = 0
        d.cfg_freq_sel.value = 0
        d.cfg_chi_pkt_mask.value = 0
        d.cfg_stall_threshold.value = 0
        d.i_mon_time.value = TS_PATTERN

    async def deassert_reset(self):
        # The sampler and the monbus slave exist before the link comes up, so
        # the bring-up Stream events are seen from the first one.
        self.mbus = MonbusSlave(dut=self.dut, title="MonBus", prefix="", clock=self.dut.aclk,
                                bus_name="monbus", pkt_prefix="", log=self.log)
        self.set_monbus_ready(0)
        import cocotb
        cocotb.start_soon(self._sampler())
        self.rst_n.value = 1

    def set_monbus_ready(self, delay):
        self.mbus.set_ready_randomizer(FlexRandomizer({'ready_delay': ([(delay, delay)], [1])}))

    # ---- the passive sampler -----------------------------------------------------
    async def _sampler(self):
        d = self.dut
        while True:
            await FallingEdge(self.clk)
            if not int(self.rst_n.value):
                continue
            self.cyc += 1
            msgs, bp = {}, 0
            for name, pfx in self.TAP.items():
                v = int(getattr(d, f'{pfx}_valid').value)
                r = int(getattr(d, f'{pfx}_ready').value)
                if v and r:
                    msgs[name] = int(getattr(d, f'{pfx}_flit').value)
                if v and not r and name in self.BP_CHANNELS:
                    bp = 1
            tx, rx = int(d.tx_link_state.value), int(d.rx_link_state.value)
            if self.enabled:
                self.model.feed(self.cyc, msgs)
                self.model.feed_state(self.cyc, tx, rx)
            else:
                self.model._tx, self.model._rx = tx, rx
            self.series['starved'].append(int(d.credit_starved.value))
            self.series['bp'].append(bp)
            self.series['tx'].append(tx)
            self.series['rx'].append(rx)
            pe = int(d.protocol_error.value)
            if pe and not self._pe_prev and self.enabled:
                from TBClasses.chi.chi_monlite_model import Ev as _Ev
                self.model.events.append(_Ev(PT_ERR, int(CHIErrorCode.CHI_ERR_PROTOCOL), 0, self.cyc,
                                             exact=dict(tx_link=tx, rx_link=rx, txns=self.model.txns),
                                             tag='PROTOCOL'))
            self._pe_prev = pe
            if int(d.monbus_valid.value):
                self.counts['timestamp_checks'] += 1
                if int(d.monbus_timestamp.value) != TS_PATTERN:
                    self.mon_errors.append(f"monbus_timestamp {int(d.monbus_timestamp.value):#x} != i_mon_time")

    # ---- packets ---------------------------------------------------------------
    def take(self):
        """Delivered packets since the last call: [(MonitorPacket, fields)],
        every one decoded by the shared decoder."""
        raw = list(self.mbus.received_packets)
        self.mbus.clear_received_packets()
        out = []
        for p in raw:
            mp = parse(create_monitor_packet(p.pkt_type, p.protocol, p.event_code, p.channel_id,
                                             p.unit_id, p.agent_id, p.data))
            if int(mp.protocol) != int(ProtocolType.PROTOCOL_CHI) or mp.unit_id != self.UNIT_ID \
                    or mp.agent_id != self.AGENT_ID:
                self.mfail(f"packet protocol/unit/agent {mp.protocol}/{mp.unit_id:#x}/{mp.agent_id:#x}")
            fields = unpack(int(mp.packet_type), int(mp.event_code), int(mp.event_data))
            if not fields:
                self.mfail(f"packet with no known layout: type {mp.packet_type} code {mp.event_code}")
            out.append((mp, fields))
            if int(mp.packet_type) == PT_ERR and int(mp.event_code) != EV_DROPPED:
                self.err_pkts += 1
        return out

    def mfail(self, msg):
        self.log.error(msg)
        self.mon_errors.append(msg)

    async def drain(self, cycles=60):
        """Endpoint, event stage and queue empty: monbus_valid low for 20
        consecutive cycles (a drop report is pushed only into an empty queue)."""
        await ClockCycles(self.dut.aclk, cycles)
        quiet = 0
        for _ in range(8000):
            quiet = 0 if int(self.dut.monbus_valid.value) else quiet + 1
            if quiet >= 20:
                return
            await RisingEdge(self.dut.aclk)
        self.mfail("monbus never went quiet")

    # ---- verdict pieces --------------------------------------------------------------
    def verify(self, name, mark, drops_ok=False, mask=0, idle=True):
        """Compare the packets since the last call with the model's events
        since ``mark``. Exact multiset, payload fields included, unless
        ``drops_ok`` (then missing events must be accounted by EVENT_DROPPED)."""
        got = self.take()
        drops = [g for g in got if int(g[0].packet_type) == PT_ERR and int(g[0].event_code) == EV_DROPPED]
        real = [g for g in got if g not in drops]
        reported = sum(f['count'] for _, f in drops)
        expected = [e for e in self.model.events[mark:] if not (mask >> e.ptype) & 1]
        unexpected, missing, pairs = match(expected, real)
        hard_missing = [e for e in missing if not e.optional]
        for e, p, f in pairs:
            self.counts[f'ev_{e.tag}'] += 1
        self.counts['optional_unmatched'] += len(missing) - len(hard_missing)
        for p, f in unexpected[:6]:
            self.mfail(f"{name}: unexpected packet type {int(p.packet_type)} code {int(p.event_code)} "
                       f"chan {int(p.channel_id):#x} {f}")
        if drops_ok:
            if len(hard_missing) > reported or reported > len(missing):
                self.mfail(f"{name}: {len(hard_missing)} events missing (+{len(missing) - len(hard_missing)} "
                           f"optional) but {reported} reported dropped")
            self.counts['drop_reports'] += len(drops)
            self.counts['dropped_reported'] += reported
        else:
            for e in hard_missing[:6]:
                self.mfail(f"{name}: missing {e}")
            if drops:
                self.mfail(f"{name}: unexpected EVENT_DROPPED (count {reported})")
        self.counts['packets_checked'] += len(real)
        self._check_running_counts(name, real, drops_ok)
        if idle:
            self._check_pins(name)
        self.log.info(f"monitor {name}: {len(real)} packets vs {len(expected)} expected, "
                      f"{len(unexpected)} unexpected, {len(hard_missing)} missing, {reported} reported dropped")
        return got

    def _check_running_counts(self, name, real, drops_ok):
        """Completion/TXN+RETRY carry the running retire count; SNP the snoop count."""
        txns = [f['txns'] for p, f in real if int(p.packet_type) == PT_COMPL and 'txns' in f]
        if txns and not drops_ok:
            if txns != sorted(txns) or min(txns) != self.txn_base + 1 or max(txns) != self.model.txns:
                self.mfail(f"{name}: running txn count {txns[:12]}.. not {self.txn_base + 1}..{self.model.txns}")
            self.counts['txn_count_sequences'] += 1
        snps = [f['snps'] for p, f in real if int(p.packet_type) == PT_COMPL and 'snps' in f]
        if snps and not drops_ok:
            if snps != sorted(snps) or min(snps) != self.snp_base + 1 or max(snps) != self.model.snps:
                self.mfail(f"{name}: running snoop count {snps[:12]} not {self.snp_base + 1}..{self.model.snps}")
            self.counts['snoop_count_sequences'] += 1
        self.txn_base, self.snp_base = self.model.txns, self.model.snps

    def _check_pins(self, name):
        d = self.dut
        got = dict(active_count=int(d.active_count.value), txn_count=int(d.txn_count.value),
                   snoop_count=int(d.snoop_count.value), error_count=int(d.error_count.value),
                   dropped_count=int(d.dropped_count.value))
        want = dict(active_count=0, txn_count=self.model.txns, snoop_count=self.model.snps,
                    error_count=self.err_pkts, dropped_count=0)
        for k in want:
            if got[k] != want[k]:
                self.mfail(f"{name}: {k} = {got[k]}, expected {want[k]}")
        self.counts['pin_checks'] += len(want)

    def model_clear(self):
        self.model.slots.clear()
        self.model.snoops.clear()
        self.model.txns = self.model.snps = 0
        self.txn_base = self.snp_base = 0
        self.err_pkts = 0

    # ---- episodes: credit / backpressure / timeouts (series-derived) ---------------------
    def _series_since(self, name, start):
        return self.series[name][start:]

    def add_credit_events(self, start_cyc, threshold):
        """STARVED / BACKPRESSURE for the episodes in the series since
        ``start_cyc``: required when the episode outlasts the threshold by
        two cycles, optional on the boundary. Payload: threshold exact, the
        cycle count the threshold (the event fires on reaching it)."""
        from TBClasses.monbus import CHICreditCode
        for series, code, tag in (('starved', CHICreditCode.CHI_CREDIT_STARVED, 'STARVED'),
                                  ('bp', CHICreditCode.CHI_CREDIT_BACKPRESSURE, 'BACKPRESSURE')):
            s = self._series_since(series, start_cyc)
            for st, ln in episodes(s):
                if ln < threshold:
                    continue
                self.model.events.append(Ev(PT_CREDIT, int(code), 0, start_cyc + st,
                                            exact=dict(thresh=threshold),
                                            rng=dict(cycles=(threshold, threshold + 1)),
                                            optional=ln < threshold + 2, tag=tag,
                                            info=f'episode_len={ln} start_idx={start_cyc + st}'))

    def add_timeout_events(self, start_cyc, cfg_us):
        """Timeout/CREDIT and Timeout/LINK from the series since ``start_cyc``
        (TXN and SNP timeouts come from :meth:`add_slot_timeouts`)."""
        p = FREQ_MHZ
        req_len, opt_len = (cfg_us + 1) * p + 10, max(1, (cfg_us - 1) * p + 1)
        s = self._series_since('starved', start_cyc)
        for st, ln in episodes(s):
            if ln >= opt_len:
                self.model.events.append(Ev(PT_TMO, int(CHITimeoutCode.CHI_TIMEOUT_CREDIT), 0, start_cyc + st,
                                            exact=dict(cfg=cfg_us), rng=dict(age=(cfg_us, cfg_us + 1)),
                                            optional=ln < req_len, tag='TMO_CREDIT'))
        for dname, is_tx in (('tx', 1), ('rx', 0)):
            s = self._series_since(dname, start_cyc)
            runs, cur, begin = [], None, 0
            for i, v in enumerate(s + [-1]):
                if v != cur:
                    if cur in (1, 2) and i - begin >= opt_len:
                        runs.append((begin, i - begin, cur))
                    cur, begin = v, i
            for st, ln, val in runs:
                ex = dict(cfg=cfg_us, is_tx=is_tx, **({'tx_link': val} if is_tx else {'rx_link': val}))
                self.model.events.append(Ev(PT_TMO, int(CHITimeoutCode.CHI_TIMEOUT_LINK), 0, start_cyc + st,
                                            exact=ex, rng=dict(age=(cfg_us, cfg_us + 1)),
                                            optional=ln < req_len, tag='TMO_LINK'))

    def add_slot_timeouts(self, cfg_us, mark):
        """Timeout/TXN and Timeout/SNP for every request / snoop whose life
        (alloc to retire) outlasted the threshold: the model's TXN / SNP /
        RETRY events since ``mark`` carry the life as their latency floor."""
        p, n = FREQ_MHZ, self.max_txn
        req_len, opt_len = (cfg_us + 1) * p + n + 12, max(1, (cfg_us - 1) * p + 1)
        extra = []
        for e in self.model.events[mark:]:
            if e.tag == 'TXN':
                life = e.rng['lat'][0]
                if life >= opt_len:
                    extra.append(Ev(PT_TMO, int(CHITimeoutCode.CHI_TIMEOUT_TXN), e.chan, e.cyc,
                                    exact=dict(txnid=e.chan, cfg=cfg_us, opc=e.exact['opc']),
                                    rng=dict(age=(cfg_us, cfg_us + 1)), optional=life < req_len, tag='TMO_TXN'))
            elif e.tag == 'SNP':
                life = e.rng['lat'][0]
                if life >= opt_len:
                    extra.append(Ev(PT_TMO, int(CHITimeoutCode.CHI_TIMEOUT_SNP), e.chan, e.cyc,
                                    exact=dict(txnid=e.chan, cfg=cfg_us), rng=dict(age=(cfg_us, cfg_us + 1)),
                                    optional=life < req_len, tag='TMO_SNP'))
        self.model.events += extra

    # ---- violations the injected stimulus is MEANT to cause ------------------------------
    def viol_snapshot(self, *bfms):
        return [(b, dict(b.all_violations())) for b in bfms]

    def absorb(self, snap, expect_min=1, what=''):
        """Remove the BFM violations an injection caused (counted, and at
        least ``expect_min`` must have happened: the BFMs saw the stimulus)."""
        total = 0
        for b, before in snap:
            for k, v in b.all_violations().items():
                delta = v - before.get(k, 0)
                if delta <= 0:
                    continue
                total += delta
                holder = None
                if k in b.violations:
                    holder, key = b.violations, k
                elif k.startswith('link.') and hasattr(b, 'checker'):
                    holder, key = b.checker.violations, k[5:]
                else:
                    name, _, key = k.partition('.')
                    for m in list(getattr(b, 'tx', {}).values()) + list(getattr(b, 'rx', {}).values()):
                        if m.name == name and key in m.violations:
                            holder = m.violations
                if holder is None:
                    self.mfail(f"{what}: violation {k} on {b.title} cannot be absorbed")
                else:
                    holder[key] -= delta
        self.counts['absorbed_violations'] += total
        if total < expect_min:
            self.mfail(f"{what}: expected the BFMs to flag the injected stimulus, saw {total}")
        return total

    def final_verdict(self, tag, required):
        for e in self.mon_errors[:20]:
            self.log.error(e)
        for e in self.model.errors[:10]:
            self.errors.append(e)
        for k in required:
            if self.counts[k] <= 0:
                self.errors.append(f"count '{k}' is zero: that claim was never exercised")
        ok = not self.errors and not self.mon_errors
        for e in self.errors[:20]:
            self.log.error(e)
        self.log.info(f"CHI-MONLITE-VERDICT {tag} {'PASS' if ok else 'FAIL'} "
                      + ' '.join(f"{k}={v}" for k, v in sorted(self.counts.items())))
        return ok
