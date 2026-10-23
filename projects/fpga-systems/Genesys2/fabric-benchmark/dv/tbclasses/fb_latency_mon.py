# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Exact per-transaction latency on STREAM's port, for the harness sim.

The board's latency figure is the master-side observer's log2 histogram
(bin/fb_latency.py), which resolves 2x, not a few cycles. In sim the same
port is watched by framework GAXIMonitors -- AR, R, AW and B on fb_harness's
stream_rd_* / stream_wr_* nets, the signals u_dma_observer snoops -- and each
completion is matched to the oldest outstanding command of its ID (AXI keeps
same-ID responses in order, the rule the hardware histogram matches by too).

Latencies are in aclk cycles, handshake to handshake:
    rd_first  AR -> first R beat      rd_last  AR -> RLAST      wr_b  AW -> B

Call drain() after a run: it consumes everything observed since the last
drain and returns the summary. A command still unanswered at drain time is
counted as 'open' and carried into the next drain, never dropped.
"""
from __future__ import annotations

import statistics
from collections import defaultdict, deque

from CocoTBFramework.components.axi4.axi4_field_configs import AXI4FieldConfigHelper
from CocoTBFramework.components.gaxi.gaxi_monitor import GAXIMonitor

ID_WIDTH, ADDR_WIDTH, DATA_WIDTH = 8, 32, 128


class FbLatencyMonitor:
    def __init__(self, dut, clock, period_ns: float, log):
        self.period_ns = period_ns
        cfg = AXI4FieldConfigHelper
        spec = {
            'ar': ('stream_rd_', 'axi4_ar_slave', cfg.create_ar_field_config(ID_WIDTH, ADDR_WIDTH, 1)),
            'r':  ('stream_rd_', 'axi4_r_slave',  cfg.create_r_field_config(ID_WIDTH, DATA_WIDTH, 1)),
            'aw': ('stream_wr_', 'axi4_aw_slave', cfg.create_aw_field_config(ID_WIDTH, ADDR_WIDTH, 1)),
            'b':  ('stream_wr_', 'axi4_b_slave',  cfg.create_b_field_config(ID_WIDTH, 1)),
        }
        self.mon = {}
        for ch, (prefix, ptype, fc) in spec.items():
            m = GAXIMonitor(dut, f"lat_{ch}", prefix, clock, fc, is_slave=True, mode='skid',
                            pkt_prefix=ch, multi_sig=True, protocol_type=ptype, log=log,
                            optional_fields=('lock', 'cache', 'prot', 'qos', 'region', 'user'))
            m.enable_completed_packet_tracking()
            self.mon[ch] = m
        self._rd_open = defaultdict(deque)     # id -> [ar_time, first_r_time or None]
        self._wr_open = defaultdict(deque)     # id -> aw_time

    def _cycles(self, t0: float, t1: float) -> int:
        return round((t1 - t0) / self.period_ns)

    def drain(self) -> dict:
        lat = {'rd_first': [], 'rd_last': [], 'wr_b': []}
        unmatched = 0
        # Commands and completions on one side are merged in time order, a
        # command ahead of a same-cycle completion; a completion always takes
        # the oldest open command of its ID.
        rd = [(p.start_time, 0, p) for p in self.mon['ar'].get_completed_packets()] + \
             [(p.start_time, 1, p) for p in self.mon['r'].get_completed_packets()]
        for t, kind, p in sorted(rd, key=lambda e: (e[0], e[1])):
            q = self._rd_open[int(p.id)]
            if kind == 0:
                q.append([t, None])
                continue
            if not q:
                unmatched += 1
                continue
            if q[0][1] is None:
                q[0][1] = t
                lat['rd_first'].append(self._cycles(q[0][0], t))
            if int(p.last):
                t0, _ = q.popleft()
                lat['rd_last'].append(self._cycles(t0, t))
        wr = [(p.start_time, 0, p) for p in self.mon['aw'].get_completed_packets()] + \
             [(p.start_time, 1, p) for p in self.mon['b'].get_completed_packets()]
        for t, kind, p in sorted(wr, key=lambda e: (e[0], e[1])):
            q = self._wr_open[int(p.id)]
            if kind == 0:
                q.append(t)
            elif q:
                lat['wr_b'].append(self._cycles(q.popleft(), t))
            else:
                unmatched += 1
        out = {'unmatched': unmatched,
               'open': sum(map(len, self._rd_open.values())) + sum(map(len, self._wr_open.values()))}
        for k, v in lat.items():
            out[k] = summarize(v)
        return out


def summarize(v: list) -> dict:
    if not v:
        return {'n': 0}
    s = sorted(v)
    pct = lambda q: s[min(len(s) - 1, int(q * len(s)))]
    return {'n': len(s), 'min': s[0], 'p50': pct(0.5), 'p90': pct(0.9), 'p99': pct(0.99),
            'max': s[-1], 'mean': round(statistics.fmean(s), 2)}
