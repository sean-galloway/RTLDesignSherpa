#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# HAND-WRITTEN (not generated): bandwidth characterization of generated
# bridges. Requesters are pipelined (RDS-DV `pipelined=True`), so a gap at a
# port belongs to the fabric. Every figure is logged as a PERF line, measured
# inside its own cycle window at the port named, and every transfer's data is
# checked. Every figure also has a FLOOR (see KNOWN / RTT_BUDGET below):
# a case fails if any measurement falls under the floor its shape allows,
# so this suite gates bandwidth in the func regression.
#
#   bursts       read / write streams, 1..256 beats, one ID vs eight IDs
#   outstanding  slave latency 0/16/64 against 1..32 transactions in flight
#   duplex       read+write on one master; crossing paths; all four streams
#   contention   two masters into one slave under outstanding limits
#   fairness     the same against a slave that takes only K requests at a time
#   ooo          an out-of-order slave answering eight IDs
#   backpressure slave READY at 50%, master READY at 50%
#   width        every width-converted path, 1..256 beats (4x4 only)
#   split        8:1 downsize writes long enough to split, 1..8 in flight
#   wr_order     both masters write both slaves, each slave one write at a time

import os
import sys

import pytest

from TBClasses.shared.utilities import get_repo_root, sim_build_path

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb                                                       # noqa: E402
from cocotb_test.simulator import run                               # noqa: E402
from TBClasses.shared.utilities import get_paths, get_wave_config   # noqa: E402
from TBClasses.shared.filelist_utils import get_sources_from_filelist  # noqa: E402
from TBClasses.shared.test_levels import level_env, reg_level_grid  # noqa: E402

from bridge2x2_rw_tb import Bridge2x2RwTB                           # noqa: E402
from bridge2x2_rw_lat_tb import Bridge2x2RwLatTB                    # noqa: E402
from bridge2x2_rw_pipe_tb import Bridge2x2RwPipeTB                  # noqa: E402
from bridge2x2_rw_qos_tb import Bridge2x2RwQosTB                    # noqa: E402
from bridge4x4_rw_tb import Bridge4x4RwTB                           # noqa: E402
from bridge_perf_char import (AcceptLimit, Characterizer, Floors,  # noqa: E402
                              Stream, pipeline, throttle_ready)
from bridge_perf_probe import report                                # noqa: E402

FIXTURES = {'bridge_2x2_rw': Bridge2x2RwTB, 'bridge_2x2_rw_lat': Bridge2x2RwLatTB,
            'bridge_2x2_rw_pipe': Bridge2x2RwPipeTB, 'bridge_2x2_rw_qos': Bridge2x2RwQosTB,
            'bridge_4x4_rw': Bridge4x4RwTB}
DUTS = list(FIXTURES)
# Port roles per fixture: (cpu, dma) master indices, (ddr, sram) slave
# indices. cpu->ddr is width-matched everywhere; on 4x4_rw cpu (64b) ->
# ddr0 (64b) is matched and dma0 (32b) -> sram (128b) is a 4:1 upsize.
ROLES = {'bridge_4x4_rw': (0, 1, 1, 2)}
CPU, DMA, DDR, SRAM = ROLES.get(os.environ.get('BRIDGE_PERF_DUT', 'bridge_2x2_rw'), (0, 1, 0, 1))
SCALE = {'gate': 1, 'func': 2, 'full': 4}

DUT_NAME = os.environ.get('BRIDGE_PERF_DUT', 'bridge_2x2_rw')

# ---------------------------------------------------------------------------
# Floors. FULL is a saturated link: one beat per cycle, less measurement
# edge. Where the shape cannot saturate, the floor is the shape's own limit:
# Little's law for a bounded number in flight -- n bursts of B beats, each
# occupying B transfer cycles + the slave's latency + the bridge's own round
# trip -- and 1/(1+p) for a READY held off one cycle with probability p.
# ---------------------------------------------------------------------------
FULL = 0.97
# Round trip the bridge itself may add per burst, cycles, beyond the burst's
# own beats and the slave's latency. Measured: ~6 on the 2x2s, ~9 on pipe
# (extra register stages) and on 4x4 (a wider crossbar); each budget is that
# plus margin, so a latency regression of a few cycles fails here.
RTT_BUDGET = {'bridge_2x2_rw': 8, 'bridge_2x2_rw_lat': 8, 'bridge_2x2_rw_pipe': 10,
              'bridge_2x2_rw_qos': 8, 'bridge_4x4_rw': 10}
# Open weaknesses: (label regex, floor, note). A fixed weakness's row is
# deleted, and the shape's real floor applies again.
KNOWN = {
    'bridge_2x2_rw_pipe': [
        (r'^bursts wr beats=1 ', 0.78, 'W4 single-beat writes on the pipelined fabric (0.805)'),
    ],
    'bridge_4x4_rw': [
        (r'^width up .* beats=1$', 0.71, 'W5 single-beat upsize, reads and writes (0.734)'),
        # cpu (64b) and dma0 (32b) share ddr0 (64b): a 32-bit master's grant
        # holds the 64-bit channel at half rate for its beats.
        (r'^(contention|fairness) wr .* (contended|slave)$', 0.78,
         'W2 narrow master throttles the shared wide slave (wr 0.80)'),
        (r'^(contention|fairness) rd .* (contended|slave)$', 0.90,
         'W2 narrow master throttles the shared wide slave (rd 0.93)'),
        # Writes are fair here (0.50); reads of the 32-bit dma0 through its
        # 32->64 upsize read converter get 0.34 at 2 in flight (0.29 before
        # arbitration moved to the pins), so the shortfall is in the
        # width-converted read path, not the arbiter.
        (r'^fairness rd .* round_robin$', 0.32,
         'W2 narrow master upsize read path (0.337; writes 0.50)'),
    ],
}
NO_STARVE = 0.05   # a contending master gets at least this share
FAIR_HALF = 0.45   # round-robin share of two masters that can both fill the slave


def little(n_bursts: int, beats: int, lat: int) -> float:
    return FULL * min(1.0, n_bursts * beats / (beats + lat + RTT_BUDGET[DUT_NAME]))


def floors(tb) -> Floors:
    return Floors(tb, KNOWN.get(DUT_NAME, []))


def _tb(dut):
    return FIXTURES[os.environ.get('BRIDGE_PERF_DUT', 'bridge_2x2_rw')](dut)


def _win_rate(s, name, lo, hi):
    """Beats per cycle between the first and last handshake inside [lo, hi]."""
    pts = [c for c in s.marks[name] if lo <= c <= hi]
    if len(pts) < 2:
        return len(pts), 0.0
    return len(pts), len(pts) / (pts[-1] - pts[0] + 1)


async def _measure(ch, s, streams, ports):
    lo = s.cycle + 1
    await ch.run(streams)
    hi = s.cycle
    return {p: _win_rate(s, p, lo, hi) for p in ports}


async def _setup(dut):
    tb = _tb(dut)
    await tb.setup_clocks_and_reset()
    pipeline(tb)
    ch = Characterizer(tb)
    return tb, ch


@cocotb.test(timeout_time=200, timeout_unit="sec")
async def cocotb_test_perf_char_bursts(dut):
    tb, ch = await _setup(dut)
    s = ch.sampler({'m_aw': ('m', CPU, 'aw'), 'm_w': ('m', CPU, 'w'), 's_w': ('s', DDR, 'w'),
                    'm_ar': ('m', CPU, 'ar'), 'm_r': ('m', CPU, 'r'), 's_r': ('s', DDR, 'r')})
    k = SCALE[tb.level]
    fl = floors(tb)
    for kind in ('wr', 'rd'):
        for beats in (1, 2, 4, 8, 16, 64, 256):
            for ids in ((0,), tuple(range(8))):
                n = max(16, (256 * k) // beats)
                st = Stream(kind, CPU, DDR, n, beats, outstanding=8, ids=ids)
                d = 'w' if kind == 'wr' else 'r'
                a = 'aw' if kind == 'wr' else 'ar'
                r = await _measure(ch, s, [st], [f's_{d}', f'm_{d}', f'm_{a}'])
                label = f"bursts {kind} beats={beats} ids={len(ids)}"
                report(tb, label, slave_rate=r[f's_{d}'][1], master_rate=r[f'm_{d}'][1],
                       addr_per_cycle=r[f'm_{a}'][1], beats_total=r[f's_{d}'][0])
                fl.need(label, r[f's_{d}'][1], FULL)
    fl.check()


@cocotb.test(timeout_time=300, timeout_unit="sec")
async def cocotb_test_perf_char_outstanding(dut):
    tb, ch = await _setup(dut)
    s = ch.sampler({'s_w': ('s', DDR, 'w'), 's_r': ('s', DDR, 'r'),
                    'm_b': ('m', CPU, 'b'), 'm_r': ('m', CPU, 'r')})
    fl = floors(tb)
    for lat in (0, 16, 64):
        tb.slave_rd[DDR].response_delay_cycles = lat
        tb.slave_wr[DDR].response_delay_cycles = lat
        for kind in ('rd', 'wr'):
            for n_out in (1, 2, 4, 8, 16, 32):
                st = Stream(kind, CPU, DDR, 48, 8, outstanding=n_out, ids=tuple(range(16)))
                port = 's_r' if kind == 'rd' else 's_w'
                r = await _measure(ch, s, [st], [port])
                label = f"outstanding {kind} lat={lat} n={n_out}"
                report(tb, label, slave_rate=r[port][1])
                fl.need(label, r[port][1], little(n_out, 8, lat))
    tb.slave_rd[DDR].response_delay_cycles = 0
    tb.slave_wr[DDR].response_delay_cycles = 0
    fl.check()


@cocotb.test(timeout_time=300, timeout_unit="sec")
async def cocotb_test_perf_char_duplex(dut):
    tb, ch = await _setup(dut)
    s = ch.sampler({'ddr_w': ('s', DDR, 'w'), 'ddr_r': ('s', DDR, 'r'),
                    'sram_w': ('s', SRAM, 'w'), 'sram_r': ('s', SRAM, 'r'),
                    'cpu_w': ('m', CPU, 'w'), 'cpu_r': ('m', CPU, 'r'),
                    'dma_w': ('m', DMA, 'w'), 'dma_r': ('m', DMA, 'r')})
    k = SCALE[tb.level]
    n, b, ids = 32 * k, 16, tuple(range(8))
    cases = {
        'cpu rd+wr same slave': [Stream('rd', CPU, DDR, n, b, ids=ids, region=0),
                                 Stream('wr', CPU, DDR, n, b, ids=ids, region=1)],
        'cpu rd+wr two slaves': [Stream('rd', CPU, DDR, n, b, ids=ids),
                                 Stream('wr', CPU, SRAM, n, b, ids=ids)],
        'crossing writes': [Stream('wr', CPU, DDR, n, b, ids=ids),
                            Stream('wr', DMA, SRAM, n, b, ids=ids)],
        'crossing reads': [Stream('rd', CPU, SRAM, n, b, ids=ids),
                           Stream('rd', DMA, DDR, n, b, ids=ids)],
        'all four': [Stream('rd', CPU, DDR, n, b, ids=ids, region=0),
                     Stream('wr', CPU, SRAM, n, b, ids=ids, region=0),
                     Stream('rd', DMA, SRAM, n, b, ids=ids, region=1),
                     Stream('wr', DMA, DDR, n, b, ids=ids, region=1)],
    }
    ports = list(s.marks)
    fl = floors(tb)
    for label, streams in cases.items():
        r = await _measure(ch, s, streams, ports)
        report(tb, f"duplex {label}", **{p: v[1] for p, v in r.items() if v[0]})
        # Every requester saturates its own port: no path here shares a channel.
        for p, v in r.items():
            if v[0] and p.split('_')[0] in ('cpu', 'dma'):
                fl.need(f"duplex {label} {p}", v[1], FULL)
    fl.check()


@cocotb.test(timeout_time=300, timeout_unit="sec")
async def cocotb_test_perf_char_contention(dut):
    tb, ch = await _setup(dut)
    s = ch.sampler({'ddr_w': ('s', DDR, 'w'), 'ddr_r': ('s', DDR, 'r'),
                    'cpu_w': ('m', CPU, 'w'), 'dma_w': ('m', DMA, 'w'),
                    'cpu_r': ('m', CPU, 'r'), 'dma_r': ('m', DMA, 'r')})
    fl = floors(tb)
    for lat in (0, 32):
        tb.slave_rd[DDR].response_delay_cycles = lat
        tb.slave_wr[DDR].response_delay_cycles = lat
        for kind in ('wr', 'rd'):
            d = 'w' if kind == 'wr' else 'r'
            for cpu_out, dma_out in ((8, 8), (8, 4), (8, 2), (8, 1), (2, 2)):
                streams = [Stream(kind, CPU, DDR, 64, 8, outstanding=cpu_out, ids=tuple(range(8)), region=0),
                           Stream(kind, DMA, DDR, 64, 8, outstanding=dma_out, ids=tuple(range(8)), region=1)]
                lo = s.cycle + 1
                await ch.run(streams)
                hi = s.cycle
                cpu_pts = [c for c in s.marks[f'cpu_{d}'] if lo <= c <= hi]
                dma_pts = [c for c in s.marks[f'dma_{d}'] if lo <= c <= hi]
                w_lo, w_hi = max(cpu_pts[0], dma_pts[0]), min(cpu_pts[-1], dma_pts[-1])
                c_n = sum(1 for c in cpu_pts if w_lo <= c <= w_hi)
                d_n = sum(1 for c in dma_pts if w_lo <= c <= w_hi)
                tot = _win_rate(s, f'ddr_{d}', lo, hi)[1]
                label = f"contention {kind} lat={lat} out={cpu_out}/{dma_out}"
                contended = (c_n + d_n) / max(1, w_hi - w_lo + 1)
                report(tb, label, slave_rate=tot, contended_rate=contended,
                       dma_share=d_n / max(1, c_n + d_n))
                # While both run, the shared slave stays as busy as the two
                # masters' combined outstanding allows.
                fl.need(f"{label} contended", contended, little(cpu_out + dma_out, 8, lat))
                fl.need(f"{label} dma_share", d_n / max(1, c_n + d_n), NO_STARVE)
    tb.slave_rd[DDR].response_delay_cycles = 0
    tb.slave_wr[DDR].response_delay_cycles = 0
    fl.check()


@cocotb.test(timeout_time=200, timeout_unit="sec")
async def cocotb_test_perf_char_ooo(dut):
    tb, ch = await _setup(dut)
    s = ch.sampler({'s_r': ('s', DDR, 'r'), 'm_r': ('m', CPU, 'r')})
    sl = tb.slave_rd[DDR]
    fl = floors(tb)
    for prob, mx in ((0.0, 0), (0.3, 16), (0.7, 32)):
        sl.enable_ooo = prob > 0
        sl.ooo_config = {'mode': 'random', 'reorder_probability': prob,
                         'min_delay_cycles': 1, 'max_delay_cycles': max(1, mx)}
        st = Stream('rd', CPU, DDR, 96, 8, outstanding=16, ids=tuple(range(8)))
        r = await _measure(ch, s, [st], ['s_r', 'm_r'])
        label = f"ooo reorder={prob} maxdelay={mx}"
        report(tb, label, slave_rate=r['s_r'][1], master_rate=r['m_r'][1])
        # The reordering slave model inserts its own response delays, so the
        # master is held to the slave's rate: the bridge must pass reordered
        # beats through without losing any of it.
        fl.need(label, r['m_r'][1], FULL * r['s_r'][1])
        fl.need(f"{label} slave", r['s_r'][1], FULL if prob == 0 else 0.85)
    sl.enable_ooo = False
    fl.check()


@cocotb.test(timeout_time=200, timeout_unit="sec")
async def cocotb_test_perf_char_backpressure(dut):
    tb, ch = await _setup(dut)
    s = ch.sampler({'s_w': ('s', DDR, 'w'), 's_r': ('s', DDR, 'r'),
                    'm_w': ('m', CPU, 'w'), 'm_r': ('m', CPU, 'r')})
    fl = floors(tb)
    for side, duty in (('slave', 0.5), ('master', 0.5), ('slave', 0.25)):
        if side == 'slave':
            throttle_ready(tb.slave_wr[DDR].w_channel, duty)
        else:
            throttle_ready(tb.master_rd[CPU].r_channel, duty)
        for kind in ('wr', 'rd'):
            st = Stream(kind, CPU, DDR, 48, 16, outstanding=8, ids=tuple(range(8)))
            d = 'w' if kind == 'wr' else 'r'
            r = await _measure(ch, s, [st], [f's_{d}', f'm_{d}'])
            label = f"backpressure {side} ready={duty} {kind}"
            report(tb, label, slave_rate=r[f's_{d}'][1], master_rate=r[f'm_{d}'][1])
            # The throttled channel (slave W, master R) runs at 1/(1+p) for a
            # one-cycle READY delay with probability p = 1 - duty; the other
            # direction must not notice.
            throttled = (side == 'slave') == (kind == 'wr')
            want = FULL / (2.0 - duty) if throttled else FULL
            fl.need(label, r[f's_{d}'][1], want)
        pipeline(tb)   # back to saturating profiles
    fl.check()


async def _share(ch, s, streams, d):
    """Run two contending streams; (slave rate, dma share, and the two
    masters' combined rate, all over the window where both are active -- once
    one stream finishes the other runs alone, with fewer in flight)."""
    lo = s.cycle + 1
    await ch.run(streams)
    hi = s.cycle
    cpu = [c for c in s.marks[f'cpu_{d}'] if lo <= c <= hi]
    dma = [c for c in s.marks[f'dma_{d}'] if lo <= c <= hi]
    w_lo, w_hi = max(cpu[0], dma[0]), min(cpu[-1], dma[-1])
    c_n = sum(1 for c in cpu if w_lo <= c <= w_hi)
    d_n = sum(1 for c in dma if w_lo <= c <= w_hi)
    return (_win_rate(s, f'ddr_{d}', lo, hi)[1], d_n / max(1, c_n + d_n),
            (c_n + d_n) / max(1, w_hi - w_lo + 1))


@cocotb.test(timeout_time=400, timeout_unit="sec")
async def cocotb_test_perf_char_fairness(dut):
    tb, ch = await _setup(dut)
    s = ch.sampler({'ddr_w': ('s', DDR, 'w'), 'ddr_r': ('s', DDR, 'r'),
                    'cpu_w': ('m', CPU, 'w'), 'dma_w': ('m', DMA, 'w'),
                    'cpu_r': ('m', CPU, 'r'), 'dma_r': ('m', DMA, 'r')})
    fl = floors(tb)
    for limit in (None, 8, 4, 2):
        acc = AcceptLimit(ch, DDR, limit) if limit else None
        for lat in (0, 32):
            tb.slave_rd[DDR].response_delay_cycles = lat
            tb.slave_wr[DDR].response_delay_cycles = lat
            for kind in ('wr', 'rd'):
                d = 'w' if kind == 'wr' else 'r'
                for cpu_out, dma_out in ((8, 8), (8, 2), (8, 1), (16, 2)):
                    streams = [Stream(kind, CPU, DDR, 64, 8, outstanding=cpu_out, ids=tuple(range(8)), region=0),
                               Stream(kind, DMA, DDR, 64, 8, outstanding=dma_out, ids=tuple(range(8)), region=1)]
                    tot, share, contended = await _share(ch, s, streams, d)
                    label = f"fairness {kind} accept={limit or 'inf'} lat={lat} out={cpu_out}/{dma_out}"
                    report(tb, label, slave_rate=tot, contended_rate=contended, dma_share=share,
                           peak_in_flight=(acc.peak_rd if kind == 'rd' else acc.peak_wr) if acc else -1)
                    in_flight = min(limit or 999, cpu_out + dma_out)
                    fl.need(f"{label} contended", contended, little(in_flight, 8, lat))
                    fl.need(f"{label} dma_share", share, NO_STARVE)
                    # Arbitration at the slave's pins: when the slave takes
                    # `limit` at a time and each master can keep that many
                    # in flight, round-robin gives each half (it gave the
                    # shallow master a third while granted requests queued
                    # behind the arbiter -- bridge W3).
                    if limit == 2 and dma_out >= limit:
                        fl.need(f"{label} round_robin", share, FAIR_HALF)
        if acc:
            acc.stop()
    tb.slave_rd[DDR].response_delay_cycles = 0
    tb.slave_wr[DDR].response_delay_cycles = 0
    fl.check()


@cocotb.test(timeout_time=300, timeout_unit="sec")
async def cocotb_test_perf_char_wr_order(dut):
    """Both masters write to both slaves at once while each slave takes one
    write at a time. AXI4 W has no ID: each slave's W follows its AW pick
    order and each master's W its own issue order, so if two slaves picked
    two masters' AWs in opposite orders they would wait on each other's W
    (a crossed-W deadlock). Every write must complete and land.

    Two rules keep each master's picks in its issue order: the master
    adapter's (a new AW to another slave waits until every earlier W burst
    has left the adapter) and the crossbar's write hold (a master's AW waits
    while another of its request slots holds one). Measured 2026-10-17:
    removing the crossbar hold alone does NOT make this case fail on 2x2_rw
    or 4x4_rw -- the adapter rule already covers these paths, so the test
    guards the pair, and the hold is the guarantee at the pick itself for a
    path that buffers W past the adapter's tracker."""
    tb, ch = await _setup(dut)
    s = ch.sampler({'ddr_w': ('s', DDR, 'w'), 'sram_w': ('s', SRAM, 'w')})
    fl = floors(tb)
    accs = [AcceptLimit(ch, DDR, 1), AcceptLimit(ch, SRAM, 1)]
    for beats in (1, 4, 16):
        # Distinct IDs per (master, slave): the master adapter keeps one ID on
        # one slave, which would otherwise serialize the streams it splits.
        streams = [Stream('wr', CPU, DDR, 24, beats, outstanding=4, ids=(0, 1, 2, 3), region=0),
                   Stream('wr', CPU, SRAM, 24, beats, outstanding=4, ids=(4, 5, 6, 7), region=0),
                   Stream('wr', DMA, SRAM, 24, beats, outstanding=4, ids=(0, 1, 2, 3), region=1),
                   Stream('wr', DMA, DDR, 24, beats, outstanding=4, ids=(4, 5, 6, 7), region=1)]
        lo = s.cycle + 1
        await ch.run(streams, timeout_cycles=60_000)   # a deadlock fails here
        hi = s.cycle
        label = f"wr_order beats={beats}"
        rates = {p: _win_rate(s, p, lo, hi)[1] for p in ('ddr_w', 'sram_w')}
        report(tb, label, ddr_rate=rates['ddr_w'], sram_rate=rates['sram_w'])
        # One write in service per slave: it pays its W and B round trip.
        for p, r in rates.items():
            fl.need(f"{label} {p}", r, 0.5 * little(1, beats, 0))
    for a in accs:
        a.stop()
    fl.check()


# Width-converted paths on bridge_4x4_rw: (label, master, slave). Master widths
# cpu 64, dma0 32, dma1 128, gpu 256; slave widths periph 32, ddr0 64, sram 128,
# gpu_mem 256.
WIDTH_PATHS = [('up 2:1 32->64', 1, 1), ('up 2:1 64->128', 0, 2), ('up 4:1 32->128', 1, 2),
               ('up 4:1 64->256', 0, 3), ('down 2:1 64->32', 0, 0), ('down 2:1 128->64', 2, 1),
               ('down 8:1 256->32', 3, 0), ('matched 64', 0, 1)]


@cocotb.test(timeout_time=600, timeout_unit="sec")
async def cocotb_test_perf_char_width(dut):
    tb, ch = await _setup(dut)
    fl = floors(tb)
    for label, m, sl in WIDTH_PATHS:
        mw, sw = tb.master_data_width[m], tb.slave_info[sl][3]
        ideal_m = min(1.0, sw / mw)
        s = ch.sampler({'m_w': ('m', m, 'w'), 'm_r': ('m', m, 'r'),
                        's_w': ('s', sl, 'w'), 's_r': ('s', sl, 'r')})
        for kind in ('wr', 'rd'):
            d = 'w' if kind == 'wr' else 'r'
            for beats in (1, 2, 4, 8, 16, 64, 256):
                st = Stream(kind, m, sl, max(8, 256 // beats), beats, outstanding=8, ids=tuple(range(8)))
                r = await _measure(ch, s, [st], [f'm_{d}', f's_{d}'])
                tag = f"width {label} {kind} beats={beats}"
                report(tb, tag, ideal_master=ideal_m,
                       master_rate=r[f'm_{d}'][1], slave_rate=r[f's_{d}'][1],
                       master_vs_ideal=r[f'm_{d}'][1] / ideal_m)
                fl.need(tag, r[f'm_{d}'][1] / ideal_m, FULL)
    fl.check()


@cocotb.test(timeout_time=600, timeout_unit="sec")
async def cocotb_test_perf_char_split(dut):
    """Write bursts long enough that an 8:1 downsize splits them (256-bit gpu
    master -> 32-bit periph), 1..8 in flight. The slave side should stay
    saturated however deep the master queues."""
    tb, ch = await _setup(dut)
    s = ch.sampler({'m_w': ('m', 3, 'w'), 's_w': ('s', 0, 'w'), 's_aw': ('s', 0, 'aw')})
    fl = floors(tb)
    for beats in (32, 64, 256):
        for out in (1, 2, 4, 8):
            st = Stream('wr', 3, 0, 8, beats, outstanding=out, ids=tuple(range(8)))
            r = await _measure(ch, s, [st], ['m_w', 's_w', 's_aw'])
            label = f"split 8:1 wr beats={beats} out={out}"
            report(tb, label, slave_rate=r['s_w'][1], slave_aw=r['s_aw'][0], master_rate=r['m_w'][1])
            # One in flight pays the round trip once per burst of 8*beats
            # slave beats; two or more hide it.
            fl.need(label, r['s_w'][1], little(out, 8 * beats, 0))
    fl.check()


CASES = ['bursts', 'outstanding', 'duplex', 'contention', 'fairness', 'ooo', 'backpressure', 'width',
         'split', 'wr_order']


def _run(request, test_level, case, dut_name):
    module, repo_root_, tests_dir, log_dir, _ = get_paths({})
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_,
        filelist_path=f'projects/components/fabric-gen-ip/bridge/rtl/filelists/{dut_name}.f')
    worker = os.environ.get('PYTEST_XDIST_WORKER', '')
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    name = f"test_{dut_name}_perf_char_{case}_{test_level}_{reg_level}" + (f"_{worker}" if worker else "")
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    waves = get_wave_config(sim_build)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase=f"cocotb_test_perf_char_{case}",
        sim_build=sim_build, waves=False,
        extra_args=['--assert'] + waves['extra_args'],
        extra_env={'COCOTB_LOG_LEVEL': 'INFO', 'LOG_PATH': log_path,
                   'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{name}.xml'),
                   'BRIDGE_PERF_DUT': dut_name, **level_env(test_level), **waves['extra_env']},
        plus_args=waves['sim_args'], keep_files=True)


# Which cases run on which fixture. width and split need the 4x4's mixed
# widths; lat (no AR/AW skid) and qos exist for the arbitration cases; ooo
# and backpressure exercise paths every fixture shares, so 2x2_rw covers them.
MATRIX = {
    'bridge_2x2_rw':      ['bursts', 'outstanding', 'duplex', 'contention', 'fairness', 'ooo', 'backpressure',
                           'wr_order'],
    'bridge_2x2_rw_lat':  ['bursts', 'outstanding', 'contention', 'fairness'],
    'bridge_2x2_rw_pipe': ['bursts', 'outstanding', 'duplex', 'contention', 'wr_order'],
    'bridge_2x2_rw_qos':  ['bursts', 'contention', 'fairness'],
    'bridge_4x4_rw':      ['bursts', 'outstanding', 'duplex', 'contention', 'fairness', 'width', 'split',
                           'wr_order'],
}
assert set(DUTS) == set(MATRIX) and all(c in CASES for cs in MATRIX.values() for c in cs)


@pytest.mark.parametrize("dut_name, case", [(d, c) for d, cs in MATRIX.items() for c in cs])
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_perf_char(request, test_level, case, dut_name):
    _run(request, test_level, case, dut_name)
