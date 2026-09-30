# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Byte-granular RAPIDS performance campaign (rapids TASK-019 characterization).

Pure logic over RapidsByteCampaign: point profiles, one-point runner, metric
derivation and the incremental results file. No hardware access of its own, so
the same code runs on the board (run_characterization.py --byte-perf) and in
the cocotb harness (dv/test_rapids_byte_harness.py).

Per point and per direction the record carries the measured bytes, the measured
beats on the AXIS and memory interfaces, the payload efficiency
(bytes / (beats x BYTE_LANES)) on both, MB/s over the direction's meter window
against the peak, and the engaged utilization of every interface.
"""

import hashlib
import json
import os
import time
from datetime import datetime

from rapids_byte_golden import source_mem_beats

SCHEMA = 'rapids_byte_perf/1'

SIZES = (1, 7, 32, 33, 64, 77, 203, 1024, 4035, 4096)
OFFSETS_ALL = (0, 1, 5, 31)
CHANNELS = (1, 2, 4, 8)
ALIGNED_BEATS = (1, 4, 16, 64, 256, 1024, 4096)
BEAT_COMPARE_CHANNELS = (1, 2, 4, 8)


def _pt(group, ch, *, payload=None, beats=None, offset=0, descs=1,
        bp=False, directions=('sink', 'source')):
    if payload is not None:
        pid = f"{group}_ch{ch}_p{payload}_o{offset}_d{descs}"
    else:
        pid = f"{group}_ch{ch}_b{beats}"
    if bp:
        pid += '_bp'
    return {'id': pid, 'group': group, 'channels': ch, 'payload': payload,
            'beats': beats, 'offset': offset, 'descs': descs,
            'backpressure': bp, 'directions': list(directions)}


def build_points(profile: str):
    """Ordered point list for a profile: quick | standard | full."""
    pts = []
    if profile == 'quick':
        for ch in (2,):
            for p, o in ((77, 5), (33, 0), (4096, 0)):
                pts.append(_pt('size', ch, payload=p, offset=o))
        for b in (4, 64):
            pts.append(_pt('beat', 2, beats=b))
        pts.append(_pt('bp', 2, payload=33, offset=0, bp=True, directions=('source',)))
        return pts
    offs = (0,) if profile == 'standard' else OFFSETS_ALL
    for ch in CHANNELS:
        for p in SIZES:
            for o in offs:
                pts.append(_pt('size', ch, payload=p, offset=o))
    if profile == 'standard':
        for ch in (1, 8):
            for p in (33, 203, 1024, 4035):
                for o in (1, 5, 31):
                    pts.append(_pt('offset', ch, payload=p, offset=o))
    for ch in BEAT_COMPARE_CHANNELS:
        for b in ALIGNED_BEATS:
            pts.append(_pt('beat', ch, beats=b))
    for p, d in ((1, 16), (64, 4), (64, 16), (1024, 4), (1024, 16)):
        pts.append(_pt('chain', 4, payload=p, descs=d))
    for ch in (1, 4):
        for p in (33, 1024):
            for o in (0, 5):
                pts.append(_pt('bp', ch, payload=p, offset=o, bp=True,
                               directions=('source',)))
    return pts


PROFILES = ('quick', 'standard', 'full')


def _expected(pt, bpb):
    d, n = pt['descs'], pt['channels']
    if pt['payload'] is not None:
        pl, off = pt['payload'], pt['offset']
        axis_beats = -(-pl // bpb)
        mem_beats = source_mem_beats(off, pl, bpb)
    else:
        pl, axis_beats, mem_beats = pt['beats'] * bpb, pt['beats'], pt['beats']
    return {'payload_per_pkt': pl, 'bytes': pl * d * n, 'packets': d * n,
            'axis_beats': axis_beats * d * n, 'mem_beats': mem_beats * d * n}


def _iface(ifs, key):
    m = (ifs.get(key) or {}).get('buckets')
    if not m:
        return None
    return {'util': m['util'], 'prod': m['prod'], 'bp': m['bp'],
            'starv': m['starv'], 'idle': m['idle'], 'window': m['total']}


def derive(ok, detail, pt, direction, bpb, aclk_hz):
    """Reduce one _score() detail to the numbers the report tabulates."""
    perf = (detail or {}).get('perf') or {}
    ifs = perf.get('ifaces') or {}
    axis_key, mem_key = ('sin', 'wr') if direction == 'sink' else ('sout', 'rd')
    exp = _expected(pt, bpb)
    peak = bpb * aclk_hz / 1e6
    axis, mem = _iface(ifs, axis_key), _iface(ifs, mem_key)
    axis_rec = ifs.get(axis_key) or {}
    nbytes = axis_rec.get('bytes')
    rec = {
        'pass': bool(ok),
        'perf_valid': bool(ok) and not (direction == 'source' and pt['backpressure']),
        'errors': list((detail or {}).get('errors') or [])[:4],
        'golden_mismatch': bool((detail or {}).get('golden_mismatch')),
        'expected': exp,
        'ifaces': {axis_key: axis, mem_key: mem},
        'axis_key': axis_key, 'mem_key': mem_key,
        'bytes': nbytes, 'packets': axis_rec.get('packets'),
        'axis_beats': axis['prod'] if axis else None,
        'mem_beats': mem['prod'] if mem else None,
        'peak_mb_s': peak,
    }
    rec['counts_match'] = (nbytes == exp['bytes'] and rec['axis_beats'] == exp['axis_beats']
                           and rec['mem_beats'] == exp['mem_beats']
                           and rec['packets'] == exp['packets'])
    windows = [x['window'] for x in (axis, mem) if x]
    span = max(windows) if windows else 0
    rec['window'] = span or None
    if nbytes is not None and rec['axis_beats']:
        rec['eff_axis'] = nbytes / (rec['axis_beats'] * bpb)
    if nbytes is not None and rec['mem_beats']:
        rec['eff_mem'] = nbytes / (rec['mem_beats'] * bpb)
    if nbytes is not None and span:
        rec['mb_s'] = nbytes * aclk_hz / span / 1e6
        rec['pct_peak'] = rec['mb_s'] / peak
    lat = {}
    obs = (perf.get('observers') or {}).get(mem_key) or {}
    for name, ld in (obs.get('latency') or {}).items():
        if ld.get('samples'):
            lat[name] = {k: ld[k] for k in ('samples', 'mean_cyc', 'p50_cyc', 'p90_cyc', 'p99_cyc')}
    if lat:
        rec['latency'] = lat
    return rec


def run_point(campaign, pt, timeout_s):
    """Run one point (sink and/or source); returns the row dict."""
    design = campaign.ensure_build()
    bpb, aclk = design['beat_bytes'], design['aclk_hz']
    active = list(range(pt['channels']))
    if pt['payload'] is not None:
        kw = {'pkt_bytes': pt['payload'], 'offset': pt['offset'], 'descs': pt['descs']}
        beats = 0
    else:
        kw, beats = {'descs': pt['descs']}, pt['beats']
    row = {k: pt[k] for k in ('id', 'group', 'channels', 'payload', 'beats',
                              'offset', 'descs', 'backpressure')}
    row['bytes_per_beat'] = bpb
    row['xfer_beats'] = campaign.xfer_axlen + 1
    t0 = time.time()
    for direction in pt['directions']:
        try:
            if direction == 'sink':
                ok, det = campaign.run_sink_selfcheck(active, beats, timeout_s, **kw)
            else:
                ok, det = campaign.run_source_selfcheck(
                    active, beats, timeout_s, backpressure=pt['backpressure'], **kw)
            row[direction] = derive(ok, det, pt, direction, bpb, aclk)
        except Exception as exc:  # noqa: BLE001 - a dead point must not end the campaign
            row[direction] = {'pass': False, 'perf_valid': False,
                              'errors': [f"exception: {exc}"], 'exception': True}
    row['pass'] = all(row[d]['pass'] for d in pt['directions'])
    row['seconds'] = round(time.time() - t0, 2)
    return row


def file_sha256(path):
    if not path or not os.path.isfile(path):
        return None
    h = hashlib.sha256()
    with open(path, 'rb') as fh:
        for blk in iter(lambda: fh.read(1 << 20), b''):
            h.update(blk)
    return h.hexdigest()


def _write_atomic(path, doc):
    os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
    tmp = path + '.tmp'
    with open(tmp, 'w') as fh:
        json.dump(doc, fh, indent=1)
    os.replace(tmp, path)


def _short(row):
    parts = []
    for d in ('sink', 'source'):
        r = row.get(d)
        if not r:
            continue
        if r.get('mb_s') is not None:
            parts.append(f"{d} {'ok' if r['pass'] else 'FAIL'} {r['mb_s']:.0f} MB/s eff {r.get('eff_axis', 0):.2f}")
        else:
            parts.append(f"{d} {'ok' if r['pass'] else 'FAIL'}")
    return ' | '.join(parts)


CSR_ID_EXPECTED = 0x5241_5042  # "RAPB", the harness magic (CTRL read alias)
SENTINEL_REG = "MON_LIMIT"  # written once by configure(), resets to 0 on any FPGA reconfiguration


def device_readback(campaign):
    """What is actually on the device right now: CSR_ID (CTRL read alias), BUILD,
    and a configure-time sentinel that only survives while nobody reprograms the
    FPGA. A reprogram to the SAME bitstream changes the sentinel, not the ID."""
    io = campaign.io
    return {'csr_id': io.csr_read_reg("CTRL"), 'build': io.csr_read_reg("BUILD"),
            'sentinel': io.csr_read_reg(SENTINEL_REG),
            'time': datetime.now().isoformat(timespec='seconds')}


def _device_changed(start, now):
    return [k for k in ('csr_id', 'build', 'sentinel') if start.get(k) != now.get(k)]


def run_campaign(campaign, profile, results_path, *, timeout_s=30.0, prelim=False,
                 resume=False, max_minutes=None, bitstream=None, points=None,
                 stop_after_dead=3, out=print):
    """Run a profile, rewriting the results file after every point.

    Returns (doc, all_pass). `resume` skips point ids already in the file.
    `max_minutes` stops cleanly between points and marks the file incomplete.
    A failed point is recorded and later points carry `after_failure`, because
    the sticky sink flags clear only on aresetn (the channel-reset gap).
    """
    design = campaign.ensure_build()
    pts = points if points is not None else build_points(profile)
    doc = None
    if resume and os.path.isfile(results_path):
        with open(results_path) as fh:
            doc = json.load(fh)
    if doc is None:
        doc = {'schema': SCHEMA, 'timestamp': datetime.now().isoformat(timespec='seconds'),
               'prelim': bool(prelim), 'profile': profile, 'design': dict(design),
               'aclk_hz': design['aclk_hz'],
               'peak_mb_s': design['beat_bytes'] * design['aclk_hz'] / 1e6,
               'bitstream': {'path': os.path.basename(bitstream) if bitstream else None,
                             'sha256': file_sha256(bitstream)},
               'points': []}
    done = {r['id'] for r in doc['points']}
    todo = [p for p in pts if p['id'] not in done]
    doc['planned'] = len(pts)
    doc['complete'] = False
    doc.pop('aborted', None)
    first_fail = next((r['id'] for r in doc['points'] if not r['pass']), None)
    sess = {'bitstream_sha256': (doc.get('bitstream') or {}).get('sha256') if bitstream is None
            else file_sha256(bitstream), 'points_before': len(doc['points'])}
    try:
        sess['start'] = device_readback(campaign)
    except Exception as exc:  # noqa: BLE001
        sess['start'] = {'error': str(exc)}
    doc.setdefault('sessions', []).append(sess)
    if sess['start'].get('csr_id') != CSR_ID_EXPECTED:
        doc['aborted'] = f"device readback at start is not the rapids harness: {sess['start']}"
        out(f"byte-perf: {doc['aborted']}")
        sess['stable'], sess['aborted'] = False, True
        _write_atomic(results_path, doc)
        return doc, False
    start, dead = time.time(), 0
    out(f"byte-perf: profile={profile} planned={len(pts)} todo={len(todo)} -> {results_path}")
    for i, pt in enumerate(todo, 1):
        if max_minutes is not None and (time.time() - start) / 60.0 >= max_minutes:
            out(f"byte-perf: --max-minutes {max_minutes} reached with {len(todo) - i + 1} points left")
            break
        row = run_point(campaign, pt, timeout_s)
        try:
            now = device_readback(campaign)
            changed = _device_changed(sess['start'], now)
        except Exception as exc:  # noqa: BLE001
            now, changed = None, [f"readback failed: {exc}"]
        if changed:
            doc['aborted'] = (f"device changed at {pt['id']} ({', '.join(changed)}): the board was "
                              "reprogrammed or lost while this point ran (another user?); point not recorded")
            out(f"byte-perf: {doc['aborted']}")
            sess['stable'], sess['aborted'] = False, True
            sess['end'] = now
            break
        if first_fail:
            row['after_failure'] = first_fail
        elif not row['pass']:
            first_fail = row['id']
        doc['points'].append(row)
        doc['passed'] = sum(1 for r in doc['points'] if r['pass'])
        doc['failed'] = len(doc['points']) - doc['passed']
        _write_atomic(results_path, doc)
        el = time.time() - start
        eta = el / i * (len(todo) - i)
        out(f"[{i}/{len(todo)}] {pt['id']}: {'PASS' if row['pass'] else 'FAIL'} "
            f"{_short(row)} ({row['seconds']}s, elapsed {el/60:.1f}m, eta {eta/60:.1f}m)")
        dead = dead + 1 if any(row.get(d, {}).get('exception') for d in pt['directions']) else 0
        if dead >= stop_after_dead:
            out(f"byte-perf: {dead} consecutive exceptions -- link is dead, stopping")
            break
    if 'end' not in sess:
        try:
            sess['end'] = device_readback(campaign)
            sess['stable'] = not _device_changed(sess['start'], sess['end'])
        except Exception as exc:  # noqa: BLE001
            sess['end'] = {'error': str(exc)}
            sess['stable'] = False
        if not sess['stable']:
            doc['aborted'] = f"device readback at end differs from the start: {sess['start']} -> {sess['end']}"
            out(f"byte-perf: {doc['aborted']}")
    shas = {x.get('bitstream_sha256') for x in doc['sessions']}
    # An aborted session dropped its last point; every recorded point passed the sentinel check.
    doc['device_stable'] = all(x.get('stable') or x.get('aborted') for x in doc['sessions']) and len(shas) == 1
    doc['complete'] = all(p['id'] in {r['id'] for r in doc['points']} for p in pts)
    doc['passed'] = sum(1 for r in doc['points'] if r['pass'])
    doc['failed'] = len(doc['points']) - doc['passed']
    _write_atomic(results_path, doc)
    out(f"byte-perf: {doc['passed']} passed, {doc['failed']} failed, "
        f"{len(doc['points'])}/{len(pts)} points, complete={doc['complete']}")
    return doc, doc['failed'] == 0 and doc['complete'] and doc['device_stable']


def compare_beats(doc, beats_json_path):
    """Beat-aligned rows against the RAPIDS Beats matrix (bare meters, bp off,
    9-beat bursts, delay 0, default seed). Returns one dict per cell/interface."""
    with open(beats_json_path) as fh:
        ref = json.load(fh)
    idx = {}
    for c in ref['configs']:
        if (c.get('descs') == 1 and c.get('xfer_beats') == 9 and not c.get('source_backpressure')
                and c.get('resp_delay') == 0 and not c.get('gen_interleave')
                and c.get('base_seed_label') == 'default'):
            idx[(c['active_channels'], c['beats'])] = c
    cells = []
    for r in doc['points']:
        if r['group'] != 'beat':
            continue
        ref_c = idx.get((r['channels'], r['beats']))
        for d, keys in (('sink', ('sin', 'wr')), ('source', ('rd', 'sout'))):
            side = r.get(d)
            for k in keys:
                cell = {'channels': r['channels'], 'beats': r['beats'], 'direction': d,
                        'iface': k, 'byte': None, 'ref': None, 'delta_pp': None,
                        'byte_pass': bool(side and side.get('pass'))}
                if side and side.get('ifaces', {}).get(k):
                    cell['byte'] = side['ifaces'][k]['util']
                if ref_c and ref_c.get(d) and ref_c[d].get('perf'):
                    rm = (ref_c[d]['perf']['ifaces'].get(k) or {}).get('buckets')
                    if rm:
                        cell['ref'] = rm['util']
                if cell['byte'] is not None and cell['ref'] is not None:
                    cell['delta_pp'] = (cell['byte'] - cell['ref']) * 100.0
                cells.append(cell)
    return cells
