#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Generate perf/README.md and perf/plots/*.png for RAPIDS_ByteCharacterizationReport
from a byte-perf results JSON (host/byte_perf.py).

Every number comes from the JSON or from the RAPIDS Beats reference JSON. A cell
with no measurement is printed as a marked TBD; nothing is filled in by hand.

  make_byte_perf_report.py --results <json> [--beats-json <json>] [--out-dir <dir>] [--rev 0.1]
"""
import argparse
import json
import math
import os
import sys
from datetime import datetime

HERE = os.path.dirname(os.path.abspath(__file__))
RAPIDS = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(RAPIDS, 'flows-rapids', 'host'))
import byte_perf  # noqa: E402

DEFAULT_BEATS = os.path.join(RAPIDS, os.pardir, 'rapids_beats', 'reports', 'perf', 'json',
                             'genesys_dw256_obs_C.json')
TOL_PP = 0.5          # the RAPIDS Beats report's own "no cell moved by more than" threshold
TBD = '**TBD**'
HEADER = """<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> &middot; <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> &middot;
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> &middot;
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

"""


# ---------------------------------------------------------------- formatting
def f(v, fmt='{:.2f}', scale=1.0, unit=''):
    if v is None:
        return TBD
    if fmt.endswith('d}'):
        return fmt.format(int(round(v * scale))) + unit
    return fmt.format(v * scale) + unit


def table(head, rows, caption, align=None):
    align = align or ['l'] + ['r'] * (len(head) - 1)
    sep = {'l': '|---', 'r': '|---:', 'c': '|:--:'}
    out = ['| ' + ' | '.join(head) + ' |', ''.join(sep[a] for a in align) + '|']
    out += ['| ' + ' | '.join(str(c) for c in r) + ' |' for r in rows]
    return '\n'.join(out) + f"\n\n: {caption}\n"


class Figs:
    """Numbered figure headings (### Figure S.N) and matplotlib output."""

    def __init__(self, plot_dir):
        self.dir = plot_dir
        os.makedirs(plot_dir, exist_ok=True)
        self.counts = {}
        import matplotlib
        matplotlib.use('Agg')
        import matplotlib.pyplot as plt
        self.plt = plt

    def md(self, sec, title, fname, alt):
        n = self.counts[sec] = self.counts.get(sec, 0) + 1
        return f"### Figure {sec}.{n}: {title}\n\n![{alt}](plots/{fname})\n"

    def save(self, fig, fname):
        fig.tight_layout()
        fig.savefig(os.path.join(self.dir, fname), dpi=140)
        self.plt.close(fig)

    def placeholder(self, fname, what):
        fig, ax = self.plt.subplots(figsize=(6, 2))
        ax.text(0.5, 0.5, f"TBD: no measurement for {what}", ha='center', va='center')
        ax.axis('off')
        self.save(fig, fname)


# -------------------------------------------------------------------- data
class Data:
    def __init__(self, doc):
        self.doc = doc
        self.pts = doc['points']
        self.by_id = {p['id']: p for p in self.pts}
        self.peak = doc['peak_mb_s']
        self.bpb = doc['design']['beat_bytes']

    def side(self, pid, direction):
        p = self.by_id.get(pid)
        return None if p is None else p.get(direction)

    def sel(self, group):
        return [p for p in self.pts if p['group'] == group]


def _mbs(s):
    return None if (s is None or not s.get('perf_valid') or s.get('mb_s') is None) else s['mb_s']


def _pct(s):
    m = _mbs(s)
    return None if m is None else s['pct_peak'] * 100.0


# ------------------------------------------------------------------ figures
def fig_size(F, D, sec):
    plt = F.plt
    sizes = byte_perf.SIZES
    made = {}
    for metric, fname, ylabel in (('eff_axis', 'size_efficiency.png', 'efficiency = bytes / (beats x 32)'),
                                  ('mb_s', 'size_mbs.png', 'measured MB/s (aggregate)')):
        fig, axes = plt.subplots(1, 2, figsize=(10, 3.8), sharey=True)
        any_data = False
        for ax, dirn in zip(axes, ('sink', 'source')):
            for ch in byte_perf.CHANNELS:
                ys = []
                for p in sizes:
                    s = D.side(f"size_ch{ch}_p{p}_o0_d1", dirn)
                    v = None if s is None else (_mbs(s) if metric == 'mb_s' else s.get(metric))
                    ys.append(math.nan if v is None else v)
                if not all(math.isnan(y) for y in ys):
                    any_data = True
                    ax.plot(range(len(sizes)), ys, marker='o', label=f"{ch} ch")
            ax.set_xticks(range(len(sizes)))
            ax.set_xticklabels([str(p) for p in sizes], rotation=45)
            ax.set_xlabel('payload bytes per packet')
            ax.set_title(dirn.upper())
            ax.grid(alpha=.3)
            if metric == 'mb_s':
                ax.axhline(D.peak, color='k', ls='--', lw=1, label=f"peak {D.peak:.0f} MB/s")
                ax.set_yscale('log')
            ax.legend(fontsize=7)
        axes[0].set_ylabel(ylabel)
        if any_data:
            F.save(fig, fname)
        else:
            plt.close(fig)
            F.placeholder(fname, 'the size sweep')
        made[metric] = fname
    return made


def fig_offset(F, D, sec):
    plt = F.plt
    fig, axes = plt.subplots(1, 2, figsize=(10, 3.8), sharey=True)
    any_data = False
    for ax, dirn in zip(axes, ('sink', 'source')):
        for ch in (1, 8):
            for p in (33, 203, 1024, 4035):
                ys = []
                for o in (0, 1, 5, 31):
                    pid = f"size_ch{ch}_p{p}_o0_d1" if o == 0 else f"offset_ch{ch}_p{p}_o{o}_d1"
                    s = D.side(pid, dirn)
                    ys.append(math.nan if s is None else s.get('eff_mem'))
                if not all(math.isnan(y) for y in ys):
                    any_data = True
                    ax.plot(range(4), ys, marker='o', ls='-' if ch == 1 else '--', label=f"{p} B, {ch} ch")
        ax.set_xticks(range(4))
        ax.set_xticklabels(['0', '1', '5', '31'])
        ax.set_xlabel('start offset in the first beat (bytes)')
        ax.set_title(dirn.upper())
        ax.grid(alpha=.3)
        ax.legend(fontsize=6, ncol=2)
    axes[0].set_ylabel('efficiency on the memory side')
    if any_data:
        F.save(fig, 'offset_efficiency.png')
    else:
        plt.close(fig)
        F.placeholder('offset_efficiency.png', 'the offset sweep')


def fig_aligned(F, D, cells):
    plt = F.plt
    fig, ax = plt.subplots(figsize=(10, 3.6))
    pts = [(i, c['delta_pp']) for i, c in enumerate(cells) if c['delta_pp'] is not None]
    if pts:
        ax.axhspan(-TOL_PP, TOL_PP, color='green', alpha=.12, label=f"+/-{TOL_PP} pp")
        ax.plot([i for i, _ in pts], [d for _, d in pts], 'o', ms=3)
        ax.set_xlabel('beat-aligned cell (channels x beats x path x interface)')
        ax.set_ylabel('byte minus beats utilization (pp)')
        ax.legend(fontsize=7)
        ax.grid(alpha=.3)
        F.save(fig, 'aligned_delta.png')
    else:
        plt.close(fig)
        F.placeholder('aligned_delta.png', 'the beat-aligned comparison')


# ---------------------------------------------------------------- sections
def _ceiling(D):
    """Rate the byte-wise on-chip checkers can absorb: they feed 4 bytes per
    cycle and hold ready low meanwhile, so a beat costs BYTE_LANES/4 + 1 cycles."""
    cyc = D.bpb // 4 + 1
    return cyc, D.peak / cyc


def _ceiling_note(D):
    cyc, cap = _ceiling(D)
    return (f"**What this comparison can and cannot show.** The byte build's on-chip checkers "
            f"(`BYTE_CRC=1` on `axi4_slave_wr_crc_check` and `axis4_slave_pattern_check`) fold the "
            f"strobed bytes of each beat into the CRC four bytes per cycle and hold ready low while "
            f"they do, so a {D.bpb}-byte beat occupies {cyc} cycles. That caps the harness at "
            f"{D.peak:.0f} / {cyc} = {cap:.1f} MB/s ({100.0 / cyc:.1f} % of the {D.peak:.0f} MB/s peak), "
            f"which is where the large-transfer rows sit. The RAPIDS Beats reference used the "
            f"word-wide checkers and is not checker-bound. The large differences above are therefore "
            f"the checkers backpressuring the DUT, not evidence about the DUT's own throughput, and "
            f"the \"utilization unchanged\" criterion cannot be settled on this build. It needs the "
            f"beat-aligned rows measured with the word-wide checkers (`BYTE_CRC=0`) on a separate "
            f"performance bitstream, which also has to keep the 1-beat and 4-beat rows comparable. "
            f"Until then the beat-aligned rows are **not comparable** to the RAPIDS Beats report.\n")


def sec_aligned(D, beats_json, F):
    cells = byte_perf.compare_beats(D.doc, beats_json) if os.path.isfile(beats_json) else []
    md = ["## 3. Beat-aligned rows against the RAPIDS Beats report\n"]
    md.append("These rows use the beat-scaled path (`pkt_bytes=None`, beats per channel) on the byte DUT, "
              "which is how the RAPIDS Beats report measured its matrix: 9-beat bursts, response delay 0, "
              "backpressure off, default seed, bare bus meters. The metric is engaged utilization "
              "(`prod / (prod + bp + starv)`), the RAPIDS Beats headline metric. "
              f"\"Unchanged\" is checked numerically: every cell is compared to the same cell of "
              f"`{os.path.basename(beats_json)}` and must agree within {TOL_PP} percentage points, "
              "the threshold the RAPIDS Beats report itself applies between builds.\n")
    have = [c for c in cells if c['delta_pp'] is not None]
    n_cells = len(cells)
    rows = []
    for ch in byte_perf.CHANNELS:
        for b in byte_perf.ALIGNED_BEATS:
            row = [ch, b]
            dmax = None
            for d, k in (('sink', 'sin'), ('sink', 'wr'), ('source', 'rd'), ('source', 'sout')):
                c = next((c for c in cells if (c['channels'], c['beats'], c['direction'], c['iface']) == (ch, b, d, k)), None)
                if c is None or c['byte'] is None:
                    row.append(TBD)
                else:
                    ref = 'n/a' if c['ref'] is None else f"{c['ref'] * 100:.1f}"
                    row.append(f"{c['byte'] * 100:.1f} / {ref}")
                    if c['delta_pp'] is not None:
                        dmax = abs(c['delta_pp']) if dmax is None else max(dmax, abs(c['delta_pp']))
            row.append(TBD if dmax is None else f"{dmax:.2f}")
            rows.append(row)
    md.append(table(['Ch', 'Beats/ch', 'Sink AXIS-in % (byte / beats)', 'Sink AXI4-wr %',
                     'Source AXI4-rd %', 'Source AXIS-out %', 'Max abs delta (pp)'], rows,
                    "Engaged utilization, byte build / RAPIDS Beats reference, beat-aligned rows"))
    if not have:
        verdict = (f"{TBD}: no beat-aligned cell has been measured in this results file, "
                   "so the \"utilization unchanged\" check cannot be made yet.")
    else:
        bad = [c for c in have if abs(c['delta_pp']) > TOL_PP]
        worst = max(have, key=lambda c: abs(c['delta_pp']))
        missing = n_cells - len(have)
        status = "UNCHANGED" if not bad and not missing else ("CHANGED" if bad else "PARTIAL")
        verdict = (f"**Verdict: {status}.** {len(have)} of {n_cells} beat-aligned cells were compared; "
                   f"{len(bad)} differ by more than {TOL_PP} pp; the largest difference is "
                   f"{worst['delta_pp']:+.2f} pp (ch {worst['channels']}, {worst['beats']} beats, "
                   f"{worst['direction']} {worst['iface']}).")
        if missing:
            verdict += f" {missing} cells have no measurement and print as TBD."
        if bad:
            verdict += " Cells over the threshold: " + "; ".join(
                f"ch{c['channels']} b{c['beats']} {c['direction']} {c['iface']} {c['delta_pp']:+.2f} pp"
                for c in bad[:12]) + ("; ..." if len(bad) > 12 else "") + "."
    md.append(verdict + "\n")
    md.append(_ceiling_note(D))
    md.append(F.md(3, "Byte minus beats utilization, beat-aligned cells", 'aligned_delta.png',
                   'utilization delta'))
    fig_aligned(F, D, cells)
    # bytes per beat of the same rows
    rows = []
    for ch in byte_perf.CHANNELS:
        for b in byte_perf.ALIGNED_BEATS:
            pid = f"beat_ch{ch}_b{b}"
            row = [ch, b]
            for d in ('sink', 'source'):
                s = D.side(pid, d)
                row += [f(s and s.get('bytes'), '{:d}'), f(s and s.get('axis_beats'), '{:d}'),
                        f(s and s.get('eff_axis'), '{:.3f}'), f(s and _mbs(s), '{:.0f}'),
                        f(s and _pct(s), '{:.1f}', 1, ' %')]
            rows.append(row)
    md.append(table(['Ch', 'Beats/ch', 'Sink bytes', 'Sink beats', 'Sink eff', 'Sink MB/s', 'Sink % peak',
                     'Src bytes', 'Src beats', 'Src eff', 'Src MB/s', 'Src % peak'], rows,
                    f"Beat-aligned rows: bytes, beats, efficiency, MB/s and share of the {D.peak:.0f} MB/s peak"))
    eff = [D.side(f"beat_ch{ch}_b{b}", d).get('eff_axis')
           for ch in byte_perf.CHANNELS for b in byte_perf.ALIGNED_BEATS for d in ('sink', 'source')
           if D.side(f"beat_ch{ch}_b{b}", d) and D.side(f"beat_ch{ch}_b{b}", d).get('eff_axis') is not None]
    if eff:
        md.append(f"Every beat-aligned row moves whole beats, so efficiency is 1.000 by construction; "
                  f"measured range over {len(eff)} rows: {min(eff):.3f} to {max(eff):.3f}.\n")
    return '\n'.join(md)


def _size_rows(D, group, direction, specs):
    rows = []
    for ch, p, o, d in specs:
        pid = f"{group}_ch{ch}_p{p}_o{o}_d{d}"
        s = D.side(pid, direction)
        ok = 'PASS' if (s and s['pass']) else ('FAIL' if s else TBD)
        rows.append([p, o, ch, f(s and s.get('bytes'), '{:d}'), f(s and s.get('axis_beats'), '{:d}'),
                     f(s and s.get('mem_beats'), '{:d}'), f(s and s.get('eff_axis'), '{:.3f}'),
                     f(s and s.get('eff_mem'), '{:.3f}'), f(s and _mbs(s), '{:.1f}'),
                     f(s and _pct(s), '{:.2f}', 1, ' %'), ok])
    return rows


HEAD = ['Payload B', 'Offset', 'Ch', 'Bytes moved', 'AXIS beats', 'Mem beats', 'Eff (AXIS)',
        'Eff (mem)', 'MB/s', f'% of peak', 'Result']


def sec_size(D, F):
    md = ["## 4. Transfer size (offset 0)\n"]
    md.append("One descriptor per channel, payload in bytes, start offset 0. Bytes moved and beats are "
              "totals over the active channels; efficiency is payload bytes over beats times 32 bytes per "
              "beat, on the AXIS side and on the memory side. MB/s is total bytes over the measurement window "
              f"(the longer of the stream and memory windows) and is always shown with its share of the "
              f"{D.peak:.0f} MB/s peak (100 MHz x 32 B).\n")
    specs = [(ch, p, 0, 1) for p in byte_perf.SIZES for ch in byte_perf.CHANNELS]
    for d in ('sink', 'source'):
        md.append(f"### 4.{1 if d == 'sink' else 2} {d.capitalize()} path\n")
        md.append(table(HEAD, _size_rows(D, 'size', d, specs), f"Size sweep, {d} path, offset 0"))
    md.append(F.md(4, "Efficiency against payload size", 'size_efficiency.png', 'efficiency vs size'))
    md.append(F.md(4, "Measured MB/s against payload size, peak as the dashed line", 'size_mbs.png', 'MB/s vs size'))
    made = fig_size(F, D, 4)  # noqa: F841
    # computed observations
    obs = []
    for d in ('sink', 'source'):
        big = D.side('size_ch8_p4096_o0_d1', d)
        small = D.side('size_ch8_p1_o0_d1', d)
        if big and _mbs(big):
            obs.append(f"{d.capitalize()}, 8 channels, 4096 B: {_mbs(big):.0f} MB/s = {_pct(big):.1f} % of the "
                       f"{D.peak:.0f} MB/s peak at efficiency {big['eff_axis']:.3f}.")
        if big and small and _mbs(big) and _mbs(small):
            obs.append(f"{d.capitalize()}, 8 channels: 1 B payload reaches {_mbs(small):.1f} MB/s, "
                       f"{_mbs(big) / _mbs(small):.0f}x less than 4096 B; the window is dominated by fixed "
                       f"per-packet latency ({small['window']} cycles for one beat per channel).")
    if obs:
        md.append("Observations from this data:\n\n" + '\n'.join(f"- {o}" for o in obs) + "\n")
    return '\n'.join(md)


def sec_offset(D, F):
    md = ["## 5. Start offset\n"]
    md.append("A descriptor may start mid-beat. The offset moves payload into an extra memory beat when "
              "`offset + payload` crosses a beat boundary, lowering memory-side efficiency while the AXIS "
              "side, which packs from lane 0, is unchanged. Offset 0 rows repeat the size sweep.\n")
    specs = [(ch, p, o, 1) for ch in (1, 8) for p in (33, 203, 1024, 4035) for o in (0, 1, 5, 31)]
    for d in ('sink', 'source'):
        rows = []
        for ch, p, o, n in specs:
            grp = 'size' if o == 0 else 'offset'
            rows += _size_rows(D, grp, d, [(ch, p, o, n)])
        md.append(f"### 5.{1 if d == 'sink' else 2} {d.capitalize()} path\n")
        md.append(table(HEAD, rows, f"Offset sweep, {d} path"))
    md.append(F.md(5, "Memory-side efficiency against start offset", 'offset_efficiency.png', 'efficiency vs offset'))
    fig_offset(F, D, 5)
    extra = []
    for p in (33, 203, 1024, 4035):
        for o in (1, 5, 31):
            s0, s1 = D.side(f"size_ch1_p{p}_o0_d1", 'sink'), D.side(f"offset_ch1_p{p}_o{o}_d1", 'sink')
            if s0 and s1 and s0.get('mem_beats') is not None and s1.get('mem_beats') is not None \
                    and s1['mem_beats'] > s0['mem_beats']:
                extra.append(f"{p} B at offset {o}: {s0['mem_beats']} -> {s1['mem_beats']} memory beats")
    if extra:
        md.append("Offsets that cost an extra memory beat (sink, 1 channel): " + '; '.join(extra) + ".\n")
    return '\n'.join(md)


def sec_chain(D):
    md = ["## 6. Descriptor chains\n"]
    md.append("Several descriptors per channel back to back (4 channels), offset 0. Efficiency counts "
              "payload over all beats of the chain.\n")
    pts = [p for p in D.pts if p['group'] == 'chain']
    planned = [q for q in byte_perf.build_points(D.doc['profile']) if q['group'] == 'chain']
    rows = []
    for q in planned:
        for d in ('sink', 'source'):
            s = D.side(q['id'], d)
            rows.append([q['payload'], q['descs'], d, f(s and s.get('bytes'), '{:d}'),
                         f(s and s.get('axis_beats'), '{:d}'), f(s and s.get('eff_axis'), '{:.3f}'),
                         f(s and _mbs(s), '{:.1f}'), f(s and _pct(s), '{:.2f}', 1, ' %'),
                         'PASS' if (s and s['pass']) else ('FAIL' if s else TBD)])
    md.append(table(['Payload B', 'Descs', 'Path', 'Bytes moved', 'AXIS beats', 'Eff (AXIS)', 'MB/s',
                     '% of peak', 'Result'], rows, "Descriptor chains, 4 channels"))
    if not pts:
        md.append(f"{TBD}: no chain point has been measured.\n")
    return '\n'.join(md)


def sec_bp(D):
    md = ["## 7. Source backpressure (integrity only)\n"]
    md.append("The source backpressure is paced by the host toggling the checker's ready over UART, so "
              "the cycle counts measure the host, not the DUT (rapids TASK-085). These rows are integrity "
              "checks: bytes and beats must still match and the golden CRCs must agree. Their MB/s is not "
              "reported.\n")
    planned = [q for q in byte_perf.build_points(D.doc['profile']) if q['group'] == 'bp']
    rows = []
    for q in planned:
        s = D.side(q['id'], 'source')
        e = (s or {}).get('expected') or {}
        rows.append([q['channels'], q['payload'], q['offset'], f(e.get('bytes'), '{:d}'),
                     f(e.get('axis_beats'), '{:d}'), 'n/a (host-paced)',
                     'PASS' if (s and s['pass']) else ('FAIL' if s else TBD)])
    md.append(table(['Ch', 'Payload B', 'Offset', 'Expected bytes', 'Expected AXIS beats', 'MB/s', 'Result'], rows,
                    "Source with backpressure, integrity rows"))
    return '\n'.join(md)


def sec_failures(D):
    md = ["## 8. Failures, caveats and coverage\n"]
    fails = [(p, d) for p in D.pts for d in p.get('directions', ('sink', 'source'))
             if isinstance(p.get(d), dict) and not p[d]['pass']]
    if not fails:
        md.append("No measured point failed.\n")
    else:
        rows = []
        for p, d in fails:
            errs = '; '.join(p[d].get('errors', [])[:2]) or 'no detail'
            rows.append([p['id'], d, p.get('after_failure') or '-', errs.replace('|', '/')])
        md.append(table(['Point', 'Path', 'After earlier failure', 'Errors (first two)'], rows,
                        "Failed points as recorded, never dropped", align=['l', 'l', 'l', 'l']))
        md.append("A failure is recorded with its errors and is never retried away. Points after the first "
                  "failure carry the id of that failure (`after_failure`): the sticky sink packet-length flag "
                  "and the AXI response error flags clear only on `aresetn`, and `CHANNEL_RESET` does not "
                  "reach them, so one failed point can poison the ones after it. A failure that is repeatable "
                  "at its own coordinates, with no earlier failure in the file, is a genuine result.\n")
    planned = byte_perf.build_points(D.doc['profile'])
    missing = [p['id'] for p in planned if p['id'] not in D.by_id]
    md.append(f"Coverage: {len(planned) - len(missing)} of {len(planned)} planned points of profile "
              f"`{D.doc['profile']}` are in this file ({D.doc.get('passed', 0)} passed, "
              f"{D.doc.get('failed', 0)} failed).\n")
    if D.doc.get('aborted'):
        md.append(f"The run aborted: {D.doc['aborted']}.\n")
    if missing:
        md.append("Planned points with no measurement (TBD): " + ', '.join(f"`{m}`" for m in missing[:40]) +
                  (f", and {len(missing) - 40} more" if len(missing) > 40 else "") + ".\n")
    md.append("Standing limitations of the design, not of this measurement:\n\n"
              "- The sink `s_axis_tready` is one signal qualified by TID, so a beat for a channel whose "
              "packet record has not arrived blocks every channel behind it on the stream (head-of-line "
              "blocking, inherent and documented).\n"
              "- TYPE=EXT descriptors stay beat-aligned by design and are not part of the byte sweeps.\n"
              "- Each interface has its own measurement window; the `sin` window runs from the first to the "
              "last stream beat (rapids ISSUE-001), so windows differ per interface and MB/s here uses the "
              "longer of the stream and memory windows.\n")
    return '\n'.join(md)


def _hx(v):
    return TBD if v is None else f"0x{v:08X}"


def _device_section(d):
    """Device readback recorded by the campaign; absent in files that predate it."""
    sess = d.get('sessions')
    if not sess:
        return ("No device readback is recorded in this results file: it was measured before the "
                "campaign began reading CSR_ID, BUILD and the configure-time sentinel at the start "
                "and end of each session. The bitstream identity above is the file hash the run "
                "was started from, not a readback, so a reprogram by another user during the run "
                "would not have been detected. The final run records the readback.\n")
    rows = []
    for i, x in enumerate(sess, 1):
        a, b = x.get('start') or {}, x.get('end') or {}
        rows.append([i, f"`{str(x.get('bitstream_sha256') or TBD)[:16]}`", _hx(a.get('csr_id')),
                     _hx(a.get('build')), _hx(a.get('sentinel')), _hx(b.get('sentinel')),
                     'yes' if x.get('stable') else 'NO', 'yes' if x.get('aborted') else 'no'])
    txt = table(['Session', 'Bitstream sha256', 'CSR_ID', 'BUILD', 'Sentinel start', 'Sentinel end',
                 'Stable', 'Aborted'], rows, "Device readback per session")
    txt += ("\nThe sentinel is the MON_LIMIT register written once at configure time. It resets on any "
            "FPGA reconfiguration, so a change between readbacks means the device was reprogrammed "
            "during the run. A point measured across such a change is dropped, not recorded. "
            f"Device stable for the whole run: {'yes' if d.get('device_stable') else 'NO'}.\n")
    return txt


def sec_provenance(D, results_path, beats_json):
    d = D.doc
    md = ["## 9. Provenance and reproduction\n"]
    rows = [['Results file', f"`{os.path.basename(results_path)}`"],
            ['Timestamp', d.get('timestamp', TBD)],
            ['Profile', f"`{d.get('profile')}`"],
            ['Status', 'PRELIMINARY' if d.get('prelim') else 'final'],
            ['Bitstream', f"`{(d.get('bitstream') or {}).get('path')}` sha256 "
                          f"`{((d.get('bitstream') or {}).get('sha256') or TBD)[:16]}`"],
            ['Design', f"{d['design']['data_width']}-bit, {d['design']['channels']} channels, "
                       f"{d['design']['sram_bytes_per_channel']} B SRAM per channel, "
                       f"{d['aclk_hz'] / 1e6:.0f} MHz, peak {D.peak:.0f} MB/s per direction"],
            ['Beats reference', f"`{os.path.basename(beats_json)}`"]]
    md.append(table(['Item', 'Value'], rows, "Provenance", align=['l', 'l']))
    md.append(_device_section(d))
    md.append("One command runs the campaign and regenerates this report:\n\n"
              "```bash\n"
              "cd projects/fpga-systems/Genesys2/rapids/flows-rapids\n"
              "./byte_perf.sh --profile standard          # PRELIMINARY: writes *_prelim_*.json\n"
              "./byte_perf.sh --profile full --final      # final numbers, after the channel-reset fix is on the board\n"
              "```\n")
    return '\n'.join(md)


def sec_defs(D):
    md = ["## 2. Definitions\n"]
    rows = [['Bytes moved', 'Total payload bytes over all active channels and descriptors; from the exact byte count of the AXIS bus meter.'],
            ['Beats moved', 'Accepted beats on the interface named: AXIS beats on the stream side, memory beats on the AXI side.'],
            ['Efficiency', f'payload bytes / (beats x BYTE_LANES), BYTE_LANES = {D.bpb}. 1.0 means every lane of every beat carried payload.'],
            ['MB/s', 'Total bytes / measurement window, windows counted in 100 MHz cycles by the harness meters, not wall clock.'],
            ['Peak', f'{D.peak:.0f} MB/s = 100 MHz x {D.bpb} B, per direction. Shown beside every measured MB/s value.'],
            ['Engaged utilization', 'prod / (prod + bp + starv) on one interface; the RAPIDS Beats headline metric, used only for the beat-aligned comparison.']]
    md.append(table(['Term', 'Meaning'], rows, "Definitions", align=['l', 'l']))
    return '\n'.join(md)


def sec_headline(D):
    md = ["## 1. Headline\n"]
    rows = []
    for d in ('sink', 'source'):
        s = D.side('size_ch8_p4096_o0_d1', d)
        b = D.side('beat_ch8_b4096', d)
        rows.append([d.capitalize(), 'byte path, 4096 B x 8 ch',
                     f(s and s.get('eff_axis'), '{:.3f}'), f(s and _mbs(s), '{:.0f}'),
                     f(s and _pct(s), '{:.1f}', 1, ' %')])
        rows.append([d.capitalize(), 'beat path, 4096 beats x 8 ch',
                     f(b and b.get('eff_axis'), '{:.3f}'), f(b and _mbs(b), '{:.0f}'),
                     f(b and _pct(b), '{:.1f}', 1, ' %')])
    md.append(table(['Path', 'Point', 'Efficiency', 'MB/s measured', f'% of {D.peak:.0f} MB/s peak'], rows,
                    "Largest transfers at 8 channels"))
    cyc, cap = _ceiling(D)
    md.append(f"These rates sit at the harness checker ceiling of {D.peak:.0f} / {cyc} = {cap:.1f} MB/s, "
              f"not at the DUT's limit: the byte-wise CRC checkers take {cyc} cycles per {D.bpb}-byte beat "
              f"(section 3). Read every MB/s in this report against both the {D.peak:.0f} MB/s peak and "
              f"that ceiling. Efficiency (payload over beats x lanes) does not depend on the checker.\n")
    return '\n'.join(md)


def build(results_path, beats_json, out_dir, rev):
    with open(results_path) as fh:
        doc = json.load(fh)
    D = Data(doc)
    F = Figs(os.path.join(out_dir, 'plots'))
    prelim = doc.get('prelim')
    md = [HEADER]
    md.append("# RAPIDS Byte-Granular DMA: Byte Characterization Report\n")
    md.append(f"**Version:** {rev}  \n**Date:** {datetime.now().strftime('%Y-%m-%d')}  \n"
              f"**Platform:** Genesys 2, {doc['design']['data_width']}-bit, {doc['design']['channels']} channels, "
              f"{doc['aclk_hz'] / 1e6:.0f} MHz  \n**Results:** `{os.path.basename(results_path)}`\n")
    if prelim:
        md.append("> **PRELIMINARY.** These numbers were measured on the bitstream that predates the "
                  "channel-reset fix. They validate the tooling and the report; the final numbers replace "
                  "them after the rebuild. Cells without a measurement are marked **TBD**.\n")
    md.append("---\n")
    md.append(sec_headline(D))
    md.append(sec_defs(D))
    md.append(sec_aligned(D, beats_json, F))
    md.append(sec_size(D, F))
    md.append(sec_offset(D, F))
    md.append(sec_chain(D))
    md.append(sec_bp(D))
    md.append(sec_failures(D))
    md.append(sec_provenance(D, results_path, beats_json))
    os.makedirs(out_dir, exist_ok=True)
    out = os.path.join(out_dir, 'README.md')
    with open(out, 'w') as fh:
        fh.write('\n'.join(md))
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument('--results', required=True, help='byte-perf results JSON')
    ap.add_argument('--beats-json', default=os.path.normpath(DEFAULT_BEATS))
    ap.add_argument('--out-dir', default=os.path.join(HERE, 'perf'))
    ap.add_argument('--rev', default='0.1')
    ap.add_argument('--pdf', action='store_true', help='also build the DOCX/PDF through generate_reports_pdf.sh')
    a = ap.parse_args()
    out = build(a.results, a.beats_json, a.out_dir, a.rev)
    print(f"wrote {out}")
    if a.pdf:
        import subprocess
        sys.exit(subprocess.call([os.path.join(HERE, 'generate_reports_pdf.sh'), '--rev', a.rev]))


if __name__ == '__main__':
    main()
