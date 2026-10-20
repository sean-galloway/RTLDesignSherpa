#!/usr/bin/env python3
import csv
from pathlib import Path
from collections import defaultdict

ROOT = Path(__file__).parent

def load(path):
    rows = []
    with open(path, newline='') as f:
        for r in csv.DictReader(f):
            if int(r['burst_len']) != 8:
                continue
            r['wr_bw_mb_s'] = float(r['wr_bw_mb_s'])
            r['rd_bw_mb_s'] = float(r['rd_bw_mb_s'])
            r['wr_cycles'] = int(r['wr_cycles'])
            r['rd_cycles'] = int(r['rd_cycles'])
            r['bytes_moved'] = int(r['bytes_moved'])
            rows.append(r)
    return rows

granite = load(ROOT / 'char_granite_n8_soak_2026-10-13.csv')
pumice = load(ROOT / 'char_pumice_soak_2026-10-13.csv')
litedram = load(ROOT / 'char_litedram75_soak_2026-10-13.csv')

scenarios = ['incremental', 'row_major', 'col_major', 'col_major_interleaved']
granite_configs = ['defaults', 'close_page', 'bank_interleave', 'open_page', 'inorder', 'age_thr']

def index(rows):
    d = defaultdict(dict)
    for r in rows:
        d[r['family']][r['config']] = r
    return d

gi = index(granite)
pi = index(pumice)
li = index(litedram)

def bpc(row, direction):
    cycles = row[f'{direction}_cycles']
    return row['bytes_moved'] / cycles if cycles else 0.0

def table(direction):
    lines = []
    header = ['scenario'] + granite_configs + ['pumice_best', 'litedram75']
    lines.append('| ' + ' | '.join(header) + ' |')
    lines.append('|' + '|'.join(['---'] * len(header)) + '|')
    for scen in scenarios:
        vals = []
        for cfg in granite_configs:
            r = gi[scen].get(cfg)
            vals.append(f"{r[f'{direction}_bw_mb_s']:.1f}" if r else '-')
        # pumice best
        p_rows = [pi[scen][c] for c in pi[scen] if scen in pi]
        if p_rows:
            best = max(p_rows, key=lambda r: r[f'{direction}_bw_mb_s'])
            vals.append(f"{best[f'{direction}_bw_mb_s']:.1f}")
        else:
            vals.append('-')
        # litedram75
        l = li[scen].get('litedram')
        vals.append(f"{l[f'{direction}_bw_mb_s']:.1f}" if l else '-')
        lines.append('| ' + ' | '.join([scen] + vals) + ' |')
    return '\n'.join(lines)

print('## Write bandwidth (MB/s)')
print(table('wr'))
print()
print('## Read bandwidth (MB/s)')
print(table('rd'))
print()

# Headline: best rd/wr MB/s and B/cycle across all scenarios for each contender
def best(rows, direction):
    best_row = max(rows, key=lambda r: r[f'{direction}_bw_mb_s'])
    return (best_row[f'{direction}_bw_mb_s'], bpc(best_row, direction), best_row['family'], best_row['config'])

for label, data in [('granite-N8', granite), ('pumice', pumice), ('litedram75', litedram)]:
    rmb, rbpc, rscen, rcfg = best(data, 'rd')
    wmb, wbpc, wscen, wcfg = best(data, 'wr')
    print(f"{label}: best rd {rmb:.1f} MB/s ({rbpc:.3f} B/cycle) @ {rscen}/{rcfg}; "
          f"best wr {wmb:.1f} MB/s ({wbpc:.3f} B/cycle) @ {wscen}/{wcfg}")
