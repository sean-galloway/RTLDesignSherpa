#!/usr/bin/env python3
"""Apples-to-apples 75 MHz DDR2 controller comparison table generator."""
import csv
from pathlib import Path
from collections import defaultdict

ROOT = Path(__file__).parent

def read_csv(path):
    with open(path, newline='') as f:
        return list(csv.DictReader(f))

def best_per_scenario(recs):
    """For controllers with multiple configs, pick the best MB/s per scenario."""
    by_scenario = defaultdict(list)
    for r in recs:
        by_scenario[r['scenario']].append(r)
    best = {}
    for scen, rows in by_scenario.items():
        best[scen] = max(rows, key=lambda r: (float(r['rd_bw_mb_s']) + float(r['wr_bw_mb_s'])))
    return best

def bytes_per_cycle(bytes_moved, cycles):
    return float(bytes_moved) / float(cycles)

pumice = read_csv(ROOT / 'char_pumice_soak_2026-10-13.csv')
granite = read_csv(ROOT / 'char_granite_soak_2026-10-13.csv')
litedram = read_csv(ROOT / 'char_litedram75_soak_2026-10-13.csv')

pumice_best = best_per_scenario(pumice)
granite_best = best_per_scenario(granite)
litedram_recs = {r['scenario']: r for r in litedram}

scenarios = ['incremental_bl8', 'row_major_bl8', 'col_major_bl8', 'col_major_interleaved_bl8']
scenario_labels = {
    'incremental_bl8': 'incremental',
    'row_major_bl8': 'row_major',
    'col_major_bl8': 'col_major',
    'col_major_interleaved_bl8': 'col_major_interleaved',
}

print("=" * 80)
print("Apples-to-apples 75 MHz DDR2 controller comparison")
print("=" * 80)
print()

print("Read MB/s (best config per controller)")
print("-" * 60)
print(f"{'scenario':<26} {'pumice':>10} {'granite':>10} {'litedram75':>10}")
print("-" * 60)
for s in scenarios:
    pr = pumice_best[s]
    gr = granite_best[s]
    lr = litedram_recs[s]
    print(f"{scenario_labels[s]:<26} {float(pr['rd_bw_mb_s']):>10.1f} {float(gr['rd_bw_mb_s']):>10.1f} {float(lr['rd_bw_mb_s']):>10.1f}")
print()

print("Write MB/s (best config per controller)")
print("-" * 60)
print(f"{'scenario':<26} {'pumice':>10} {'granite':>10} {'litedram75':>10}")
print("-" * 60)
for s in scenarios:
    pr = pumice_best[s]
    gr = granite_best[s]
    lr = litedram_recs[s]
    print(f"{scenario_labels[s]:<26} {float(pr['wr_bw_mb_s']):>10.1f} {float(gr['wr_bw_mb_s']):>10.1f} {float(lr['wr_bw_mb_s']):>10.1f}")
print()

print("Per-cycle headline: best read/write bytes/cycle across scenarios")
print("-" * 60)
print(f"{'controller':<16} {'best rd B/c':>12} {'scenario':>26}")
print(f"{'controller':<16} {'best wr B/c':>12} {'scenario':>26}")
print("-" * 60)

controllers = [
    ('pumice', pumice_best),
    ('granite', granite_best),
    ('litedram75', litedram_recs),
]

for name, recs in controllers:
    best_rd = max(scenarios, key=lambda s: bytes_per_cycle(recs[s]['bytes_moved'], recs[s]['rd_cycles']))
    best_wr = max(scenarios, key=lambda s: bytes_per_cycle(recs[s]['bytes_moved'], recs[s]['wr_cycles']))
    rd_bpc = bytes_per_cycle(recs[best_rd]['bytes_moved'], recs[best_rd]['rd_cycles'])
    wr_bpc = bytes_per_cycle(recs[best_wr]['bytes_moved'], recs[best_wr]['wr_cycles'])
    print(f"{name:<16} {rd_bpc:>12.3f} {scenario_labels[best_rd]:>26}")
    print(f"{name:<16} {wr_bpc:>12.3f} {scenario_labels[best_wr]:>26}")
    print()

# Summary sentence stats
pumice_best_rd = max(float(r['rd_bw_mb_s']) for r in pumice_best.values())
pumice_best_wr = max(float(r['wr_bw_mb_s']) for r in pumice_best.values())
granite_best_rd = max(float(r['rd_bw_mb_s']) for r in granite_best.values())
granite_best_wr = max(float(r['wr_bw_mb_s']) for r in granite_best.values())
litedram_best_rd = max(float(r['rd_bw_mb_s']) for r in litedram_recs.values())
litedram_best_wr = max(float(r['wr_bw_mb_s']) for r in litedram_recs.values())

print("Summary")
print("-" * 60)
print(f"Best read:  pumice={pumice_best_rd:.1f} MB/s, granite={granite_best_rd:.1f} MB/s, litedram75={litedram_best_rd:.1f} MB/s")
print(f"Best write: pumice={pumice_best_wr:.1f} MB/s, granite={granite_best_wr:.1f} MB/s, litedram75={litedram_best_wr:.1f} MB/s")
print()
print(f"At 75 MHz, LiteDRAM best read is {litedram_best_rd/pumice_best_rd:.2f}x pumice best read ({litedram_best_rd-pumice_best_rd:+.1f} MB/s).")
print(f"At 75 MHz, LiteDRAM best write is {litedram_best_wr/pumice_best_wr:.2f}x pumice best write ({litedram_best_wr-pumice_best_wr:+.1f} MB/s).")
