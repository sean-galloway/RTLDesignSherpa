#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
"""
Generate detailed coverage breakdown report for STREAM component.

This creates a separate detailed report file with:
1. Per-file line/toggle/branch coverage
2. Protocol coverage by interface (AXI read, AXI write, APB)
3. Uncovered lines with source context

Usage:
    python generate_detailed_coverage.py [--output-dir <dir>]
"""

import os
import sys
import json
import glob
import re
import subprocess
import tempfile
from datetime import datetime
from pathlib import Path
from collections import defaultdict
from typing import Dict, List, Any, Tuple


def get_script_dir() -> str:
    """Get the directory containing this script."""
    return os.path.dirname(os.path.abspath(__file__))


def get_default_paths() -> Tuple[str, str]:
    """Get default coverage and sim_build directories."""
    script_dir = get_script_dir()
    coverage_dir = os.path.join(script_dir, '..', 'dv', 'tests', 'fub', 'coverage_data')
    sim_build_dir = os.path.join(script_dir, '..', 'dv', 'tests', 'fub', 'local_sim_build')
    return os.path.abspath(coverage_dir), os.path.abspath(sim_build_dir)


def parse_verilator_coverage(merged_dat: str) -> Dict[str, Dict]:
    """Parse merged coverage.dat and return per-file, per-type stats."""
    stats = defaultdict(lambda: {'line': {'covered': 0, 'total': 0},
                                  'toggle': {'covered': 0, 'total': 0},
                                  'branch': {'covered': 0, 'total': 0}})
    
    with open(merged_dat, 'r') as f:
        for line in f:
            if not line.startswith('C '):
                continue
            
            parts = line.rsplit(' ', 1)
            if len(parts) != 2:
                continue
            
            try:
                count = int(parts[1].strip())
            except ValueError:
                continue
            
            metadata = parts[0]
            
            if '.sv' not in metadata:
                continue
            
            sv_match = re.search(r'/([^/]+\.sv)', metadata)
            if not sv_match:
                continue
            
            filename = sv_match.group(1)
            
            if 'v_line' in metadata:
                cov_type = 'line'
            elif 'v_toggle' in metadata:
                cov_type = 'toggle'
            elif 'v_branch' in metadata:
                cov_type = 'branch'
            else:
                continue
            
            stats[filename][cov_type]['total'] += 1
            if count > 0:
                stats[filename][cov_type]['covered'] += 1
    
    return dict(stats)


def merge_coverage_files(sim_build_dir: str) -> str:
    """Merge all coverage.dat files and return path to merged file."""
    coverage_files = []
    for test_dir in glob.glob(os.path.join(sim_build_dir, 'test_*')):
        coverage_dat = os.path.join(test_dir, 'coverage.dat')
        if os.path.exists(coverage_dat):
            coverage_files.append(coverage_dat)
    
    if not coverage_files:
        return None
    
    # Create temp file for merged output
    merged_dat = tempfile.NamedTemporaryFile(suffix='.dat', delete=False).name
    
    cmd = ['verilator_coverage', '--write', merged_dat] + coverage_files
    result = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
    
    if result.returncode != 0:
        print(f"Warning: verilator_coverage merge failed: {result.stderr}")
        return None
    
    return merged_dat


def parse_protocol_coverage(coverage_dir: str) -> Dict[str, Dict]:
    """Parse protocol coverage JSON files and aggregate by interface."""
    per_test_dir = os.path.join(coverage_dir, 'per_test')
    protocol_files = glob.glob(os.path.join(per_test_dir, '*_protocol.json'))
    
    # Interface-specific coverage
    interfaces = {
        'axi_read': {
            'groups': ['axi_read_burst_length', 'axi_read_burst_size', 'axi_read_burst_type', 'axi_read_response'],
            'points': {}
        },
        'axi_write': {
            'groups': ['axi_write_burst_length', 'axi_write_burst_size', 'axi_write_burst_type', 'axi_write_response'],
            'points': {}
        },
        'apb': {
            'groups': ['apb_transactions'],
            'points': {}
        },
        'handshakes': {
            'groups': ['handshakes'],
            'points': {}
        },
        'scenarios': {
            'groups': ['scenarios'],
            'points': {}
        },
        'other': {
            'groups': ['address_alignment', 'burst_type_x_size'],
            'points': {}
        }
    }
    
    for protocol_file in protocol_files:
        try:
            with open(protocol_file, 'r') as f:
                data = json.load(f)
        except Exception:
            continue
        
        groups = data.get('groups', {})
        for group_name, group_data in groups.items():
            # Find which interface this group belongs to
            target_interface = 'other'
            for iface_name, iface_data in interfaces.items():
                if group_name in iface_data['groups']:
                    target_interface = iface_name
                    break
            
            # Aggregate points
            for point_name, point_data in group_data.get('points', {}).items():
                key = f"{group_name}.{point_name}"
                if key not in interfaces[target_interface]['points']:
                    interfaces[target_interface]['points'][key] = {
                        'name': point_data.get('name', point_name),
                        'hits': 0,
                        'goal': point_data.get('goal', 1)
                    }
                interfaces[target_interface]['points'][key]['hits'] += point_data.get('hits', 0)
    
    return interfaces


def generate_detailed_report(output_dir: str = None) -> str:
    """Generate detailed coverage breakdown report."""
    coverage_dir, sim_build_dir = get_default_paths()
    
    if output_dir is None:
        output_dir = os.path.join(coverage_dir, 'reports')
    
    os.makedirs(output_dir, exist_ok=True)
    
    lines = []
    lines.append("# STREAM Detailed Coverage Breakdown")
    lines.append("")
    lines.append(f"**Generated:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    lines.append("")
    
    # Merge coverage files
    merged_dat = merge_coverage_files(sim_build_dir)
    
    if merged_dat:
        # Per-file coverage
        file_stats = parse_verilator_coverage(merged_dat)
        
        lines.append("## Code Coverage by File")
        lines.append("")
        lines.append("| File | Line | Toggle | Branch |")
        lines.append("|------|------|--------|--------|")
        
        totals = {'line': {'c': 0, 't': 0}, 'toggle': {'c': 0, 't': 0}, 'branch': {'c': 0, 't': 0}}
        
        for filename in sorted(file_stats.keys()):
            stats = file_stats[filename]
            row = [filename]
            for cov_type in ['line', 'toggle', 'branch']:
                c = stats[cov_type]['covered']
                t = stats[cov_type]['total']
                totals[cov_type]['c'] += c
                totals[cov_type]['t'] += t
                if t > 0:
                    pct = c / t * 100
                    row.append(f"{pct:.1f}% ({c}/{t})")
                else:
                    row.append("-")
            lines.append("| " + " | ".join(row) + " |")
        
        # Totals row
        row = ["**TOTAL**"]
        for cov_type in ['line', 'toggle', 'branch']:
            c = totals[cov_type]['c']
            t = totals[cov_type]['t']
            if t > 0:
                pct = c / t * 100
                row.append(f"**{pct:.1f}%** ({c}/{t})")
            else:
                row.append("-")
        lines.append("| " + " | ".join(row) + " |")
        lines.append("")
        
        # Clean up
        os.unlink(merged_dat)
    else:
        lines.append("## Code Coverage by File")
        lines.append("")
        lines.append("*No coverage data available*")
        lines.append("")
    
    # Protocol coverage by interface
    interfaces = parse_protocol_coverage(coverage_dir)
    
    lines.append("## Protocol Coverage by Interface")
    lines.append("")
    
    for iface_name, iface_data in interfaces.items():
        points = iface_data['points']
        if not points:
            continue
        
        covered = sum(1 for p in points.values() if p['hits'] >= p['goal'])
        total = len(points)
        pct = (covered / total * 100) if total > 0 else 0
        
        lines.append(f"### {iface_name.upper().replace('_', ' ')}")
        lines.append("")
        lines.append(f"**Coverage:** {covered}/{total} ({pct:.1f}%)")
        lines.append("")
        
        if points:
            lines.append("| Coverage Point | Hits | Goal | Status |")
            lines.append("|----------------|------|------|--------|")
            
            for key in sorted(points.keys()):
                p = points[key]
                status = "PASS" if p['hits'] >= p['goal'] else "MISS"
                lines.append(f"| {key} | {p['hits']} | {p['goal']} | {status} |")
            lines.append("")
    
    # Explanation of coverage types
    lines.append("## Coverage Type Definitions")
    lines.append("")
    lines.append("- **Line Coverage**: Percentage of executable code lines executed")
    lines.append("- **Toggle Coverage**: Percentage of signal bits that transitioned 0→1 and 1→0")
    lines.append("- **Branch Coverage**: Percentage of if/else and case branches taken")
    lines.append("")
    lines.append("*Note: Comments and declarations are NOT counted in coverage metrics.*")
    lines.append("")
    
    # Write report
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    report_path = os.path.join(output_dir, f'detailed_coverage_{timestamp}.md')
    
    with open(report_path, 'w') as f:
        f.write('\n'.join(lines))
    
    # Create symlink to latest
    latest_link = os.path.join(output_dir, 'detailed_coverage_latest.md')
    if os.path.exists(latest_link):
        os.unlink(latest_link)
    os.symlink(os.path.basename(report_path), latest_link)
    
    print(f"Detailed coverage report saved to: {report_path}")
    return report_path


def main():
    import argparse
    parser = argparse.ArgumentParser(description='Generate detailed coverage breakdown')
    parser.add_argument('--output-dir', help='Output directory for report')
    args = parser.parse_args()
    
    generate_detailed_report(args.output_dir)


if __name__ == '__main__':
    main()
