#!/usr/bin/env python3
"""Generate alu-infer testplan YAML from real Verilator coverage data.

Per TEST_TYPE, merges that scenario's coverage.dat files (across levels,
PIPE_DEPTHs, timing profiles), annotates with verilator_coverage, and records
the covered lines (annotate numbering -- the same semantics
bin/cov_utils/verify_testplan_coverage.py checks with) as the scenario's
covers_lines. coverage_points carry alu_infer_top's ports with the hit count
annotate reports for each port line.

Run AFTER: COVERAGE=1 make run-all-func-parallel  (in alu-infer/dv/tests).
Paths resolve from this file's location, so it can run from anywhere:

    python3 projects/components/compute-eng-ip/alu-infer/dv/testplans/gen_alu_infer_testplan.py
"""

import re
import subprocess
import sys
import tempfile
from pathlib import Path

AREA_DIR = Path(__file__).resolve().parents[2]          # .../alu-infer
TESTS_DIR = AREA_DIR / 'dv' / 'tests'
RTL_DIR = AREA_DIR / 'rtl'
OUT_DIR = AREA_DIR / 'dv' / 'testplans'

RTL_FILES = [
    'alu_infer_top.sv',
    'alu_infer_rows.sv',
    'alu_infer_pipe.sv',
    'alu_infer_acc.sv',
]

TEST_TYPES = [
    'copy_timing', 'add_sub', 'mul', 'minmax', 'compare', 'relu', 'mac',
    'backpressure', 'error_opcode', 'special_grid', 'mixed_soak',
    'sub_ulp_corner', 'tag_join',
]

SCENARIOS = {
    'copy_timing': ('ALUINF-01', 'Handshake shell, copy, natural latency',
                    'Valid/ready shell, copy opcode, per-row natural-latency '
                    'retirement timing, in-order II=1 streaming',
                    'test_alu_infer (copy_timing)', 'high'),
    'add_sub': ('ALUINF-02', 'BF16 add/sub golden',
                'Add/sub lanes vs Python float RNE golden (1-ULP library contract)',
                'test_alu_infer (add_sub)', 'high'),
    'mul': ('ALUINF-03', 'BF16 multiply golden',
            'Mul lanes vs Python float RNE golden (1-ULP library contract)',
            'test_alu_infer (mul)', 'high'),
    'minmax': ('ALUINF-04', 'Min/max rows',
               'Min and max sub-ops on both lanes',
               'test_alu_infer (minmax)', 'medium'),
    'compare': ('ALUINF-05', 'Compare vs B and immediate',
                'Compare against operand B and threshold_imm; result_line is '
                'zero, mask packed low in result_flags[1:0]',
                'test_alu_infer (compare)', 'medium'),
    'relu': ('ALUINF-06', 'ReLU row',
             'ReLU including negative, -0, +0, -inf, NaN inputs',
             'test_alu_infer (relu)', 'medium'),
    'mac': ('ALUINF-07', 'MAC with FP32 accumulator',
            'MAC CLEAR/ACC/DRAIN/HOLD acc_ctrl sequences against the FP32 '
            'accumulator golden (math_bf16_fma contract)',
            'test_alu_infer (mac)', 'high'),
    'backpressure': ('ALUINF-08', 'Elastic backpressure',
                     'Consumer stall: results hold, tag FIFO fills, issue '
                     'backpressures, in-order resume on release',
                     'test_alu_infer (backpressure)', 'high'),
    'error_opcode': ('ALUINF-09', 'Reserved opcode handling',
                     'Out-of-range opcode retires in order and returns zero',
                     'test_alu_infer (error_opcode)', 'medium'),
    'special_grid': ('ALUINF-10', 'Special-value grid',
                     'Special-value grid (0/inf/NaN/subnormal) across '
                     'add/sub/mul/minmax/compare/relu',
                     'test_alu_infer (special_grid)', 'high'),
    'mixed_soak': ('ALUINF-11', 'Mixed-opcode soak',
                   'Random mixed-opcode sequence retires in order with golden '
                   'check; FUNC/FULL sweep the standard GAXI delay profiles '
                   '(fast, slow_producer, slow_consumer, gaxi_realistic, '
                   'gaxi_backpressure; FULL adds constrained, burst_pause, '
                   'high_throughput, gaxi_stress)',
                   'test_alu_infer (mixed_soak)', 'high'),
    'sub_ulp_corner': ('ALUINF-12', 'SUB 1-ULP corner',
                       'Directed SUB corner exposing the library adder 1-ULP '
                       'tolerance boundary',
                       'test_alu_infer (sub_ulp_corner)', 'low'),
    'tag_join': ('ALUINF-13', 'Tag-FIFO alignment join',
                 'Tag-based alignment: fast rows wait behind an earlier slow '
                 'row sharing the tag; first-offer timing checked cycle-exact',
                 'test_alu_infer (tag_join)', 'high'),
}

DIR_RE = re.compile(r'test_alu_infer_(.+)_(gate|func|full)_pd\d+_')
ANNOTATED_RE = re.compile(r'^([ %~])0*(\d+)')


def annotate_covered(dat_paths):
    """Merge dats, annotate, return {(basename, lineno): hits} using the same
    parsing rule as verify_testplan_coverage.get_covered_lines."""
    if not dat_paths:
        return {}
    with tempfile.TemporaryDirectory() as tmp:
        if len(dat_paths) == 1:
            merged = dat_paths[0]
        else:
            merged = str(Path(tmp) / 'merged.dat')
            subprocess.run(['verilator_coverage', '--write', merged] + dat_paths,
                           check=True, capture_output=True)
        ann_dir = Path(tmp) / 'ann'
        ann_dir.mkdir()
        subprocess.run(['verilator_coverage', '--annotate', str(ann_dir), merged],
                       check=True, capture_output=True)
        cov = {}
        for base in RTL_FILES:
            ann = ann_dir / base
            if not ann.exists():
                continue
            lines = ann.read_text(errors='replace').splitlines()
            offset = 1 if lines and 'verilator_coverage annotation' in lines[0] else 0
            for lineno, line in enumerate(lines[offset:], start=1):
                m = ANNOTATED_RE.match(line)
                if m and int(m.group(2)) > 0:
                    cov[(base, lineno)] = int(m.group(2))
        return cov


def main():
    sim_root = TESTS_DIR / 'local_sim_build'
    type_dats = {t: [] for t in TEST_TYPES}
    for d in sim_root.iterdir():
        m = DIR_RE.match(d.name)
        if not m:
            continue
        dat = d / 'coverage.dat'
        if dat.exists():
            t = m.group(1)
            if t in type_dats:
                type_dats[t].append(str(dat))

    for t, dats in type_dats.items():
        print(f'{t:16} {len(dats)} coverage.dat files', file=sys.stderr)
    missing = [t for t, dats in type_dats.items() if not dats]
    if missing:
        sys.exit(f'No coverage data for test types: {missing} -- '
                 f'run COVERAGE=1 make run-all-func-parallel first')

    # Per-scenario covered lines (annotate semantics, union across the 4 files).
    scen_lines = {}
    for t in TEST_TYPES:
        cov = annotate_covered(type_dats[t])
        scen_lines[t] = sorted(l for (_f, l) in cov)

    # Full union for the port hit counts.
    all_dats = [d for dats in type_dats.values() for d in dats]
    total_cov = annotate_covered(all_dats)

    # Port coverage points from alu_infer_top.sv.
    top_src = (RTL_DIR / 'alu_infer_top.sv').read_text().splitlines()
    points = []
    for lineno, text in enumerate(top_src, start=1):
        m = re.match(r'\s*(input|output)\s+logic\b', text)
        if not m:
            continue
        hits = total_cov.get(('alu_infer_top.sv', lineno), 0)
        content = re.sub(r'\s+', ' ', text.strip()).rstrip(',')
        points.append((lineno, m.group(1), content, hits))

    out = []
    w = out.append
    w('# Testplan for alu_infer_top (covers the full alu-infer pipeline:')
    w('# top + rows + pipe + acc -- one inseparable unit tested via the top)')
    w('# Maps functional test scenarios to Verilator coverage points.')
    w('#')
    w('# GENERATED FROM REAL COVERAGE DATA: per-scenario coverage.dat files')
    w('# (COVERAGE=1 make run-all-func-parallel) are merged and annotated;')
    w('# covers_lines are that scenario\'s covered lines in')
    w('# verilator_coverage --annotate numbering -- the same semantics')
    w('# bin/cov_utils/verify_testplan_coverage.py checks with. Regenerate')
    w('# with the same flow when the RTL or tests change.')
    w('')
    w('module: alu_infer_top')
    w('rtl_files:')
    for rf in RTL_FILES:
        w(f'  - projects/components/compute-eng-ip/alu-infer/rtl/{rf}')
    w('test_file: projects/components/compute-eng-ip/alu-infer/dv/tests/test_alu_infer.py')
    w('')
    w('# Module description:')
    w('# BF16 inference ALU at the cell execution-FSM seam. One GAXI-style')
    w('# valid/ready issue interface (op lines, func_sel, acc_ctrl), one')
    w('# valid/ready result interface. Elastic pipeline: comb rows retire the')
    w('# cycle after issue, the pipelined adder row after ADDER_LATENCY, MAC')
    w('# drains on acc_ctrl; an 8-bit tag FIFO joins ops that must align.')
    w('')
    w('parameters:')
    w('  - name: LINE_W')
    w('    default: 32')
    w('    description: Operand line width (2 x BF16 lanes)')
    w('  - name: N_LANES')
    w('    default: 2')
    w('    description: BF16 lanes per line (LINE_W/16)')
    w('  - name: ACC_W')
    w('    default: 32')
    w('    description: FP32 accumulator width')
    w('  - name: PIPE_DEPTH')
    w('    default: 8')
    w('    description: In-flight bound (tag FIFO depth); tested at 4 and 8')
    w('  - name: ADDER_LATENCY')
    w('    default: 3')
    w('    description: Pipelined adder row latency (0-4)')
    w('  - name: TAG_W')
    w('    default: 8')
    w('    description: Alignment tag width')
    w('')
    w('coverage_points:')
    for lineno, direction, content, hits in points:
        w(f'  - line: {lineno}')
        w(f'    type: {direction}_port')
        w(f'    content: "{content}"')
        w(f'    covered: {str(hits > 0).lower()}')
        w(f'    hit_count: {hits}')
    w('')
    w('functional_scenarios:')
    for t in TEST_TYPES:
        sid, name, desc, func, prio = SCENARIOS[t]
        lines = scen_lines[t]
        w(f'  - id: {sid}')
        w(f'    name: "{name}"')
        w(f'    description: "{desc}"')
        w(f'    test_function: {func}')
        w(f'    covers_lines: {lines}')
        w(f'    priority: {prio}')
        w('    status: verified')

    OUT_DIR.mkdir(parents=True, exist_ok=True)
    out_path = OUT_DIR / 'alu_infer_top_testplan.yaml'
    out_path.write_text('\n'.join(out) + '\n')
    print(f'Wrote {out_path}', file=sys.stderr)

    union_lines = sorted({l for lines in scen_lines.values() for l in lines})
    uncovered_ports = [p for p in points if p[3] == 0]
    print(f'Covered lines (union, all files): {len(union_lines)}', file=sys.stderr)
    print(f'Ports: {len(points)}, uncovered: {len(uncovered_ports)}', file=sys.stderr)
    for lineno, _d, content, _h in uncovered_ports:
        print(f'  UNCOVERED PORT line {lineno}: {content}', file=sys.stderr)


if __name__ == '__main__':
    main()
