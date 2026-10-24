#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Synthesize one module of the repo against ASAP7 and report where it lands.

The same recipe as timing_char_sweep.py (yosys-slang, synth -flatten,
dfflibmap + abc against the ASAP7 RVT Liberty, `stat -liberty`), pointed at
any repo module through its filelist: the ABC mapper's achieved delay and
logic depth, the Liberty cell count / flop count / area, and -- with --sta --
an OpenSTA register-to-register check at the given clock period, naming the
worst path. Minutes, not a Vivado run; a proxy, not a sign-off (see
feedback: ASAP7 flops within 3 percent of Vivado FF; comb cells about 4 x LUT).

    python3 synth_module.py --top bridge_2x2_rw_xbar \\
        --filelist projects/components/fabric-gen-ip/bridge/rtl/filelists/bridge_2x2_rw.f \\
        --period-ps 1000 --sta --json out.json --tag rr

Output: one JSON row (appended to --json when given) and one line on stdout.
Work files land under --workdir (default /tmp/charwork/asap7/modules/<top>).
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

REPO_ROOT = Path(subprocess.run(['git', 'rev-parse', '--show-toplevel'], capture_output=True,
                                text=True, check=True).stdout.strip())
sys.path.insert(0, str(REPO_ROOT / 'bin'))
from TBClasses.shared.filelist_utils import get_sources_from_filelist  # noqa: E402

LIB_DIR = Path.home() / 'eda/asap7_merged'
LIB = {c: LIB_DIR / f'asap7sc7p5t_RVT_{c}_nldm.lib' for c in ('TT', 'FF', 'SS')}
# OpenSTA: the merged Liberty maps fine in ABC but its flop setup / hold arcs
# carry no table models, so STA sees no constrained endpoint. STA reads the
# per-family ASAP7 files instead, extracted once from the PDK's 7z archives.
# ~/eda/sta-asap7 strips LD_LIBRARY_PATH so Vivado's libtcl does not shadow
# the system one (the bare binary cannot find init.tcl).
STA = Path.home() / 'eda/sta-asap7'
ASAP7_NLDM = Path.home() / 'eda/asap7/asap7sc7p5t_28/LIB/NLDM'
STA_LIB_DIR = Path('/tmp/charwork/asap7/libs')
STA_FAMILIES = ('SIMPLE', 'INVBUF', 'AO', 'OA', 'SEQ')
# the flop cells the characterization sweep keeps out of the mapping
DONT_USE = ('DFFASRHQN*', 'DFFHQN*', 'DFFLQN*', 'SDFL*', 'DFFLQ*')
NUM = r'(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?'
ABC_DELAY_RE = re.compile(rf'Delay\s*=\s*({NUM})\s*ps')
ABC_LEV_RE = re.compile(r'\blev\s*=\s*(\d+)')


def write_scripts(args, work: Path, sources: list[str], incdirs: list[str]) -> Path:
    lib = LIB[args.corner]
    abc_script = work / 'abc.script'
    abc_script.write_text(f"strash\nmap -p -B 0.2 -A 0.9 -D {args.period_ps}\nbuffer -c -N 6\ntopo\n"
                          "upsize -c\ndnsize -c\nstime -c\nprint_stats -m\n")
    gparams = ' '.join(f'-G {g}' for g in args.param)
    incs = ' '.join(f'-I{d}' for d in incdirs)
    srcs = ' \\\n        '.join(sources)
    dont_use = ' '.join(f'-dont_use {c}' for c in DONT_USE)
    keep = ''.join(f'setattr -set keep 1 w:{g}\n' for g in args.keep_nets)
    ys = f"""plugin -i slang
read_slang {incs} --top {args.top} {gparams} \\
        {srcs}
{keep}async2sync
read_liberty -lib {lib}
synth -top {args.top} -flatten
dfflibmap -liberty {lib} {dont_use}
abc -liberty {lib} -script {abc_script}
opt_clean{'' if args.keep_names else ' -purge'}
tee -o {work / 'stat.txt'} stat -liberty {lib}
write_verilog -noattr {work / 'netlist.v'}
"""
    (work / 'synth.ys').write_text(ys)
    return work / 'synth.ys'


def parse_stat(text: str) -> dict:
    """Yosys `stat -liberty` (0.62): a `<count> <area> cells` total line, one
    `<count> <area> <cell>` line per Liberty cell, and the chip area line."""
    out = {'cells': None, 'area_um2': None, 'flops': 0, 'flop_area_um2': 0.0}
    for line in text.splitlines():
        m = re.match(r'\s+(\d+)\s+(' + NUM + r')\s+cells\s*$', line)
        if m:
            out['cells'] = int(m.group(1))
            continue
        m = re.match(r'\s+(\d+)\s+(' + NUM + r')\s+(\S+)\s*$', line)
        if m and ('DFF' in m.group(3) or 'SDF' in m.group(3)):
            out['flops'] += int(m.group(1))
            out['flop_area_um2'] += float(m.group(2))
    m = re.search(r'Chip area for (?:top )?module.*?:\s+(' + NUM + ')', text)
    out['area_um2'] = float(m.group(1)) if m else None
    out['flop_area_um2'] = round(out['flop_area_um2'], 3)
    return out


def sta_libs() -> list[Path]:
    STA_LIB_DIR.mkdir(parents=True, exist_ok=True)
    libs = []
    for fam in STA_FAMILIES:
        have = sorted(STA_LIB_DIR.glob(f'asap7sc7p5t_{fam}_RVT_TT_nldm_*.lib'))
        if not have:
            arc = sorted(ASAP7_NLDM.glob(f'asap7sc7p5t_{fam}_RVT_TT_nldm_*.lib.7z'))
            if not arc:
                sys.exit(f'no ASAP7 {fam} RVT TT Liberty under {ASAP7_NLDM}')
            subprocess.run(['7z', 'x', '-y', str(arc[0])], cwd=STA_LIB_DIR, check=True,
                           capture_output=True)
            have = sorted(STA_LIB_DIR.glob(f'asap7sc7p5t_{fam}_RVT_TT_nldm_*.lib'))
        libs.append(have[0])
    return libs


def inst_out_net(netlist: str, inst: str) -> str | None:
    """The net on a mapped cell's output pin (Y / Q / QN / CON / SN)."""
    m = re.search(r'\n\s+\S+\s+' + re.escape(inst) + r'\s*\((.*?)\);', netlist, re.S)
    if not m:
        return None
    o = re.search(r'\.(?:Y|Q|QN|CON|SN)\s*\(\s*(.*?)\s*\)', m.group(1))
    return o.group(1).strip() if o else None


def flop_nets(netlist: str, inst: str) -> tuple[str | None, str | None]:
    """(D net, Q net) of a mapped flop instance: Yosys anonymises the instance
    but keeps the RTL register name on its Q net, which names the path end."""
    m = re.search(r'\n\s+\S+\s+' + re.escape(inst) + r'\s*\((.*?)\);', netlist, re.S)
    if not m:
        return None, None
    body = m.group(1)
    d = re.search(r'\.D\s*\(\s*(.*?)\s*\)', body)
    q = re.search(r'\.QN?\s*\(\s*(.*?)\s*\)', body)
    return (d.group(1).strip() if d else None, q.group(1).strip() if q else None)


def run_sta(args, work: Path) -> dict:
    """OpenSTA on the mapped netlist: register-to-register only (no I/O
    delays, so the unconstrained port paths drop out), worst path named."""
    if args.corner != 'TT':
        return {'sta_rc': None, 'sta_error': 'STA libraries extracted for TT only'}
    tcl = work / 'sta.tcl'
    rpt = work / 'sta.rpt'
    reads = ''.join(f'read_liberty {l}\n' for l in sta_libs())
    # the ASAP7 Liberty time unit is 1 ps, so the period is in ps as given
    tcl.write_text(f"""{reads}read_verilog {work / 'netlist.v'}
link_design {args.top}
create_clock -name clk -period {args.period_ps} [get_ports {args.clock}]
report_checks -path_delay max -group_path_count 1 -digits 2 > {rpt}
puts "WORST_SLACK [worst_slack -max]"
puts "TNS [total_negative_slack -max]"
exit
""")
    r = subprocess.run([str(STA), '-no_init', '-no_splash', '-exit', str(tcl)],
                       capture_output=True, text=True, cwd=work, timeout=1800)
    out = {'sta_rc': r.returncode}
    m = re.search(r'WORST_SLACK\s+(-?' + NUM + ')', r.stdout)
    out['sta_slack_ps'] = round(float(m.group(1)), 1) if m else None
    m = re.search(r'TNS\s+(-?' + NUM + ')', r.stdout)
    out['sta_tns_ps'] = round(float(m.group(1)), 1) if m else None
    if rpt.exists():
        t = rpt.read_text()
        net = (work / 'netlist.v').read_text()
        sp = re.search(r'Startpoint:\s+(\S+)', t)
        ep = re.search(r'Endpoint:\s+(\S+)', t)
        da = re.search(r'(-?' + NUM + r')\s+data arrival time', t)
        out['sta_arrival_ps'] = round(float(da.group(1)), 1) if da else None
        out['sta_levels'] = len(re.findall(r'_ASAP7_75t_R\)\s*$', t.split('data arrival time')[0], re.M)) - 1
        insts = re.findall(r'[\^v]\s+(\S+)/[A-Z]+\s*\(', t.split('data arrival time')[0])
        out['sta_named_nets'] = [n for n in (inst_out_net(net, i) for i in insts) if n and n.startswith('\\')][:12]
        if sp:
            out['sta_start'] = flop_nets(net, sp.group(1))[1] or sp.group(1)
        if ep:
            out['sta_end'] = flop_nets(net, ep.group(1))[0] or ep.group(1)
    if r.returncode:
        out['sta_error'] = (r.stderr or r.stdout)[-400:]
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--top', required=True)
    ap.add_argument('--filelist', required=True, help='repo-relative .f (nested -f and $REPO_ROOT resolved)')
    ap.add_argument('--corner', default='TT', choices=sorted(LIB))
    ap.add_argument('--period-ps', type=int, default=1000, help="ABC's delay target and the STA clock")
    ap.add_argument('--clock', default='aclk', help='clock port for the STA check')
    ap.add_argument('--param', '-G', action='append', default=[], help='NAME=VALUE top parameter')
    ap.add_argument('--sta', action='store_true', help='run the OpenSTA register-to-register check too')
    ap.add_argument('--tag', default='', help='free label carried into the JSON row')
    ap.add_argument('--keep-nets', action='append', default=[], metavar='GLOB',
                    help="mark matching RTL wires keep=1 (e.g. '*_arb_*') so they survive synth and"
                         ' name the STA path; attribution runs only -- it perturbs the mapping a little')
    ap.add_argument('--keep-names', action='store_true',
                    help='keep RTL net names in the netlist (opt_clean without -purge) so the STA path names signals')
    ap.add_argument('--json', help='append the row to this JSON list file')
    ap.add_argument('--workdir', help='default /tmp/charwork/asap7/modules/<top>[_<tag>]')
    args = ap.parse_args()

    if not LIB[args.corner].exists():
        sys.exit(f'Liberty not found: {LIB[args.corner]}')
    work = Path(args.workdir) if args.workdir else \
        Path('/tmp/charwork/asap7/modules') / (args.top + (f'_{args.tag}' if args.tag else ''))
    work.mkdir(parents=True, exist_ok=True)
    sources, incdirs = get_sources_from_filelist(str(REPO_ROOT), filelist_path=args.filelist)
    ys = write_scripts(args, work, sources, incdirs)
    print(f'[synth] {args.top} ({args.corner}, {args.period_ps} ps): {len(sources)} sources -> {work}',
          file=sys.stderr, flush=True)
    t0 = time.time()
    log = work / 'yosys.log'
    r = subprocess.run(['yosys', '-ql', str(log), str(ys)], capture_output=True, text=True,
                       cwd=work, timeout=3600)
    row = {'top': args.top, 'tag': args.tag, 'corner': args.corner, 'period_ps': args.period_ps,
           'filelist': args.filelist, 'yosys_s': round(time.time() - t0, 1)}
    if r.returncode:
        row['status'] = 'FAIL'
        row['error'] = (r.stderr[-600:] or log.read_text()[-600:])
        print(json.dumps(row, indent=1))
        return 1
    text = log.read_text()
    d, lev = None, None
    for line in text.splitlines():
        m = ABC_DELAY_RE.search(line)
        if m:
            d = float(m.group(1))
        m = ABC_LEV_RE.search(line)
        if m:
            lev = int(m.group(1))
    row.update(status='OK', abc_delay_ps=d, abc_levels=lev, **parse_stat((work / 'stat.txt').read_text()))
    if args.sta:
        row.update(run_sta(args, work))
    if args.json:
        p = Path(args.json)
        rows = json.loads(p.read_text()) if p.exists() else []
        rows.append(row)
        p.write_text(json.dumps(rows, indent=1))
    print(json.dumps(row))
    return 0


if __name__ == '__main__':
    sys.exit(main())
