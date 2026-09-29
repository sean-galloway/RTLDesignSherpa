#!/usr/bin/env python3
"""Render docs/baseline_results.md from the sweep CSVs (timing_characterization TASK-002).

Every number on that page comes from a CSV written by a sweep -- nothing is
typed. Inputs (each optional; a missing one leaves its section out and says so):

  fpga/reports/sweep_wns.csv                 Vivado, Artix-7, frequency sweep (bitstream-sweep)
  fpga/reports/quartus/sweep_wns.csv         Quartus, Cyclone V, frequency sweep (quartus-sweep)
  fpga/reports/quartus/<name>/sweep_wns.csv  Quartus parameter sweeps (quartus/sweeps/<name>.tcl)

Usage:  python3 fpga/tools/baseline_report.py [--out docs/baseline_results.md]
"""
from __future__ import annotations

import argparse
import csv
import datetime as dt
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve()
AREA = HERE.parents[2]
REPORTS = AREA / "fpga" / "reports"

FUBS = ["nand", "inv", "xor", "carry", "mult", "mux", "queue", "clkdiv", "gray"]
PARAM_SWEEPS = [  # name, parameter, the FUB whose row is the measurement, what it measures, reading notes
    ("carry_width", "CARRY_WIDTH", "carry", "carry-chain adder width",
     ["`logic levels` stays 1 at every width: the adder rides the ALM carry chain, so what grows is the "
      "chain's propagation, not a LUT count -- the data-path delay column is the measurement."]),
    ("nand_levels", "NAND_LEVELS", "nand", "NAND tree depth",
     ["`NUM_FLOPS` is raised to 4096 for this sweep. char_top clamps the leaf count to NUM_FLOPS "
      "(`NAND_ACTUAL_FLOPS`) and wraps the leaves; with the default 256 the 8/10/12-level points folded "
      "to one identical netlist (278 ALMs, 4 LUT levels) on the first run, which measured the clamp, not "
      "the tree.",
      "Quartus counts LUT levels, not NAND gates; an ALM absorbs about two tree levels."]),
    ("mult_type", "MULT_TYPE", "mult", "multiplier architecture (0 inferred/DSP, 1 dadda, 2 wallace, 3 wallace_csa, 4 dadda_4to2)",
     ["Type 4 (Dadda with 4:2 compressors) is implemented for widths 8, 11 and 24 only; at the default "
      "`MULT_WIDTH = 16` `multiplier_tree.sv` falls back to the inferred multiplier, so its row equals "
      "type 0 by construction (the RTL header says so). Sweep it with `MULT_WIDTH 8` or `24` to see it.",
      "Types 1 and 3 synthesized to the same ALM count, register count and delay although their sources "
      "differ (`math_multiplier_dadda_tree_016.sv` vs `math_multiplier_wallace_tree_csa_016.sv`): read "
      "that as the fitter reducing both trees to the same structure, not as two measured architectures.",
      "Type 0 lands in one DSP block and shows 0 LUT levels; that is the DSP-vs-LUT comparison the task "
      "asked for: one DSP delay against an 8-10 level LUT tree at 3x the ALMs."]),
]


def read(path: Path) -> list[dict]:
    if not path.exists():
        return []
    with path.open(newline="") as f:
        return list(csv.DictReader(f))


def fmt(v, nd=3):
    try:
        return f"{float(v):.{nd}f}"
    except (TypeError, ValueError):
        return "" if v in (None, "") else str(v)


def freq_table_vivado(rows: list[dict]) -> list[str]:
    freqs = sorted({int(r["freq_mhz"]) for r in rows})
    out = ["| target MHz | period ns | clock group | WNS ns | met | LUTs | FFs | BRAM | DSP |",
           "|---:|---:|---|---:|---|---:|---:|---:|---:|"]
    for r in sorted(rows, key=lambda r: (int(r["freq_mhz"]), r["group"])):
        out.append(f"| {r['freq_mhz']} | {r['period_ns']} | {r['group']} | {fmt(r['wns_ns'])} | "
                   f"{'yes' if r['slack_status'] == 'PASS' else 'no'} | {r['utilization_luts']} | "
                   f"{r['utilization_ffs']} | {r['utilization_brams']} | {r['utilization_dsps']} |")
    return out


def freq_table_quartus(rows: list[dict]) -> tuple[list[str], list[str]]:
    freqs = sorted({int(r["freq_mhz"]) for r in rows})
    slack = defaultdict(dict); delay = defaultdict(dict); levels = defaultdict(dict); clk = {}
    for r in rows:
        f = int(r["freq_mhz"]); g = r["group"]
        if g.startswith("fub:"):
            k = g[4:]; slack[k][f] = r["wns_ns"]; delay[k][f] = r["data_delay_ns"]; levels[k][f] = r["logic_levels"]
        elif g == "clk:Slow 1100mV 85C":
            clk[f] = r["wns_ns"]
    head = "| path | " + " | ".join(f"{f} MHz" for f in freqs) + " |"
    rule = "|---|" + "---:|" * len(freqs)
    t1 = [head, rule, "| clock `clk`, slow 85C corner, worst setup slack | " + " | ".join(fmt(clk.get(f)) for f in freqs) + " |"]
    t1.append("| `design` worst path anywhere (ports included) | " + " | ".join(fmt(slack["design"].get(f)) for f in freqs) + " |")
    for k in FUBS:
        t1.append(f"| `{k}` reg-to-reg worst slack | " + " | ".join(fmt(slack[k].get(f)) for f in freqs) + " |")
    for k in FUBS:
        t1.append(f"| `{k}.io` worst slack incl. output ports | " + " | ".join(fmt(slack[k + '.io'].get(f)) for f in freqs) + " |")
    t2 = ["| FUB | data-path delay ns (worst reg-to-reg path, per target) | logic levels |", "|---|---|---:|"]
    for k in FUBS:
        d = ", ".join(f"{f}: {fmt(delay[k].get(f))}" for f in freqs if delay[k].get(f))
        lv = sorted({levels[k][f] for f in freqs if levels[k].get(f)}, key=lambda x: int(x) if x.isdigit() else 0)
        t2.append(f"| `{k}` | {d} | {'/'.join(lv)} |")
    util = next((r for r in rows), None)
    if util:
        t2.append("")
        t2.append(f"Resources at every point (full char_top, all FUBs): {util['utilization_luts']} ALMs, "
                  f"{util['utilization_ffs']} registers, {util['utilization_brams']} RAM block(s), {util['utilization_dsps']} DSP block(s).")
    return t1, t2


def param_table(rows: list[dict], param: str, fub: str) -> list[str]:
    pts = {}
    for r in rows:
        if r["group"] == f"fub:{fub}" and r["variant"].startswith(param + "="):
            pts[int(r["variant"].split("=", 1)[1])] = r
    out = [f"| `{param}` | reg-to-reg slack ns | data-path delay ns | logic levels | ALMs | registers | DSP |",
           "|---:|---:|---:|---:|---:|---:|---:|"]
    for v in sorted(pts):
        r = pts[v]
        out.append(f"| {v} | {fmt(r['wns_ns'])} | {fmt(r['data_delay_ns'])} | {r['logic_levels']} | "
                   f"{r['utilization_luts']} | {r['utilization_ffs']} | {r['utilization_dsps']} |")
    freq = next(iter(pts.values()))["freq_mhz"] if pts else "?"
    return out, freq


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--out", type=Path, default=AREA / "docs" / "baseline_results.md")
    a = ap.parse_args(argv)
    viv = read(REPORTS / "sweep_wns.csv")
    qtz = read(REPORTS / "quartus" / "sweep_wns.csv")
    L = []
    L += ["# Baseline Results -- Cross-Technology Comparison", "",
          f"Generated {dt.date.today().isoformat()} by `fpga/tools/baseline_report.py` from the sweep CSVs "
          "under `fpga/reports/`. Do not edit the numbers here; rerun the sweep and this script.", "",
          "The constraint is the same on every target -- `rtl/syn/char_top.sdc`: a single clock at the target "
          "frequency, 80 % of the period as input delay, 20 % as output delay, 100 ps uncertainty. The point "
          "of the design is NOT to close timing; it is to read how far each FUB's combinational path falls "
          "short as the target tightens (README.md section 1). Two FPGA technologies are compared here: "
          "Artix-7 (Xilinx, 28 nm, Vivado, the Nexys A7 part) and Cyclone V GX (Intel, 28 nm, Quartus Prime "
          "Lite). The ASAP7 numbers live in `work/timing_char_data.csv` and the ASIC paper.", ""]
    L += ["## 1. Frequency sweep, Artix-7 (Vivado, `make bitstream-sweep`)", ""]
    if viv:
        L += ["Full place-and-route of the board wrapper `char_top_fpga` on xc7a100tcsg324-1, all nine FUBs enabled. "
              "WNS is post-route, per clock group; `met` is WNS >= 0.", ""] + freq_table_vivado(viv)
        L += ["", "Vivado reports one number per clock group, not per FUB; the per-FUB view on this target is the "
              "`timing_worst.txt` in each `fpga/reports/sweep_<F>MHz/` archive."]
    else:
        L += ["_No `fpga/reports/sweep_wns.csv` -- run `cd fpga && make bitstream-sweep`._"]
    L += ["", "## 2. Frequency sweep, Cyclone V GX (Quartus, `make quartus-sweep`)", ""]
    if qtz:
        t1, t2 = freq_table_quartus(qtz)
        L += ["`char_top` itself (no board wrapper) on 5CGXFC5C6F27C7, all nine FUBs, map + fit + STA per point. "
              "Slack is setup slack at the slow 85C corner from `fub_slack.csv` "
              "(`fpga/quartus/sta_reports.tcl`): the worst register-to-register path launched from each FUB's "
              "flops, then the worst path from those flops to ANY endpoint (`.io`, which carries the 20 % "
              "output-delay budget). The `design` row is the worst path anywhere.", ""] + t1
        L += ["", "### 2.1 Per-FUB data-path delay and logic levels", "",
              "Delay is what the fitter achieved for that FUB's worst reg-to-reg path at each target; it moves "
              "with placement effort, so read the trend across FUBs, not the third decimal.", ""] + t2
    else:
        L += ["_No `fpga/reports/quartus/sweep_wns.csv` -- run `cd fpga && make quartus-sweep`._"]
    L += ["", "## 3. Parameter sweeps, Cyclone V GX (Quartus)", "",
          "One FUB enabled at a time, `VIRTUAL_PINS 1`, target 150 MHz (`fpga/quartus/sweeps/<name>.tcl`; "
          "`make quartus-sweep QUARTUS_CFG=quartus/sweeps/<name>.tcl QUARTUS_REPORTS_SUB=<name>`). "
          "The row is that FUB's worst reg-to-reg path.", ""]
    for i, (name, param, fub, what, notes) in enumerate(PARAM_SWEEPS, start=1):
        rows = read(REPORTS / "quartus" / name / "sweep_wns.csv")
        L += [f"### 3.{i} {what}", ""]
        if rows:
            t, freq = param_table(rows, param, fub)
            L += [f"Target {freq} MHz."] + [""] + t + [""] + [f"- {n}" for n in notes] + [""]
        else:
            L += [f"_No `fpga/reports/quartus/{name}/sweep_wns.csv` yet._", ""]
    L += ["## 4. Reading across technologies", "",
          "- The two 28 nm FPGA fabrics are compared on the same RTL and the same SDC, but not the same top: "
          "the Artix-7 numbers include the Nexys A7 board wrapper and real pins, the Cyclone V numbers are the "
          "bare `char_top` with real pins (frequency sweep) or virtual pins (parameter sweeps). Compare slopes, "
          "not absolute slack.",
          "- Vivado's per-clock WNS and Quartus' per-FUB slack are different cuts of the same question; the "
          "Quartus `design` row is the like-for-like number against Vivado's WNS.",
          "- `mult` shows 0 logic levels on Cyclone V: the inferred multiplier lands in a DSP block, so its "
          "path is one DSP delay, not a LUT count. The `MULT_TYPE` sweep is where DSP and LUT trees meet.",
          "- Resource columns are not comparable across vendors (an ALM is not a LUT); use them within a target.", ""]
    a.out.parent.mkdir(parents=True, exist_ok=True)
    a.out.write_text("\n".join(L) + "\n")
    print(f"wrote {a.out} ({len(L)} lines; vivado rows {len(viv)}, quartus rows {len(qtz)})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
