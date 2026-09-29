# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Teeth for fpga/tools/parse_timing_sweep.py.

The Quartus fixtures under fixtures/quartus_sweep_100MHz/ are the REAL files
the first sweep produced (char_top on 5CGXFC5C6F27C7, 100 MHz, Quartus Prime
Lite 24.1std, 2026-09-29) -- copied, not typed -- so the parser is pinned to
the format the tool actually writes. The Vivado fixture under
fixtures/artix7_axi4_master_rd_vivado/ (named so the root .gitignore rule `vivado*` does not swallow it) is likewise a REAL report_timing_summary
+ report_utilization pair (rtl/amba/fpga OOC run of axi4_master_rd on
xc7a100tcsg324-1). It is what exposed that the per-clock-group regex had
never matched a real report: the Intra Clock Table's third and fourth columns
are endpoint COUNTS, not delays.
"""
from __future__ import annotations

import csv
import shutil
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import parse_timing_sweep as pts  # noqa: E402

FIX = HERE / "fixtures" / "quartus_sweep_100MHz"


def test_quartus_summary_takes_setup_slack_per_model():
    rows = pts.parse_quartus_summary(FIX / "char_top.sta.summary")
    assert rows == [("Slow 1100mV 85C", -2.384), ("Slow 1100mV 0C", -2.39),
                    ("Fast 1100mV 85C", 0.11), ("Fast 1100mV 0C", 0.169)]


def test_quartus_fit_summary_resources():
    assert pts.parse_quartus_fit(FIX / "char_top.fit.summary") == {
        "luts": 746, "ffs": 1559, "brams": 1, "dsps": 1}


def test_fub_slack_rows_are_constraint_aware():
    rows = {r["fub"]: r for r in pts.parse_fub_slack(FIX / "fub_slack.csv")}
    # design worst == the sta.summary slow-corner setup slack
    assert float(rows["design"]["slack_ns"]) == -2.384
    # reg-to-reg rows are positive at 100 MHz; the .io rows carry the 20%
    # output-delay budget and are the ones that fail
    assert float(rows["nand"]["slack_ns"]) > 0 and float(rows["nand.io"]["slack_ns"]) < 0
    assert rows["nand"]["logic_levels"] == "4"
    assert len(rows) == 1 + 2 * 9


def test_quartus_end_to_end_csv(tmp_path):
    rep = tmp_path / "quartus"
    shutil.copytree(FIX, rep / "sweep_100MHz")
    out = tmp_path / "out.csv"
    assert pts.main(["--tool", "quartus", str(rep), str(out)]) == 0
    with out.open(newline="") as f:
        rows = list(csv.DictReader(f))
    assert rows[0].keys() >= {"freq_mhz", "group", "wns_ns", "data_delay_ns", "logic_levels"}
    groups = [r["group"] for r in rows]
    assert "clk:Slow 1100mV 85C" in groups and "fub:mult" in groups and "fub:mult.io" in groups
    assert all(r["freq_mhz"] == "100" and r["period_ns"] == "10.0" for r in rows)
    assert all(r["utilization_luts"] == "746" for r in rows)
    fail = [r for r in rows if r["slack_status"] == "FAIL"]
    assert {r["group"] for r in fail} >= {"fub:design", "fub:queue.io", "clk:Slow 1100mV 85C"}


def test_quartus_skips_dir_without_summary(tmp_path, capsys):
    (tmp_path / "sweep_150MHz").mkdir()
    assert pts.main(["--tool", "quartus", str(tmp_path), str(tmp_path / "o.csv")]) == 1
    assert "no *.sta.summary" in capsys.readouterr().err


VFIX = HERE / "fixtures" / "artix7_axi4_master_rd_vivado"


def test_vivado_real_report_groups_and_design_wns():
    design_wns, groups = pts.parse_timing(VFIX / "timing_summary.txt")
    assert design_wns == 1.895
    # the per-clock row, which the old three-floats regex never produced
    assert groups == [("aclk", 1.895)]
    assert pts.parse_util(VFIX / "utilization_impl.txt") == {"luts": 285, "ffs": 328, "brams": 0, "dsps": 0}


def test_vivado_end_to_end_csv(tmp_path):
    shutil.copytree(VFIX, tmp_path / "sweep_100MHz")
    out = tmp_path / "out.csv"
    assert pts.main([str(tmp_path), str(out)]) == 0
    with out.open(newline="") as f:
        rows = list(csv.DictReader(f))
    assert [(r["group"], r["wns_ns"], r["slack_status"]) for r in rows] == [("aclk", "1.895", "PASS")]
    assert rows[0]["utilization_luts"] == "285" and rows[0]["data_delay_ns"] == ""
