#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: unified_coverage_report
# Purpose: Generate a unified cross-component coverage summary by aggregating
#          data from ALL components in the repository.
#
# Author: sean galloway
# Created: 2025-01-20

"""
Unified Cross-Component Coverage Report Generator

Scans all component coverage data directories, aggregates Verilator
line/branch/toggle coverage and protocol coverage from merged JSON
summaries, and produces a unified report across the entire repository.

Supported output formats:
    - Markdown report (default or --output)
    - JSON for CI integration (--json)
    - Console summary (always printed)

Coverage thresholds (per coverage type):
    - Line:     95%
    - Branch:   90%
    - Toggle:   85%
    - Protocol: 80%

Usage:
    python bin/cov_utils/unified_coverage_report.py
    python bin/cov_utils/unified_coverage_report.py --output coverage_summary.md
    python bin/cov_utils/unified_coverage_report.py --json coverage_summary.json
    python bin/cov_utils/unified_coverage_report.py --output report.md --json report.json

Exit codes:
    0 - All components pass all coverage thresholds
    1 - One or more components fail a threshold
"""

import argparse
import glob
import json
import os
import subprocess
import sys
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Tuple

# ---------------------------------------------------------------------------
# Ensure the bin/ directory is on sys.path so sibling package imports work
# when this script is invoked directly.
# ---------------------------------------------------------------------------
_SCRIPT_DIR = Path(__file__).resolve().parent
_BIN_DIR = _SCRIPT_DIR.parent
if str(_BIN_DIR) not in sys.path:
    sys.path.insert(0, str(_BIN_DIR))

from cov_utils.verilator_coverage import (
    CoverageStats,
    find_coverage_files,
    parse_verilator_coverage_file,
)

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

# Coverage thresholds (percentage)
THRESHOLD_LINE = 95.0
THRESHOLD_BRANCH = 90.0
THRESHOLD_TOGGLE = 85.0
THRESHOLD_PROTOCOL = 80.0

# Status labels
STATUS_PASS = "PASS"
STATUS_WARN = "WARN"
STATUS_FAIL = "FAIL"


def _get_repo_root() -> Path:
    """Return the repository root directory.

    Tries ``git rev-parse`` first, then walks upward looking for a ``.git``
    directory as a fallback.
    """
    try:
        result = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            capture_output=True,
            text=True,
            timeout=5,
        )
        if result.returncode == 0:
            return Path(result.stdout.strip())
    except Exception:
        pass

    # Fallback: walk from this file upward
    current = _SCRIPT_DIR
    while current != current.parent:
        if (current / ".git").exists():
            return current
        current = current.parent

    # Last resort
    return _SCRIPT_DIR.parent.parent


# ---------------------------------------------------------------------------
# Data classes
# ---------------------------------------------------------------------------

@dataclass
class ComponentCoverage:
    """Aggregated coverage data for a single component."""

    name: str
    line_covered: int = 0
    line_total: int = 0
    branch_covered: int = 0
    branch_total: int = 0
    toggle_covered: int = 0
    toggle_total: int = 0
    protocol_covered: int = 0
    protocol_total: int = 0
    test_count: int = 0
    has_data: bool = False

    # Per-test details (optional, populated when available)
    tests: List[Dict] = field(default_factory=list)

    @property
    def line_pct(self) -> float:
        return (self.line_covered / self.line_total * 100) if self.line_total > 0 else 0.0

    @property
    def branch_pct(self) -> float:
        return (self.branch_covered / self.branch_total * 100) if self.branch_total > 0 else 0.0

    @property
    def toggle_pct(self) -> float:
        return (self.toggle_covered / self.toggle_total * 100) if self.toggle_total > 0 else 0.0

    @property
    def protocol_pct(self) -> float:
        return (self.protocol_covered / self.protocol_total * 100) if self.protocol_total > 0 else 0.0

    def status_for(self, metric: str) -> str:
        """Return PASS / WARN / FAIL for a given metric."""
        thresholds = {
            "line": THRESHOLD_LINE,
            "branch": THRESHOLD_BRANCH,
            "toggle": THRESHOLD_TOGGLE,
            "protocol": THRESHOLD_PROTOCOL,
        }
        pct_map = {
            "line": self.line_pct,
            "branch": self.branch_pct,
            "toggle": self.toggle_pct,
            "protocol": self.protocol_pct,
        }
        threshold = thresholds.get(metric, 80.0)
        pct = pct_map.get(metric, 0.0)
        total_map = {
            "line": self.line_total,
            "branch": self.branch_total,
            "toggle": self.toggle_total,
            "protocol": self.protocol_total,
        }
        # If there is no data at all for the metric, report N/A-style WARN
        if total_map.get(metric, 0) == 0:
            return STATUS_WARN
        if pct >= threshold:
            return STATUS_PASS
        if pct >= threshold * 0.8:
            return STATUS_WARN
        return STATUS_FAIL

    @property
    def overall_pass(self) -> bool:
        """True when every metric with data meets its threshold."""
        for metric in ("line", "branch", "toggle", "protocol"):
            total_map = {
                "line": self.line_total,
                "branch": self.branch_total,
                "toggle": self.toggle_total,
                "protocol": self.protocol_total,
            }
            if total_map[metric] > 0 and self.status_for(metric) == STATUS_FAIL:
                return False
        return True

    def to_dict(self) -> Dict:
        """Serialize to a plain dictionary."""
        return {
            "name": self.name,
            "line": {
                "covered": self.line_covered,
                "total": self.line_total,
                "pct": round(self.line_pct, 2),
                "status": self.status_for("line"),
            },
            "branch": {
                "covered": self.branch_covered,
                "total": self.branch_total,
                "pct": round(self.branch_pct, 2),
                "status": self.status_for("branch"),
            },
            "toggle": {
                "covered": self.toggle_covered,
                "total": self.toggle_total,
                "pct": round(self.toggle_pct, 2),
                "status": self.status_for("toggle"),
            },
            "protocol": {
                "covered": self.protocol_covered,
                "total": self.protocol_total,
                "pct": round(self.protocol_pct, 2),
                "status": self.status_for("protocol"),
            },
            "test_count": self.test_count,
            "has_data": self.has_data,
            "overall_pass": self.overall_pass,
        }


# ---------------------------------------------------------------------------
# Component scan definitions
# ---------------------------------------------------------------------------

# Each entry: (human-readable name, base directory relative to repo root,
#              list of sub-paths to search for coverage data)
_COMPONENT_SCAN_DEFS: List[Tuple[str, str, List[str]]] = [
    (
        "stream",
        "projects/components/stream",
        [
            "dv/tests/coverage_data",
            "coverage_data",
        ],
    ),
    (
        "rapids",
        "projects/components/rapids",
        [
            "dv/tests/coverage_data",
        ],
    ),
    (
        "bridge",
        "projects/components/bridge",
        [
            "dv/tests/coverage_data",
        ],
    ),
    (
        "converters",
        "projects/components/converters",
        [
            "dv/tests/coverage_data",
        ],
    ),
    (
        "val/common",
        "val/common",
        [
            "coverage_data",
        ],
    ),
    (
        "val/amba",
        "val/amba",
        [
            "coverage_data",
        ],
    ),
]


# ---------------------------------------------------------------------------
# Data collection helpers
# ---------------------------------------------------------------------------

def _find_merged_json(base_dir: Path) -> Optional[Path]:
    """Locate the latest merged coverage JSON in *base_dir* and its sub-dirs.

    Looks for ``latest_merged_coverage.json`` first, then falls back to the
    most recently modified ``*.json`` under ``reports/``.
    """
    candidates = [
        base_dir / "reports" / "latest_merged_coverage.json",
        base_dir / "latest_merged_coverage.json",
    ]
    for candidate in candidates:
        if candidate.is_file():
            return candidate

    # Fallback: search for any JSON report
    reports_dir = base_dir / "reports"
    if reports_dir.is_dir():
        json_files = sorted(reports_dir.glob("*.json"), key=os.path.getmtime, reverse=True)
        if json_files:
            return json_files[0]

    return None


def _find_merged_dat(base_dir: Path) -> Optional[Path]:
    """Locate the latest merged Verilator .dat file."""
    candidates = [
        base_dir / "merged" / "latest_merged_coverage.dat",
        base_dir / "latest_merged_coverage.dat",
    ]
    for candidate in candidates:
        if candidate.is_file():
            return candidate

    # Fallback: most recent .dat in merged/
    merged_dir = base_dir / "merged"
    if merged_dir.is_dir():
        dat_files = sorted(
            [f for f in merged_dir.glob("*.dat") if "verFiles" not in f.name],
            key=os.path.getmtime,
            reverse=True,
        )
        if dat_files:
            return dat_files[0]

    return None


def _find_per_test_summaries(base_dir: Path) -> List[Path]:
    """Return all per-test *_summary.json files."""
    per_test_dir = base_dir / "per_test"
    if per_test_dir.is_dir():
        return sorted(per_test_dir.glob("*_summary.json"))
    return []


def _count_tests_from_dat(base_dir: Path) -> int:
    """Count distinct test .dat files (a proxy for test count)."""
    per_test_dir = base_dir / "per_test"
    if per_test_dir.is_dir():
        return len(list(per_test_dir.glob("*.dat")))

    # Also check local_sim_build
    sim_build = base_dir.parent / "local_sim_build"
    if sim_build.is_dir():
        return len(list(sim_build.glob("test_*/coverage.dat")))

    return 0


def _aggregate_protocol_from_summaries(summaries: List[Path]) -> Tuple[int, int]:
    """Walk per-test summary JSONs and aggregate protocol coverage points.

    Returns (total_covered, total_points) across all groups and tests,
    de-duplicated by point name within each group.
    """
    # group_name -> point_name -> max hits
    group_points: Dict[str, Dict[str, int]] = {}
    # group_name -> point_name -> goal
    group_goals: Dict[str, Dict[str, int]] = {}

    for summary_path in summaries:
        try:
            with open(summary_path, "r") as fh:
                data = json.load(fh)
        except (json.JSONDecodeError, OSError):
            continue

        protocol = data.get("protocol_coverage", {})
        groups = protocol.get("groups", {})
        for group_name, group_data in groups.items():
            if group_name not in group_points:
                group_points[group_name] = {}
                group_goals[group_name] = {}
            for point_name, point_data in group_data.get("points", {}).items():
                hits = point_data.get("hits", 0)
                goal = point_data.get("goal", 1)
                # Keep the maximum hit count across tests (merge)
                prev = group_points[group_name].get(point_name, 0)
                group_points[group_name][point_name] = max(prev, hits)
                group_goals[group_name][point_name] = goal

    total = 0
    covered = 0
    for group_name, points in group_points.items():
        for point_name, max_hits in points.items():
            goal = group_goals[group_name].get(point_name, 1)
            total += 1
            if max_hits >= goal:
                covered += 1

    return covered, total


def collect_component(repo_root: Path, name: str, base_rel: str,
                      search_paths: List[str]) -> ComponentCoverage:
    """Collect coverage data for a single component.

    Searches each path under *base_rel* for merged JSON, merged .dat, and
    per-test summaries.
    """
    comp = ComponentCoverage(name=name)
    component_base = repo_root / base_rel

    if not component_base.is_dir():
        return comp

    for sub in search_paths:
        cov_dir = component_base / sub
        if not cov_dir.is_dir():
            continue

        # ----- Merged JSON (has overall line/toggle/branch + test count) ----
        merged_json_path = _find_merged_json(cov_dir)
        if merged_json_path is not None:
            try:
                with open(merged_json_path, "r") as fh:
                    jdata = json.load(fh)
            except (json.JSONDecodeError, OSError):
                jdata = {}

            code_cov = jdata.get("code_coverage", {})

            line_info = code_cov.get("line", {})
            if line_info.get("total", 0) > comp.line_total:
                comp.line_covered = line_info.get("covered", 0)
                comp.line_total = line_info.get("total", 0)

            branch_info = code_cov.get("branch", {})
            if branch_info.get("total", 0) > comp.branch_total:
                comp.branch_covered = branch_info.get("covered", 0)
                comp.branch_total = branch_info.get("total", 0)

            toggle_info = code_cov.get("toggle", {})
            if toggle_info.get("total", 0) > comp.toggle_total:
                comp.toggle_covered = toggle_info.get("covered", 0)
                comp.toggle_total = toggle_info.get("total", 0)

            if jdata.get("test_count", 0) > comp.test_count:
                comp.test_count = jdata["test_count"]

            comp.tests.extend(jdata.get("tests", []))

            # Protocol from merged JSON overall
            protocol_groups = jdata.get("protocol_groups", {})
            p_covered = 0
            p_total = 0
            for _gname, gdata in protocol_groups.items():
                p_covered += gdata.get("covered", 0)
                p_total += gdata.get("total", 0)
            if p_total > comp.protocol_total:
                comp.protocol_covered = p_covered
                comp.protocol_total = p_total

            comp.has_data = True

        # ----- Merged .dat (Verilator coverage when no JSON available) ------
        if comp.line_total == 0:
            merged_dat = _find_merged_dat(cov_dir)
            if merged_dat is not None:
                stats = parse_verilator_coverage_file(str(merged_dat))
                comp.line_covered = stats.line_covered
                comp.line_total = stats.line_total
                comp.branch_covered = stats.branch_covered
                comp.branch_total = stats.branch_total
                comp.toggle_covered = stats.toggle_covered
                comp.toggle_total = stats.toggle_total
                comp.has_data = True

        # ----- Per-test protocol summaries (when merged JSON lacks them) ----
        if comp.protocol_total == 0:
            summaries = _find_per_test_summaries(cov_dir)
            if summaries:
                p_cov, p_tot = _aggregate_protocol_from_summaries(summaries)
                if p_tot > 0:
                    comp.protocol_covered = p_cov
                    comp.protocol_total = p_tot
                    comp.has_data = True

        # ----- Test count fallback ------------------------------------------
        if comp.test_count == 0:
            cnt = _count_tests_from_dat(cov_dir)
            if cnt > comp.test_count:
                comp.test_count = cnt

    return comp


# ---------------------------------------------------------------------------
# Report generation
# ---------------------------------------------------------------------------

def _fmt_pct(pct: float) -> str:
    """Format a percentage for display."""
    return f"{pct:.1f}%"


def _compute_health(components: List[ComponentCoverage]) -> str:
    """Compute an overall repository health rating.

    Returns one of: EXCELLENT, GOOD, FAIR, POOR, CRITICAL.
    """
    if not components:
        return "CRITICAL"

    active = [c for c in components if c.has_data]
    if not active:
        return "CRITICAL"

    total = len(active)
    passing = sum(1 for c in active if c.overall_pass)
    ratio = passing / total

    if ratio >= 1.0:
        return "EXCELLENT"
    if ratio >= 0.8:
        return "GOOD"
    if ratio >= 0.6:
        return "FAIR"
    if ratio >= 0.4:
        return "POOR"
    return "CRITICAL"


def generate_markdown(components: List[ComponentCoverage]) -> str:
    """Produce a Markdown coverage summary report."""
    lines: List[str] = []
    now_str = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    health = _compute_health(components)

    # Header
    lines.append("# Unified Coverage Report")
    lines.append("")
    lines.append(f"**Generated:** {now_str}")
    lines.append(f"**Repository Health:** {health}")
    lines.append("")

    # Thresholds reference
    lines.append("## Coverage Thresholds")
    lines.append("")
    lines.append("| Metric | Target |")
    lines.append("|--------|--------|")
    lines.append(f"| Line | {_fmt_pct(THRESHOLD_LINE)} |")
    lines.append(f"| Branch | {_fmt_pct(THRESHOLD_BRANCH)} |")
    lines.append(f"| Toggle | {_fmt_pct(THRESHOLD_TOGGLE)} |")
    lines.append(f"| Protocol | {_fmt_pct(THRESHOLD_PROTOCOL)} |")
    lines.append("")

    # Executive summary table
    lines.append("## Executive Summary")
    lines.append("")
    lines.append(
        "| Component | Line% | Branch% | Toggle% | Protocol% | Tests | Status |"
    )
    lines.append(
        "|-----------|------:|--------:|--------:|----------:|------:|--------|"
    )

    for comp in components:
        if not comp.has_data:
            lines.append(
                f"| {comp.name} | -- | -- | -- | -- | 0 | NO DATA |"
            )
            continue

        def _cell(pct: float, total: int, metric: str) -> str:
            if total == 0:
                return "--"
            status = comp.status_for(metric)
            return f"{_fmt_pct(pct)} {status}"

        overall = STATUS_PASS if comp.overall_pass else STATUS_FAIL
        lines.append(
            f"| {comp.name} "
            f"| {_cell(comp.line_pct, comp.line_total, 'line')} "
            f"| {_cell(comp.branch_pct, comp.branch_total, 'branch')} "
            f"| {_cell(comp.toggle_pct, comp.toggle_total, 'toggle')} "
            f"| {_cell(comp.protocol_pct, comp.protocol_total, 'protocol')} "
            f"| {comp.test_count} "
            f"| {overall} |"
        )

    lines.append("")

    # Aggregate totals
    lines.append("## Aggregate Totals")
    lines.append("")
    agg_line_c = sum(c.line_covered for c in components)
    agg_line_t = sum(c.line_total for c in components)
    agg_branch_c = sum(c.branch_covered for c in components)
    agg_branch_t = sum(c.branch_total for c in components)
    agg_toggle_c = sum(c.toggle_covered for c in components)
    agg_toggle_t = sum(c.toggle_total for c in components)
    agg_proto_c = sum(c.protocol_covered for c in components)
    agg_proto_t = sum(c.protocol_total for c in components)
    agg_tests = sum(c.test_count for c in components)

    def _agg_pct(covered: int, total: int) -> str:
        if total == 0:
            return "--"
        return _fmt_pct(covered / total * 100)

    lines.append("| Metric | Covered | Total | Percentage |")
    lines.append("|--------|--------:|------:|-----------:|")
    lines.append(f"| Line | {agg_line_c} | {agg_line_t} | {_agg_pct(agg_line_c, agg_line_t)} |")
    lines.append(f"| Branch | {agg_branch_c} | {agg_branch_t} | {_agg_pct(agg_branch_c, agg_branch_t)} |")
    lines.append(f"| Toggle | {agg_toggle_c} | {agg_toggle_t} | {_agg_pct(agg_toggle_c, agg_toggle_t)} |")
    lines.append(f"| Protocol | {agg_proto_c} | {agg_proto_t} | {_agg_pct(agg_proto_c, agg_proto_t)} |")
    lines.append(f"| **Total Tests** | | | **{agg_tests}** |")
    lines.append("")

    # Coverage gaps
    gaps: List[Tuple[str, str, float, float]] = []
    for comp in components:
        if not comp.has_data:
            continue
        for metric, threshold in [
            ("line", THRESHOLD_LINE),
            ("branch", THRESHOLD_BRANCH),
            ("toggle", THRESHOLD_TOGGLE),
            ("protocol", THRESHOLD_PROTOCOL),
        ]:
            pct_map = {
                "line": comp.line_pct,
                "branch": comp.branch_pct,
                "toggle": comp.toggle_pct,
                "protocol": comp.protocol_pct,
            }
            total_map = {
                "line": comp.line_total,
                "branch": comp.branch_total,
                "toggle": comp.toggle_total,
                "protocol": comp.protocol_total,
            }
            if total_map[metric] > 0 and pct_map[metric] < threshold:
                gaps.append((comp.name, metric, pct_map[metric], threshold))

    if gaps:
        lines.append("## Coverage Gaps")
        lines.append("")
        lines.append(f"**{len(gaps)} gap(s) detected:**")
        lines.append("")
        lines.append("| Component | Metric | Current | Target | Deficit |")
        lines.append("|-----------|--------|--------:|-------:|--------:|")
        for comp_name, metric, current, target in sorted(gaps, key=lambda g: g[2]):
            deficit = target - current
            lines.append(
                f"| {comp_name} | {metric} | {_fmt_pct(current)} | {_fmt_pct(target)} | {_fmt_pct(deficit)} |"
            )
        lines.append("")
    else:
        lines.append("## Coverage Gaps")
        lines.append("")
        lines.append("No coverage gaps detected. All metrics meet their targets.")
        lines.append("")

    # Components with no data
    no_data = [c for c in components if not c.has_data]
    if no_data:
        lines.append("## Components Without Coverage Data")
        lines.append("")
        for comp in no_data:
            lines.append(f"- **{comp.name}**: No coverage data found")
        lines.append("")

    # Recommendations
    lines.append("## Recommendations")
    lines.append("")

    recs: List[str] = []

    if no_data:
        recs.append(
            "Enable coverage collection (COVERAGE=1) for components without data: "
            + ", ".join(c.name for c in no_data)
            + "."
        )

    # Specific metric recommendations
    line_gaps = [g for g in gaps if g[1] == "line"]
    branch_gaps = [g for g in gaps if g[1] == "branch"]
    toggle_gaps = [g for g in gaps if g[1] == "toggle"]
    protocol_gaps = [g for g in gaps if g[1] == "protocol"]

    if line_gaps:
        names = ", ".join(g[0] for g in line_gaps)
        recs.append(
            f"Improve line coverage for: {names}. "
            f"Add tests targeting uncovered code paths."
        )
    if branch_gaps:
        names = ", ".join(g[0] for g in branch_gaps)
        recs.append(
            f"Improve branch coverage for: {names}. "
            f"Add tests for untaken if/else and case branches."
        )
    if toggle_gaps:
        names = ", ".join(g[0] for g in toggle_gaps)
        recs.append(
            f"Improve toggle coverage for: {names}. "
            f"Ensure test stimulus exercises all signal transitions (0->1, 1->0)."
        )
    if protocol_gaps:
        names = ", ".join(g[0] for g in protocol_gaps)
        recs.append(
            f"Improve protocol coverage for: {names}. "
            f"Add test scenarios covering additional AXI/APB/AXIS transaction types."
        )

    if not recs:
        recs.append("All components meet coverage targets. Continue maintaining coverage as new features are added.")

    for i, rec in enumerate(recs, 1):
        lines.append(f"{i}. {rec}")
    lines.append("")

    # Footer
    lines.append("---")
    lines.append("*Report generated by RTLDesignSherpa unified coverage infrastructure*")

    return "\n".join(lines)


def generate_json_report(components: List[ComponentCoverage]) -> Dict:
    """Produce a JSON-serializable coverage report dictionary."""
    health = _compute_health(components)
    all_pass = all(c.overall_pass for c in components if c.has_data)

    agg_line_c = sum(c.line_covered for c in components)
    agg_line_t = sum(c.line_total for c in components)
    agg_branch_c = sum(c.branch_covered for c in components)
    agg_branch_t = sum(c.branch_total for c in components)
    agg_toggle_c = sum(c.toggle_covered for c in components)
    agg_toggle_t = sum(c.toggle_total for c in components)
    agg_proto_c = sum(c.protocol_covered for c in components)
    agg_proto_t = sum(c.protocol_total for c in components)

    def _safe_pct(covered: int, total: int) -> float:
        return round(covered / total * 100, 2) if total > 0 else 0.0

    return {
        "generated": datetime.now().isoformat(),
        "health": health,
        "overall_pass": all_pass,
        "thresholds": {
            "line": THRESHOLD_LINE,
            "branch": THRESHOLD_BRANCH,
            "toggle": THRESHOLD_TOGGLE,
            "protocol": THRESHOLD_PROTOCOL,
        },
        "aggregate": {
            "line": {
                "covered": agg_line_c,
                "total": agg_line_t,
                "pct": _safe_pct(agg_line_c, agg_line_t),
            },
            "branch": {
                "covered": agg_branch_c,
                "total": agg_branch_t,
                "pct": _safe_pct(agg_branch_c, agg_branch_t),
            },
            "toggle": {
                "covered": agg_toggle_c,
                "total": agg_toggle_t,
                "pct": _safe_pct(agg_toggle_c, agg_toggle_t),
            },
            "protocol": {
                "covered": agg_proto_c,
                "total": agg_proto_t,
                "pct": _safe_pct(agg_proto_c, agg_proto_t),
            },
            "test_count": sum(c.test_count for c in components),
        },
        "components": [c.to_dict() for c in components],
    }


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Generate unified cross-component coverage summary.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "Examples:\n"
            "  python bin/cov_utils/unified_coverage_report.py\n"
            "  python bin/cov_utils/unified_coverage_report.py --output coverage_summary.md\n"
            "  python bin/cov_utils/unified_coverage_report.py --json coverage_summary.json\n"
        ),
    )
    parser.add_argument(
        "--output", "-o",
        metavar="FILE",
        help="Write Markdown report to FILE",
    )
    parser.add_argument(
        "--json",
        metavar="FILE",
        dest="json_output",
        help="Write JSON report to FILE (for CI integration)",
    )
    parser.add_argument(
        "--repo-root",
        metavar="DIR",
        help="Repository root directory (auto-detected if omitted)",
    )
    parser.add_argument(
        "--quiet", "-q",
        action="store_true",
        help="Suppress console summary output",
    )
    return parser


def main(argv: Optional[List[str]] = None) -> int:
    """Entry point. Returns 0 if all components pass, 1 otherwise."""
    parser = _build_parser()
    args = parser.parse_args(argv)

    repo_root = Path(args.repo_root) if args.repo_root else _get_repo_root()
    if not repo_root.is_dir():
        print(f"Error: Repository root not found: {repo_root}", file=sys.stderr)
        return 1

    # Collect coverage from every component
    components: List[ComponentCoverage] = []
    for name, base_rel, search_paths in _COMPONENT_SCAN_DEFS:
        comp = collect_component(repo_root, name, base_rel, search_paths)
        components.append(comp)

    # Generate Markdown
    md_report = generate_markdown(components)

    # Console output
    if not args.quiet:
        print(md_report)

    # Write Markdown to file
    if args.output:
        output_path = Path(args.output)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(md_report)
        print(f"\nMarkdown report written to: {output_path}", file=sys.stderr)

    # Write JSON to file
    if args.json_output:
        json_data = generate_json_report(components)
        json_path = Path(args.json_output)
        json_path.parent.mkdir(parents=True, exist_ok=True)
        json_path.write_text(json.dumps(json_data, indent=2))
        print(f"JSON report written to: {json_path}", file=sys.stderr)

    # Determine exit code
    active = [c for c in components if c.has_data]
    if not active:
        if not args.quiet:
            print("\nWarning: No coverage data found for any component.", file=sys.stderr)
        return 1

    all_pass = all(c.overall_pass for c in active)
    return 0 if all_pass else 1


if __name__ == "__main__":
    sys.exit(main())
