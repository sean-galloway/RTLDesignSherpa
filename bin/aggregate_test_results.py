#!/usr/bin/env python3
"""
Aggregate Test Results Across All Environments

Reads test environments from test_environments.toml (single source of truth),
runs each test area via its own Makefile (preserving correct cwd, conftest,
and environment), injects --junitxml via PYTEST_ADDOPTS, then collects and
displays all results in a rich table.

Usage:
    # Run all tests and display table (GATE level)
    python3 bin/aggregate_test_results.py --run

    # Run at a specific level
    python3 bin/aggregate_test_results.py --run --test-level FUNC

    # Run only specific areas
    python3 bin/aggregate_test_results.py --run --area rapids --area stream

    # Display cached results from a previous --run
    python3 bin/aggregate_test_results.py

    # Export as markdown
    python3 bin/aggregate_test_results.py --markdown results.md

    # List all test areas from TOML
    python3 bin/aggregate_test_results.py --list

Environment Variables:
    TEST_LEVEL  - Set test level: GATE, FUNC, FULL (default: GATE)
    REPO_ROOT   - Repository root (auto-detected if not set)
"""

import argparse
import os
import subprocess
import sys
import xml.etree.ElementTree as ET
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path

try:
    import tomllib
except ModuleNotFoundError:
    try:
        import tomli as tomllib  # type: ignore[no-redef]
    except ImportError:
        print("Error: Python 3.11+ (tomllib) or 'pip install tomli' required",
              file=sys.stderr)
        sys.exit(1)


@dataclass
class TestSuiteResult:
    """Results for a single test suite/environment."""
    name: str
    area: str
    passed: int = 0
    failed: int = 0
    errors: int = 0
    skipped: int = 0
    time_sec: float = 0.0
    xml_path: str = ""
    run_error: str = ""

    @property
    def total(self) -> int:
        return self.passed + self.failed + self.errors + self.skipped

    @property
    def success_rate(self) -> float:
        if self.total == 0:
            return 0.0
        return (self.passed / self.total) * 100

    @property
    def status(self) -> str:
        if self.run_error:
            return "RUN_ERROR"
        if self.total == 0:
            return "NO_TESTS"
        if self.failed > 0 or self.errors > 0:
            return "FAIL"
        return "PASS"


def find_repo_root() -> Path:
    """Find repository root via git or REPO_ROOT env var."""
    env_root = os.environ.get("REPO_ROOT")
    if env_root:
        return Path(env_root)
    try:
        result = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            capture_output=True, text=True, check=True
        )
        return Path(result.stdout.strip())
    except (subprocess.CalledProcessError, FileNotFoundError):
        return Path.cwd()


def load_test_areas(repo_root: Path) -> list[tuple[str, str, str, str]]:
    """Load test areas from test_environments.toml.

    Returns a list of (area, sub_area, test_dir, make_target_fmt) tuples,
    expanding sub_areas into individual entries for per-sub-area results.

    For environments with sub_areas: each sub-area gets its own entry with
    the test_dir pointing to the sub-directory.

    For environments without sub_areas: a single entry using the root
    directory.
    """
    toml_path = repo_root / "test_environments.toml"
    if not toml_path.exists():
        print(f"Error: {toml_path} not found", file=sys.stderr)
        sys.exit(1)

    with open(toml_path, "rb") as f:
        config = tomllib.load(f)

    defaults = config.get("defaults", {})
    envs = config.get("env", {})

    areas = []
    for env_name, env_cfg in envs.items():
        directory = env_cfg["directory"]
        make_target_fmt = env_cfg.get(
            "make_target", defaults.get("make_target", "run-all-{level}")
        )
        sub_areas = env_cfg.get("sub_areas")

        if sub_areas:
            for sub in sub_areas:
                sub_dir = f"{directory}/{sub}"
                areas.append((env_name, sub, sub_dir, make_target_fmt))
        else:
            areas.append((env_name, "", directory, make_target_fmt))

    return areas


def parse_junit_xml(xml_path: str) -> TestSuiteResult:
    """Parse a JUnit XML file and return aggregated results."""
    result = TestSuiteResult(name="", area="", xml_path=xml_path)

    try:
        tree = ET.parse(xml_path)
        root = tree.getroot()

        # Handle both <testsuites> and <testsuite> root elements
        if root.tag == "testsuites":
            suites = root.findall("testsuite")
        elif root.tag == "testsuite":
            suites = [root]
        else:
            result.run_error = f"Unknown XML root: {root.tag}"
            return result

        for suite in suites:
            tests = int(suite.get("tests", 0))
            failures = int(suite.get("failures", 0))
            errors = int(suite.get("errors", 0))
            skipped = int(suite.get("skipped", 0))
            time_val = float(suite.get("time", 0.0))

            result.failed += failures
            result.errors += errors
            result.skipped += skipped
            result.passed += tests - failures - errors - skipped
            result.time_sec += time_val

    except ET.ParseError as e:
        result.run_error = f"XML parse error: {e}"
    except FileNotFoundError:
        result.run_error = "XML file not found"

    return result


def run_tests_for_area(
    repo_root: Path, area: str, sub_area: str, test_dir: str,
    make_target_fmt: str, results_dir: Path, test_level: str,
    timeout: int
) -> TestSuiteResult:
    """Run tests via the area's own Makefile, injecting --junitxml."""
    full_test_dir = repo_root / test_dir
    result_name = f"{area}/{sub_area}" if sub_area else area
    result = TestSuiteResult(name=result_name, area=area)

    if not full_test_dir.exists():
        result.run_error = "Directory not found"
        return result

    makefile = full_test_dir / "Makefile"
    if not makefile.exists():
        result.run_error = "No Makefile"
        return result

    xml_filename = f"{area}_{sub_area}_results.xml" if sub_area else f"{area}_results.xml"
    xml_file = results_dir / xml_filename
    result.xml_path = str(xml_file)

    # Resolve the make target for this level
    level_lower = test_level.lower()
    make_target = make_target_fmt.format(level=level_lower)

    # Inject --junitxml via PYTEST_ADDOPTS so the existing Makefile pytest
    # invocations pick it up automatically.
    env = os.environ.copy()
    env["TEST_LEVEL"] = test_level
    existing_addopts = env.get("PYTEST_ADDOPTS", "")
    env["PYTEST_ADDOPTS"] = f"{existing_addopts} --junitxml={xml_file} --override-ini=junit_family=xunit2".strip()

    cmd = ["make", make_target]

    try:
        run_kwargs = dict(
            capture_output=True, text=True,
            cwd=str(full_test_dir), env=env
        )
        if timeout > 0:
            run_kwargs["timeout"] = timeout

        proc = subprocess.run(cmd, **run_kwargs)

        if xml_file.exists():
            parsed = parse_junit_xml(str(xml_file))
            result.passed = parsed.passed
            result.failed = parsed.failed
            result.errors = parsed.errors
            result.skipped = parsed.skipped
            result.time_sec = parsed.time_sec
        else:
            # make ran but no XML produced — check for make-level error
            result.run_error = "No XML output"
            if proc.returncode != 0:
                stderr_lines = (proc.stderr or proc.stdout or "").strip().split("\n")
                last_lines = [l for l in stderr_lines[-5:] if l.strip()]
                result.run_error = "; ".join(last_lines)[:120] or f"exit {proc.returncode}"

    except subprocess.TimeoutExpired:
        result.run_error = f"Timeout ({timeout}s)"
    except Exception as e:
        result.run_error = str(e)[:120]

    return result


def display_rich_table(results: list[TestSuiteResult], title: str = "Test Results"):
    """Display results using rich table."""
    from rich.console import Console
    from rich.table import Table
    from rich.text import Text

    console = Console()
    table = Table(title=title, show_lines=True)

    table.add_column("Area", style="cyan", no_wrap=True)
    table.add_column("Sub-Area", style="cyan", no_wrap=True)
    table.add_column("Total", justify="right")
    table.add_column("Pass", justify="right", style="green")
    table.add_column("Fail", justify="right", style="red")
    table.add_column("Error", justify="right", style="red")
    table.add_column("Skip", justify="right", style="yellow")
    table.add_column("Rate", justify="right")
    table.add_column("Time", justify="right")
    table.add_column("Status", justify="center")

    totals = TestSuiteResult(name="TOTAL", area="")

    for r in results:
        parts = r.name.split("/", 1)
        area = parts[0] if parts else r.area
        sub_area = parts[1] if len(parts) > 1 else ""

        # Status styling
        if r.status == "PASS":
            status_text = Text("PASS", style="bold green")
        elif r.status == "FAIL":
            status_text = Text("FAIL", style="bold red")
        elif r.status == "RUN_ERROR":
            status_text = Text(f"ERR: {r.run_error[:30]}", style="bold red")
        else:
            status_text = Text("N/A", style="dim")

        # Rate styling
        rate_str = f"{r.success_rate:.1f}%"
        if r.success_rate >= 100:
            rate_style = "bold green"
        elif r.success_rate >= 80:
            rate_style = "yellow"
        else:
            rate_style = "bold red"
        rate_text = Text(rate_str, style=rate_style) if r.total > 0 else Text("-", style="dim")

        # Time formatting
        if r.time_sec >= 60:
            time_str = f"{r.time_sec / 60:.1f}m"
        else:
            time_str = f"{r.time_sec:.1f}s"

        table.add_row(
            area, sub_area,
            str(r.total), str(r.passed), str(r.failed),
            str(r.errors), str(r.skipped),
            rate_text,
            time_str if r.total > 0 else "-",
            status_text,
        )

        totals.passed += r.passed
        totals.failed += r.failed
        totals.errors += r.errors
        totals.skipped += r.skipped
        totals.time_sec += r.time_sec

    # Add totals row
    total_rate = f"{totals.success_rate:.1f}%"
    if totals.success_rate >= 100:
        total_rate_text = Text(total_rate, style="bold green")
    elif totals.success_rate >= 80:
        total_rate_text = Text(total_rate, style="yellow")
    else:
        total_rate_text = Text(total_rate, style="bold red")

    total_status = Text("PASS", style="bold green") if totals.failed == 0 and totals.errors == 0 else Text("FAIL", style="bold red")
    total_time = f"{totals.time_sec / 60:.1f}m" if totals.time_sec >= 60 else f"{totals.time_sec:.1f}s"

    table.add_section()
    table.add_row(
        Text("TOTAL", style="bold"), "",
        Text(str(totals.total), style="bold"),
        Text(str(totals.passed), style="bold green"),
        Text(str(totals.failed), style="bold red") if totals.failed > 0 else str(totals.failed),
        Text(str(totals.errors), style="bold red") if totals.errors > 0 else str(totals.errors),
        str(totals.skipped),
        total_rate_text,
        total_time,
        total_status,
    )

    console.print()
    console.print(table)
    console.print()

    return totals


def export_markdown(results: list[TestSuiteResult], output_path: str, title: str = "Test Results"):
    """Export results as a markdown table."""
    lines = []
    lines.append(f"# {title}")
    lines.append("")
    lines.append(f"**Generated:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    lines.append("")
    lines.append("| Area | Sub-Area | Total | Pass | Fail | Error | Skip | Rate | Time | Status |")
    lines.append("|------|----------|------:|-----:|-----:|------:|-----:|-----:|-----:|--------|")

    totals = TestSuiteResult(name="TOTAL", area="")

    for r in results:
        parts = r.name.split("/", 1)
        area = parts[0] if parts else r.area
        sub_area = parts[1] if len(parts) > 1 else ""

        rate = f"{r.success_rate:.1f}%" if r.total > 0 else "-"
        time_str = f"{r.time_sec / 60:.1f}m" if r.time_sec >= 60 else f"{r.time_sec:.1f}s"
        status = r.status

        lines.append(
            f"| {area} | {sub_area} | {r.total} | {r.passed} | {r.failed} "
            f"| {r.errors} | {r.skipped} | {rate} | {time_str} | {status} |"
        )

        totals.passed += r.passed
        totals.failed += r.failed
        totals.errors += r.errors
        totals.skipped += r.skipped
        totals.time_sec += r.time_sec

    total_rate = f"{totals.success_rate:.1f}%" if totals.total > 0 else "-"
    total_time = f"{totals.time_sec / 60:.1f}m" if totals.time_sec >= 60 else f"{totals.time_sec:.1f}s"
    total_status = "PASS" if totals.failed == 0 and totals.errors == 0 else "FAIL"

    lines.append(
        f"| **TOTAL** | | **{totals.total}** | **{totals.passed}** | **{totals.failed}** "
        f"| **{totals.errors}** | **{totals.skipped}** | **{total_rate}** | **{total_time}** | **{total_status}** |"
    )

    with open(output_path, "w") as f:
        f.write("\n".join(lines) + "\n")

    print(f"Markdown report written to: {output_path}")


def main():
    parser = argparse.ArgumentParser(
        description="Aggregate test results across all environments",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__
    )
    parser.add_argument(
        "--run", action="store_true",
        help="Run tests via each area's Makefile, then display table"
    )
    parser.add_argument(
        "--area", action="append", dest="areas",
        help="Only include specific areas (e.g., --area rapids --area stream). Can repeat."
    )
    parser.add_argument(
        "--results-dir", type=str, default=None,
        help="Directory for JUnit XML output (default: <repo>/test_results/)"
    )
    parser.add_argument(
        "--scan-dir", type=str, default=None,
        help="Scan directory for existing JUnit XML files instead of running tests"
    )
    parser.add_argument(
        "--markdown", type=str, default=None,
        help="Export results as markdown to the given file path"
    )
    parser.add_argument(
        "--test-level", type=str, default=None,
        help="Test level: GATE, FUNC, FULL (default: from TEST_LEVEL env or GATE)"
    )
    parser.add_argument(
        "--timeout", type=int, default=0,
        help="Per-area timeout in seconds (default: 0 = no timeout)"
    )
    parser.add_argument(
        "--toml", type=str, default=None,
        help="Path to test_environments.toml (default: <repo>/test_environments.toml)"
    )
    parser.add_argument(
        "--list", action="store_true",
        help="List all test areas from TOML and exit"
    )

    args = parser.parse_args()

    repo_root = find_repo_root()

    # Load test areas from TOML
    test_areas = load_test_areas(repo_root)

    if args.list:
        print(f"{'Area':<20s} {'Sub-Area':<20s} {'Directory':<55s} {'Target'}")
        print("-" * 110)
        for area, sub_area, test_dir, make_target_fmt in test_areas:
            print(f"{area:<20s} {sub_area:<20s} {test_dir:<55s} {make_target_fmt}")
        print(f"\n{len(test_areas)} test areas total")
        return

    test_level = args.test_level or os.environ.get("TEST_LEVEL", "GATE")

    results_dir = Path(args.results_dir) if args.results_dir else repo_root / "test_results"
    results_dir.mkdir(parents=True, exist_ok=True)

    results = []

    if args.scan_dir:
        # Scan mode: find existing XML files
        scan_path = Path(args.scan_dir)
        if not scan_path.is_absolute():
            scan_path = repo_root / scan_path
        for xml_file in sorted(scan_path.rglob("*.xml")):
            try:
                tree = ET.parse(str(xml_file))
                root = tree.getroot()
                if root.tag not in ("testsuites", "testsuite"):
                    continue
            except (ET.ParseError, Exception):
                continue
            parsed = parse_junit_xml(str(xml_file))
            rel_path = xml_file.relative_to(scan_path)
            parsed.name = str(rel_path.with_suffix(""))
            parsed.area = rel_path.parts[0] if len(rel_path.parts) > 1 else "unknown"
            results.append(parsed)
        title = f"Test Results (scanned from {args.scan_dir})"

    elif args.run:
        # Run mode: delegate to each area's Makefile
        areas_to_run = test_areas
        if args.areas:
            areas_to_run = [a for a in test_areas if a[0] in args.areas]

        title = f"Test Results (TEST_LEVEL={test_level})"
        print(f"Running tests across {len(areas_to_run)} environments (level={test_level})...")
        print()

        for area, sub_area, test_dir, make_target_fmt in areas_to_run:
            label = f"{area}/{sub_area}" if sub_area else area
            print(f"  Running {label}...", end=" ", flush=True)
            r = run_tests_for_area(
                repo_root, area, sub_area, test_dir, make_target_fmt,
                results_dir, test_level, args.timeout
            )
            r.name = label
            results.append(r)

            if r.status == "PASS":
                print(f"PASS ({r.passed}/{r.total}, {r.time_sec:.1f}s)")
            elif r.status == "FAIL":
                print(f"FAIL ({r.passed}/{r.total} pass, {r.failed}F {r.errors}E)")
            else:
                print(f"{r.status}: {r.run_error[:60]}")

        print()

    else:
        # Default: display existing cached XML results
        if not any(results_dir.glob("*.xml")):
            print(f"No XML results found in {results_dir}/")
            print()
            print("Options:")
            print("  --run            Run all tests and collect results")
            print("  --scan-dir DIR   Scan a directory for existing JUnit XML files")
            print("  --list           List all test areas from TOML")
            print()
            print("Example:")
            print(f"  python3 {sys.argv[0]} --run --area rapids")
            sys.exit(1)

        title = "Test Results (from existing XML)"
        for area, sub_area, test_dir, make_target_fmt in test_areas:
            xml_filename = f"{area}_{sub_area}_results.xml" if sub_area else f"{area}_results.xml"
            xml_file = results_dir / xml_filename
            if xml_file.exists():
                parsed = parse_junit_xml(str(xml_file))
                parsed.name = f"{area}/{sub_area}" if sub_area else area
                parsed.area = area
                results.append(parsed)

    if not results:
        print("No test results found.")
        sys.exit(1)

    # Display results
    totals = display_rich_table(results, title=title)

    # Export markdown if requested
    if args.markdown:
        export_markdown(results, args.markdown, title=title)

    # Exit with failure if any tests failed
    if totals.failed > 0 or totals.errors > 0:
        sys.exit(1)


if __name__ == "__main__":
    main()
