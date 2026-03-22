#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Test Target Generator
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Reads test_environments.toml and generates test_targets.mk for the root
# Makefile to include.
#
# Usage:
#   python3 bin/generate_test_targets.py              # writes test_targets.mk
#   python3 bin/generate_test_targets.py --dry-run     # print to stdout
#   python3 bin/generate_test_targets.py --list        # list environments
#
# Author: sean galloway
# Created: 2026-03-21

"""
Generate Makefile targets from test_environments.toml.

Produces a single test_targets.mk file that the root Makefile includes.
Each environment gets a consistent set of targets:

  test-{name}                 default (FUNC, parallel)
  test-{name}-{level}         GATE / FUNC / FULL, parallel
  test-{name}-{level}-waves   with WAVES=1
  test-{name}-{level}-serial  sequential execution
  coverage-{name}             coverage run
  coverage-report-{name}      report only
"""

import argparse
import os
import sys
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


LEVELS = ["gate", "func", "full"]
REPO_ROOT = Path(__file__).resolve().parent.parent
TOML_PATH = REPO_ROOT / "test_environments.toml"
OUTPUT_PATH = REPO_ROOT / "test_targets.mk"


def load_config(path: Path) -> dict:
    """Load and return the parsed TOML config."""
    with open(path, "rb") as f:
        return tomllib.load(f)


def merge_defaults(env: dict, defaults: dict) -> dict:
    """Return env config with defaults filled in."""
    merged = dict(defaults)
    merged.update(env)
    return merged


def gen_pytest_cmd(cfg: dict, level: str, *, parallel: bool,
                   waves: bool, coverage: bool) -> str:
    """Build a pytest invocation string."""
    parts = []

    # Environment variables
    env_vars = []

    # REG_LEVEL / TEST_LEVEL
    rl_var = cfg.get("reg_level_var", "REG_LEVEL")
    rl_values = cfg.get("reg_level_values", {})
    rl_value = rl_values.get(level, level.upper())
    env_vars.append(f"{rl_var}={rl_value}")

    if waves:
        env_vars.append("WAVES=1")

    if coverage:
        env_vars.append("COVERAGE=1")
        extra = cfg.get("coverage_extra_env", {})
        for k, v in extra.items():
            env_vars.append(f"{k}={v}")

    parts.extend(env_vars)

    # pytest itself
    parts.append("$(PYTEST)")

    # Flags
    flags = cfg.get("pytest_flags", "-v --tb=short")
    parts.append(flags)

    # Parallel
    if parallel:
        workers = cfg.get("parallel_workers", 48)
        if coverage:
            workers = cfg.get("coverage_workers", workers)
        if workers and workers > 0:
            reruns = cfg.get("coverage_reruns" if coverage else "reruns", 3)
            delay = cfg.get("coverage_reruns_delay" if coverage else "reruns_delay", 1)
            parts.append(f"-n {workers}")
            if reruns > 0:
                parts.append(f"--reruns {reruns} --reruns-delay {delay}")
    else:
        # Serial — still add reruns if configured
        reruns = cfg.get("reruns", 3)
        delay = cfg.get("reruns_delay", 1)
        if reruns > 0:
            parts.append(f"--reruns {reruns} --reruns-delay {delay}")

    # Test pattern
    pattern = cfg.get("test_pattern", "test_*.py")
    parts.append(pattern)

    return " ".join(parts)


def gen_environment_targets(name: str, cfg: dict) -> list[str]:
    """Generate all Makefile targets for one environment."""
    lines = []
    directory = cfg["directory"]
    description = cfg.get("description", name)
    can_parallel = cfg.get("parallel_workers", 48) > 0

    lines.append(f"# --- {name}: {description} ---")
    lines.append("")

    # Helper: emit a target that cd's into the directory and runs pytest
    def emit(target: str, level: str, *, parallel: bool, waves: bool = False,
             coverage: bool = False):
        cmd = gen_pytest_cmd(cfg, level, parallel=parallel, waves=waves,
                             coverage=coverage)
        mode = "parallel" if parallel else "serial"
        extra = ""
        if waves:
            extra = " + waves"
        if coverage:
            extra = " + coverage"
        label = f"{name} {level.upper()} ({mode}{extra})"

        lines.append(f".PHONY: {target}")
        lines.append(f"{target}:")
        lines.append(f'\t@echo "=== {label} ==="')
        lines.append(f"\t@cd {directory} && {cmd}")
        lines.append("")

    # ---- Default: test-{name} = FUNC parallel ----
    emit(f"test-{name}", "func", parallel=can_parallel)

    # ---- Per-level: test-{name}-{level} (parallel) ----
    for level in LEVELS:
        emit(f"test-{name}-{level}", level, parallel=can_parallel)

    # ---- Per-level waves: test-{name}-{level}-waves ----
    for level in LEVELS:
        emit(f"test-{name}-{level}-waves", level, parallel=can_parallel,
             waves=True)

    # ---- Per-level serial: test-{name}-{level}-serial ----
    for level in LEVELS:
        emit(f"test-{name}-{level}-serial", level, parallel=False)

    # ---- Coverage targets ----
    if cfg.get("coverage", False):
        # If the component has its own make coverage target, delegate to it
        cov_target = cfg.get("coverage_target")
        cov_report_target = cfg.get("coverage_report_target")

        if cov_target:
            # Delegate to the component's own Makefile
            lines.append(f".PHONY: coverage-{name}")
            lines.append(f"coverage-{name}:")
            lines.append(f'\t@echo "=== {name} coverage ==="')
            lines.append(f"\t@$(MAKE) -C {directory} {cov_target}")
            lines.append("")
        else:
            # Generate a direct pytest coverage run
            emit(f"coverage-{name}", "func", parallel=can_parallel,
                 coverage=True)

        if cov_report_target:
            lines.append(f".PHONY: coverage-report-{name}")
            lines.append(f"coverage-report-{name}:")
            lines.append(f'\t@echo "=== {name} coverage report ==="')
            lines.append(f"\t@$(MAKE) -C {directory} {cov_report_target}")
            lines.append("")

    return lines


def gen_aggregate_targets(envs: dict[str, dict]) -> list[str]:
    """Generate 'all' targets that invoke every environment."""
    lines = []
    env_names = list(envs.keys())
    cov_names = [n for n, c in envs.items() if c.get("coverage", False)]

    lines.append("# ==============================================================================")
    lines.append("# Aggregate targets — all environments")
    lines.append("# ==============================================================================")
    lines.append("")

    # test-all-{level}
    for level in LEVELS:
        target = f"test-all-{level}"
        deps = " ".join(f"test-{n}-{level}" for n in env_names)
        lines.append(f".PHONY: {target}")
        lines.append(f"{target}: {deps}")
        lines.append("")

    # test-all-{level}-serial
    for level in LEVELS:
        target = f"test-all-{level}-serial"
        deps = " ".join(f"test-{n}-{level}-serial" for n in env_names)
        lines.append(f".PHONY: {target}")
        lines.append(f"{target}: {deps}")
        lines.append("")

    # test-all-{level}-waves
    for level in LEVELS:
        target = f"test-all-{level}-waves"
        deps = " ".join(f"test-{n}-{level}-waves" for n in env_names)
        lines.append(f".PHONY: {target}")
        lines.append(f"{target}: {deps}")
        lines.append("")

    # coverage-all
    deps = " ".join(f"coverage-{n}" for n in cov_names)
    lines.append(f".PHONY: coverage-all")
    lines.append(f"coverage-all: {deps}")
    lines.append("")

    # coverage-report-all
    report_names = [n for n in cov_names
                    if envs[n].get("coverage_report_target")]
    if report_names:
        deps = " ".join(f"coverage-report-{n}" for n in report_names)
        lines.append(f".PHONY: coverage-report-all")
        lines.append(f"coverage-report-all: {deps}")
        lines.append("")

    return lines


def gen_help(envs: dict[str, dict]) -> list[str]:
    """Generate a help target listing all generated targets."""
    lines = []
    lines.append("# ==============================================================================")
    lines.append("# Help for generated targets")
    lines.append("# ==============================================================================")
    lines.append("")
    lines.append(".PHONY: help-envs")
    lines.append("help-envs:")
    lines.append('\t@echo "================================================================================"')
    lines.append('\t@echo "Test Environment Targets (generated from test_environments.toml)"')
    lines.append('\t@echo "================================================================================"')
    lines.append('\t@echo ""')
    lines.append('\t@echo "DEFAULT (FUNC, parallel):"')

    for name, cfg in envs.items():
        desc = cfg.get("description", "")
        workers = cfg.get("parallel_workers", 48)
        mode = f"{workers}w" if workers > 0 else "serial"
        lines.append(f'\t@echo "  make test-{name:<28s} {desc} ({mode})"')

    lines.append('\t@echo ""')
    lines.append('\t@echo "PER-LEVEL (append -gate, -func, or -full):"')
    lines.append('\t@echo "  make test-{name}-gate             GATE level"')
    lines.append('\t@echo "  make test-{name}-func             FUNC level"')
    lines.append('\t@echo "  make test-{name}-full             FULL level"')
    lines.append('\t@echo ""')
    lines.append('\t@echo "VARIANTS (append to any per-level target):"')
    lines.append('\t@echo "  ...-waves                         Enable waveform dump"')
    lines.append('\t@echo "  ...-serial                        Force sequential execution"')
    lines.append('\t@echo ""')
    lines.append('\t@echo "AGGREGATE:"')
    lines.append('\t@echo "  make test-all-gate                All envs, GATE, parallel"')
    lines.append('\t@echo "  make test-all-func                All envs, FUNC, parallel"')
    lines.append('\t@echo "  make test-all-full                All envs, FULL, parallel"')
    lines.append('\t@echo "  make test-all-{level}-serial      All envs, serial"')
    lines.append('\t@echo "  make test-all-{level}-waves       All envs, with waves"')
    lines.append('\t@echo ""')

    cov_names = [n for n, c in envs.items() if c.get("coverage", False)]
    if cov_names:
        lines.append('\t@echo "COVERAGE:"')
        for name in cov_names:
            lines.append(f'\t@echo "  make coverage-{name}"')
        lines.append('\t@echo "  make coverage-all                 All components"')
        lines.append('\t@echo "  make coverage-report-all          All reports"')
        lines.append('\t@echo "  make coverage-unified             Cross-component dashboard"')
        lines.append('\t@echo ""')

    lines.append('\t@echo "REGENERATE:"')
    lines.append('\t@echo "  python3 bin/generate_test_targets.py"')
    lines.append('\t@echo "================================================================================"')
    lines.append("")

    return lines


def generate(config: dict, *, dry_run: bool = False) -> str:
    """Generate the complete .mk file content."""
    defaults = config.get("defaults", {})
    envs_raw = config.get("env", {})

    # Merge defaults into each environment
    envs = {}
    for name, env_cfg in envs_raw.items():
        envs[name] = merge_defaults(env_cfg, defaults)

    lines = []
    lines.append("# ==============================================================================")
    lines.append("# AUTO-GENERATED — do not edit manually")
    lines.append("# Regenerate: python3 bin/generate_test_targets.py")
    lines.append("# Source:     test_environments.toml")
    lines.append("# ==============================================================================")
    lines.append("")
    lines.append("PYTEST ?= python3 -m pytest")
    lines.append("")

    # Per-environment targets
    for name, cfg in envs.items():
        lines.extend(gen_environment_targets(name, cfg))

    # Aggregate targets
    lines.extend(gen_aggregate_targets(envs))

    # Help
    lines.extend(gen_help(envs))

    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description="Generate Makefile test targets")
    parser.add_argument("--toml", default=str(TOML_PATH),
                        help="Path to test_environments.toml")
    parser.add_argument("--output", "-o", default=str(OUTPUT_PATH),
                        help="Output .mk file path")
    parser.add_argument("--dry-run", action="store_true",
                        help="Print to stdout instead of writing")
    parser.add_argument("--list", action="store_true",
                        help="List environments and exit")
    args = parser.parse_args()

    config = load_config(Path(args.toml))

    if args.list:
        defaults = config.get("defaults", {})
        envs = config.get("env", {})
        print(f"{'Name':<25s} {'Directory':<50s} {'Workers':>7s}  {'Coverage'}")
        print("-" * 95)
        for name, env_cfg in envs.items():
            cfg = merge_defaults(env_cfg, defaults)
            workers = cfg.get("parallel_workers", 48)
            w_str = str(workers) if workers > 0 else "serial"
            cov = "yes" if cfg.get("coverage", False) else "no"
            print(f"{name:<25s} {cfg['directory']:<50s} {w_str:>7s}  {cov}")
        return

    content = generate(config)

    if args.dry_run:
        print(content)
    else:
        with open(args.output, "w") as f:
            f.write(content)
        print(f"Generated {args.output} "
              f"({len(config.get('env', {}))} environments)")


if __name__ == "__main__":
    main()
