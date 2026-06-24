# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# DDR2/LPDDR2 coverage compile-args + env helpers.

"""Minimal helpers that flip Verilator line/toggle coverage on.

Port of `stream_coverage.coverage_mixin.get_coverage_compile_args` /
`get_coverage_env`. The functional/protocol-coverage layer is captured
by the YAML testplans under `dv/testplans/` plus their rollup scripts
(`bin/aggregate_coverage.py`, `bin/update_testplan_coverage.py`) — all
this module needs to do is make sure Verilator emits the per-test
`.dat` files those scripts consume.

Both helpers return empty list / dict when `COVERAGE=1` is not set,
so importing them in a test runner is free on a normal regression.
"""

from __future__ import annotations

import os
from typing import Dict, List, Optional


__all__ = [
    "get_coverage_compile_args",
    "get_coverage_env",
]


def get_coverage_compile_args() -> List[str]:
    """Verilator flags to enable line/toggle coverage.

    Returns:
        `['--coverage', '--coverage-line', '--coverage-toggle',
        '--coverage-underscore']` when `COVERAGE=1` is set, else `[]`.

    Use in a pytest runner::

        from projects.components.memory_controllers.ddr2_lpddr2.dv \\
            .ddr2_lpddr2_coverage import get_coverage_compile_args
        compile_args += get_coverage_compile_args()
    """
    if os.environ.get("COVERAGE", "0") != "1":
        return []
    return [
        "--coverage",
        "--coverage-line",
        "--coverage-toggle",
        "--coverage-underscore",
    ]


def get_coverage_env(test_name: str,
                     sim_build: Optional[str] = None) -> Dict[str, str]:
    """Environment vars that pin coverage-output location per test.

    Walks up from this file looking for `dv/tests/{fub,macro,top}/` so
    the cocotb subprocess writes its `.dat` files to a stable, per-tier
    location: `dv/tests/<tier>/coverage_data/per_test/`.

    Args:
        test_name: unique label for the test (file name without `.py`
            is fine).
        sim_build: path to the cocotb sim_build dir; used to infer
            tier and forwarded to the subprocess.

    Returns:
        dict to merge into the test's `extra_env` — empty when
        `COVERAGE=1` is not set.
    """
    if os.environ.get("COVERAGE", "0") != "1":
        return {}

    tier = "fub"
    if sim_build:
        abs_sb = os.path.abspath(sim_build)
        if "/tests/top/" in abs_sb or "/tests/top" in abs_sb:
            tier = "top"
        elif "/tests/macro/" in abs_sb or "/tests/macro" in abs_sb:
            tier = "macro"

    current = os.path.dirname(os.path.abspath(__file__))
    coverage_output_dir: Optional[str] = None
    while current != "/":
        candidate = os.path.join(current, "dv", "tests", tier)
        if os.path.exists(candidate):
            coverage_output_dir = os.path.join(
                current, "dv", "tests", tier, "coverage_data", "per_test"
            )
            break
        current = os.path.dirname(current)

    if not coverage_output_dir:
        coverage_output_dir = os.path.join(
            os.getcwd(), "coverage_data", "per_test"
        )

    os.makedirs(coverage_output_dir, exist_ok=True)

    env: Dict[str, str] = {
        "COVERAGE": "1",
        "COVERAGE_ENABLE": "1",
        "COVERAGE_TEST_NAME": test_name,
        "COVERAGE_OUTPUT_DIR": coverage_output_dir,
    }
    if sim_build:
        env["COVERAGE_SIM_BUILD"] = os.path.abspath(sim_build)
    return env
