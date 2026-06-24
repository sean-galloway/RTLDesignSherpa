# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# DDR2/LPDDR2 coverage package.

"""DDR2/LPDDR2 coverage helpers.

Mirrors stream's `stream_coverage` pattern. Provides a minimal
`get_coverage_compile_args()` + `get_coverage_env()` so each test
runner can opt in to Verilator line/toggle coverage by importing
this module and calling them in `compile_args` / `extra_env`.

Usage:
    from projects.components.memory_controllers.ddr2_lpddr2.dv \\
        .ddr2_lpddr2_coverage import (
        get_coverage_compile_args, get_coverage_env,
    )

    compile_args += get_coverage_compile_args()
    extra_env.update(get_coverage_env(test_name, sim_build=sim_build))

When `COVERAGE=1` is not set, both functions are no-ops — zero
overhead on normal test runs.
"""

from .coverage_helpers import (
    get_coverage_compile_args,
    get_coverage_env,
)

__all__ = [
    "get_coverage_compile_args",
    "get_coverage_env",
]
