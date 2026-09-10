# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
"""The per-cell level+seed environment for a Pattern B pytest wrapper, and the
guarantee that it actually reaches the simulator.

WHY THIS EXISTS
---------------
``cocotb_test.simulator.set_env`` applies the caller's ``extra_env`` first and
then copies EVERY ``os.environ`` entry over it::

    for e in os.environ:
        self.env[e] = os.environ[e]

So a process-level ``TEST_LEVEL`` beats the per-cell one a wrapper just passed
in ``extra_env``. Twelve component conftests set exactly that at import as a
"REG_LEVEL -> TEST_LEVEL bridge", and for eleven of them it is load-bearing:
their wrappers export nothing, so without it every test falls back to the
default depth and ``make run-all-full`` quietly runs a smaller matrix while
still reporting "passed" (measured on pumice fub during that conversion: 91
tests -> 79).

The trap is what happens when a wrapper in such an area DOES start exporting a
per-cell value: the stamp silently overrides it, the REG_LEVEL grid still
expands to gate/func/full cells, and every one of them runs at the same depth.
Measured on the bridge's first leveled FULL run, 2026-09-09: 216 cells, three
per test, all logging ``level=full`` with identical wall-clock.

WHAT DOES NOT WORK, MEASURED
---------------------------
Re-stamping this cell's value into ``os.environ`` from the wrapper, so that
what cocotb_test copies over ``extra_env`` is the cell's own value, looks like
it should make the wrapper authoritative and leave the eleven areas their
fallback. It does not. Measured on the bridge 2026-09-10 with the stamp
re-added to its conftest: the wrapper printed ``extra_env=gate
os.environ=gate`` immediately before ``run()`` and the simulation still logged
``TEST_LEVEL=full`` for all three cells, with 16 offsets per pair in every one.
The same three cells with the stamp REMOVED ran gate/func/full at 1/4/16
offsets. So the only thing measured to work is removing the conftest stamp and
having every wrapper export per cell -- and an area must convert both halves
together, because removing the stamp alone drops its tests to the default
depth. The bridge is the worked example (TOOL-016).

USAGE
-----
::

    from TBClasses.shared.test_levels import level_env, reg_level_grid

    @pytest.mark.parametrize("test_level", reg_level_grid())
    def test_thing(request, test_level):
        ...
        extra_env = {
            'COCOTB_LOG_LEVEL': 'INFO',
            'LOG_PATH': log_path,
            **level_env(test_level),
        }

Related: handbook [[test-runner]] (REG_LEVEL selects the grid, TEST_LEVEL sets
the depth), [[test-review]], [[seeds-and-determinism]] (SEED is pinned per test
node by the repo-root conftest; an explicit SEED is never overridden).
"""

import os
import random
from typing import Dict, List

LEVELS = ('gate', 'func', 'full')

# How many cells each REG_LEVEL expands to. Different counts are the point: if
# all three produced the same matrix the levels would be three names for one
# run. GATE is the smoke pass, FULL the sign-off sweep.
_GRID = {
    'GATE': ['gate'],
    'FUNC': ['gate', 'func'],
    'FULL': ['gate', 'func', 'full'],
}


def reg_level_grid(reg_level: str = None) -> List[str]:
    """The ``test_level`` cells this wrapper expands to, selected by REG_LEVEL
    (GATE 1, FUNC 2, FULL 3). Call it at module scope and parametrize on it."""
    lvl = (reg_level or os.environ.get('REG_LEVEL', 'FUNC')).upper()
    return list(_GRID.get(lvl, _GRID['FUNC']))


def current_level(default: str = 'gate') -> str:
    """The depth THIS cocotb process runs at, read by the TB from TEST_LEVEL."""
    lvl = os.environ.get('TEST_LEVEL', default).lower()
    return lvl if lvl in LEVELS else default


def level_env(test_level: str, **extra) -> Dict[str, str]:
    """``extra_env`` entries carrying this cell's depth and seed.

    These reach the simulator ONLY if the area's conftest does not stamp
    TEST_LEVEL into os.environ -- see the module docstring for the measurement.

    SEED: an explicitly supplied SEED is a reproduction request and is never
    overridden; otherwise the repo-root conftest has already pinned one per
    test node id, and this only formats it.
    """
    if test_level not in LEVELS:
        raise ValueError(f"test_level must be one of {LEVELS}, got {test_level!r}")
    env = {
        'TEST_LEVEL': test_level,
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
    }
    env.update({k: str(v) for k, v in extra.items()})
    return env
