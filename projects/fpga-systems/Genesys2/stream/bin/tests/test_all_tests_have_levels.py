# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_all_tests_have_levels
# Purpose: enforce that every test in this area honours gate/func/full
#
# Subsystem: fpga-systems/Genesys2/stream

"""Every test in this area must honour a level. This makes that mechanical.

The rule is not decorative. Before it, eleven of the thirteen simulation
tests read no level at all and a twelfth forwarded TEST_LEVEL to a cocotb
half that never read it. Asking the suite for its minimum therefore ran the
maximum: one test alone burned over two hours during a gate sweep, and the
sweep had to be abandoned rather than completed.

A test satisfies the rule one of two ways.

1. It SCALES. It imports `stream_levels` and uses the level to size its work
   -- descriptor counts, probe depth, stress iterations. Every test that
   drives a simulator must do this, because simulator time is the cost the
   levels exist to control.

2. It is FIXED-COST. A pure-Python unit test that runs in milliseconds has no
   workload to scale, and inventing three sizes for it would be theatre. Such
   a test is listed in FIXED_COST below WITH A REASON, and runs identically at
   every level.

FIXED_COST is a ledger, not an escape hatch -- the same role `[exempt]` plays
in bin/filelists.toml. A test that drives a simulator may never appear in it;
that is asserted, so the loophole cannot be widened silently.
"""

import ast
import os

import pytest

_AREA = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                     os.pardir, os.pardir))

#: Fixed-cost tests: pure Python, no simulator, milliseconds. Reason required.
FIXED_COST = {
    'bin/tests/test_dump_monbus.py':
        'decodes monbus records from a fixture; no DUT, no sweep',
    'bin/tests/test_dump_monbus_sram.py':
        'SRAM word/beat packing arithmetic; pure function under test',
    'bin/tests/test_harness_regmap.py':
        'consistency check: generated regmap vs the .sv header. One comparison '
        'over a fixed register set -- there is no "more" of it to do',
    'bin/tests/test_mon_configs.py':
        'monitor preset table lookups; a fixed table, checked exhaustively',
    'bin/tests/test_stream_levels.py':
        'tests the level helper itself; scaling it by its own level would be '
        'circular',
    'bin/tests/test_all_tests_have_levels.py':
        'this file: a static audit of the tree, cost independent of level',
    'bin/tests/test_bridge_dv_not_generated.py':
        'static audit of regen_bridges.sh plus an ast.parse of each bridge DV '
        'file; no DUT, and the file set is whatever is on disk',
    'build-mon/dv/tests/test_stream_cfg_single_source.py':
        'asserts the RTL package and the Python mirror agree; exhaustive over '
        'the parameter set by construction',
    'build-perf/dv/tests/test_harness_kick.py':
        'kick address staging arithmetic against a recording mock bridge',
    'build-perf/dv/tests/test_stream_device.py':
        'Stream host-object behaviour against a recording mock bridge',
    'build-perf/dv/tests/test_stream_ext_suite.py':
        'extended-descriptor field packing against a recording mock bridge',
    'build-perf/dv/tests/test_stream_ext_char.py':
        'extended-addressing case table construction; the sim that consumes '
        'it is test_stream_perf, which scales',
}


def _test_files():
    """Every test module in the area, excluding build/scratch trees."""
    skip = ('local_sim_build', 'sim_build', '__pycache__', 'logs',
            'fpga/build', 'generated')
    out = []
    for dirpath, dirnames, filenames in os.walk(_AREA):
        if any(s in dirpath for s in skip):
            continue
        dirnames[:] = [d for d in dirnames if d not in
                       ('local_sim_build', 'sim_build', '__pycache__', 'logs')]
        for fn in filenames:
            if fn.startswith('test_') and fn.endswith('.py'):
                out.append(os.path.relpath(os.path.join(dirpath, fn), _AREA))
    return sorted(out)


def _source(rel):
    with open(os.path.join(_AREA, rel), encoding='utf-8') as fh:
        return fh.read()


def _imports(tree):
    """Every module name the file actually imports (AST, not substrings).

    Substring matching is what made the first version of this file fail
    against ITSELF: the detector's own source contains the strings it looks
    for, so the audit reported that the audit drives a simulator. Parse
    instead of grep.
    """
    names = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            names.update(a.name for a in node.names)
        elif isinstance(node, ast.ImportFrom) and node.module:
            names.add(node.module)
    return names


def _drives_simulator(src):
    """True when the module really imports cocotb / cocotb_test."""
    mods = _imports(ast.parse(src))
    return any(m == 'cocotb' or m.startswith('cocotb.') or
               m.startswith('cocotb_test') for m in mods)


def _is_level_aware(src):
    """True when the module reads a test level by any supported means.

    Two forms count. `stream_levels` is the shared implementation and what new
    tests should use. A direct read of TEST_LEVEL / REG_LEVEL also counts:
    test_stream_perf resolves both by hand and has done so correctly since
    before the shared helper existed, and failing it here would be enforcing a
    style, not the rule. What does NOT count is merely mentioning the name --
    that is exactly the defect this whole exercise started from, where
    test_stream_mon_perf put TEST_LEVEL into an env dict nobody read.
    """
    tree = ast.parse(src)
    if 'stream_levels' in _imports(tree):
        return True
    # A genuine read: os.environ.get('TEST_LEVEL'...) / os.environ['REG_LEVEL']
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and node.value in ('TEST_LEVEL', 'REG_LEVEL'):
            parent_is_read = isinstance(getattr(node, 'parent', None), (ast.Call, ast.Subscript))
            if parent_is_read:
                return True
    # Fall back to a call-shaped search, since ast nodes carry no parent link.
    for node in ast.walk(tree):
        if isinstance(node, ast.Call):
            for arg in node.args:
                if isinstance(arg, ast.Constant) and arg.value in ('TEST_LEVEL', 'REG_LEVEL'):
                    return True
        if isinstance(node, ast.Subscript) and isinstance(node.slice, ast.Constant):
            if node.slice.value in ('TEST_LEVEL', 'REG_LEVEL'):
                return True
    return False


def test_area_has_tests():
    """Guard the guard: a walk that finds nothing would pass everything."""
    assert len(_test_files()) >= 15, _test_files()


@pytest.mark.parametrize('rel', _test_files())
def test_every_test_scales_or_is_declared_fixed_cost(rel):
    src = _source(rel)
    if _is_level_aware(src):
        return
    assert rel in FIXED_COST, (
        f"{rel} neither honours gate/func/full nor is declared fixed-cost.\n"
        f"Either import stream_levels and size the work with scale()/at_least(),\n"
        f"or add it to FIXED_COST in {os.path.basename(__file__)} with the "
        f"reason it has no workload to scale.")


@pytest.mark.parametrize('rel', sorted(FIXED_COST))
def test_fixed_cost_entries_still_exist(rel):
    """A stale ledger entry silently exempts a file that was renamed away."""
    assert os.path.isfile(os.path.join(_AREA, rel)), (
        f"FIXED_COST lists {rel}, which no longer exists. Remove the entry.")


@pytest.mark.parametrize('rel', sorted(FIXED_COST))
def test_fixed_cost_entries_have_a_reason(rel):
    reason = FIXED_COST[rel]
    assert reason and len(reason) > 20, (
        f"FIXED_COST[{rel}] needs a real reason, not {reason!r}")


@pytest.mark.parametrize('rel', sorted(FIXED_COST))
def test_no_simulator_test_is_exempt(rel):
    """THE load-bearing assertion.

    Simulator time is the entire reason levels exist. A test that drives a
    simulator must scale, never be waived -- otherwise the ledger becomes the
    way the rule gets avoided.
    """
    src = _source(rel)
    assert not _drives_simulator(src), (
        f"{rel} drives a simulator but is listed as fixed-cost. Simulator "
        f"tests must scale with the level; remove it from FIXED_COST and wire "
        f"stream_levels into it.")


@pytest.mark.parametrize('rel', _test_files())
def test_every_module_parses(rel):
    """Cheap tripwire for the failure that hid the bridge tests for months:
    a module that cannot be parsed is silently absent from every run."""
    ast.parse(_source(rel), filename=rel)
