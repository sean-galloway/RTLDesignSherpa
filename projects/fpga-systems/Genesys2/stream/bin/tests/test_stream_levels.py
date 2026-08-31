# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_stream_levels
# Purpose: guard the gate/func/full level resolution
#
# Subsystem: fpga-systems/Genesys2/stream

"""Level resolution, including the two behaviours that caused real damage.

The bug this module exists to prevent: `test_stream_mon_perf` forwarded
TEST_LEVEL into the cocotb environment where nothing read it, so asking the
suite for `gate` ran the full workload -- two hours in one test during a
"minimum" sweep. A knob that is silently ignored is worse than no knob,
because the caller believes the request was honoured.

The second is the fallback DIRECTION. An unrecognised level must resolve DOWN
to gate, never up to full: a typo should under-run visibly, not launch the
longest job in the suite.
"""

import os
import sys

import pytest

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                os.pardir))

import stream_levels as sl  # noqa: E402


@pytest.fixture(autouse=True)
def _clean_env(monkeypatch):
    """Neither variable set unless a test sets it."""
    monkeypatch.delenv('TEST_LEVEL', raising=False)
    monkeypatch.delenv('REG_LEVEL', raising=False)


# ---------------------------------------------------------------- resolution

def test_default_is_gate():
    """Unset means gate -- matches the area conftest fixture, so introducing
    this module deepens nothing that was already running."""
    assert sl.level() == sl.GATE


@pytest.mark.parametrize('value', ['gate', 'func', 'full'])
def test_canonical_levels_round_trip(monkeypatch, value):
    monkeypatch.setenv('TEST_LEVEL', value)
    assert sl.level() == value


@pytest.mark.parametrize('value', ['GATE', 'Func', 'FULL', '  full  '])
def test_case_and_whitespace_insensitive(monkeypatch, value):
    """The repo spells REG_LEVEL uppercase and TEST_LEVEL lowercase. A level
    that fails to apply because of case is a level that silently lies."""
    monkeypatch.setenv('TEST_LEVEL', value)
    assert sl.level() == value.strip().lower()


@pytest.mark.parametrize('alias,expected', [
    ('basic', sl.GATE), ('smoke', sl.GATE), ('quick', sl.GATE),
    ('medium', sl.FUNC), ('regression', sl.FUNC),
    ('nightly', sl.FULL), ('all', sl.FULL),
])
def test_aliases(monkeypatch, alias, expected):
    monkeypatch.setenv('TEST_LEVEL', alias)
    assert sl.level() == expected


def test_test_level_beats_reg_level(monkeypatch):
    monkeypatch.setenv('REG_LEVEL', 'FULL')
    monkeypatch.setenv('TEST_LEVEL', 'gate')
    assert sl.level() == sl.GATE


def test_reg_level_used_when_test_level_absent(monkeypatch):
    """397 call sites in this repo still spell it REG_LEVEL."""
    monkeypatch.setenv('REG_LEVEL', 'FULL')
    assert sl.level() == sl.FULL


# ------------------------------------------------------- the dangerous edge

def test_unknown_level_falls_back_to_gate_not_full(monkeypatch):
    """THE regression guard. Down, never up."""
    monkeypatch.setenv('TEST_LEVEL', 'exhaustive')
    with pytest.warns(RuntimeWarning):
        assert sl.level() == sl.GATE


def test_unknown_level_warns_loudly(monkeypatch):
    """Silent fallback hides the typo that caused the wrong-size run."""
    monkeypatch.setenv('TEST_LEVEL', 'ful')       # plausible typo
    with pytest.warns(RuntimeWarning, match='Unrecognised test level'):
        sl.level()


def test_empty_string_is_not_a_level(monkeypatch):
    """TEST_LEVEL= (exported but empty) is common in Makefiles."""
    monkeypatch.setenv('TEST_LEVEL', '')
    assert sl.level() == sl.GATE


# ------------------------------------------------------------ at_least/scale

@pytest.mark.parametrize('current,minimum,expected', [
    ('gate', 'gate', True),  ('gate', 'func', False), ('gate', 'full', False),
    ('func', 'gate', True),  ('func', 'func', True),  ('func', 'full', False),
    ('full', 'gate', True),  ('full', 'func', True),  ('full', 'full', True),
])
def test_at_least_is_cumulative(monkeypatch, current, minimum, expected):
    monkeypatch.setenv('TEST_LEVEL', current)
    assert sl.at_least(minimum) is expected


def test_at_least_rejects_unknown_minimum():
    """A typo in the CALL is a code bug, not user input -- raise, don't warn."""
    with pytest.raises(ValueError):
        sl.at_least('exhaustive')


@pytest.mark.parametrize('lvl,expected', [('gate', 8), ('func', 32), ('full', 128)])
def test_scale_picks_by_level(monkeypatch, lvl, expected):
    monkeypatch.setenv('TEST_LEVEL', lvl)
    assert sl.scale(8, 32, 128) == expected


def test_scale_carries_any_type(monkeypatch):
    monkeypatch.setenv('TEST_LEVEL', 'func')
    assert sl.scale(['a'], ['a', 'b'], ['a', 'b', 'c']) == ['a', 'b']


# ------------------------------------------------------------------ env/describe

def test_env_passes_resolved_level_not_raw(monkeypatch):
    """The cocotb half must not be able to re-resolve an alias differently
    from the pytest half -- that is how the two halves disagree about how
    much work to do."""
    monkeypatch.setenv('TEST_LEVEL', 'nightly')
    assert sl.env() == {'TEST_LEVEL': 'full', 'REG_LEVEL': 'FULL'}


def test_env_merges_extra(monkeypatch):
    monkeypatch.setenv('TEST_LEVEL', 'gate')
    out = sl.env({'SEED': '5'})
    assert out['SEED'] == '5' and out['TEST_LEVEL'] == 'gate'


def test_describe_names_the_source(monkeypatch):
    monkeypatch.setenv('REG_LEVEL', 'FULL')
    d = sl.describe()
    assert 'full' in d and 'REG_LEVEL' in d


def test_describe_shows_alias_mapping(monkeypatch):
    monkeypatch.setenv('TEST_LEVEL', 'basic')
    assert '-> gate' in sl.describe()


def test_describe_says_default_when_unset():
    assert 'default' in sl.describe()
