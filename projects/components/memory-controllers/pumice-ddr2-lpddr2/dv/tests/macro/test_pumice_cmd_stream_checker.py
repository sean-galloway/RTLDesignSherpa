"""Tests for the JEDEC command-stream checker itself. No RTL, no simulator.

AN ORACLE NEEDS ITS OWN TESTS. Every "zero violations" this suite reports about
pumice is only worth what this file proves: that each rule fires on a stream that
breaks it and stays silent on one that does not. An unchecked oracle degrades
into an expensive no-op, and this repo has shipped four blind checkers already
(feedback_checker_verdict_needs_a_count).

Writing these cases immediately caught five WRONG EXPECTATIONS of my own --
streams I had labelled legal that violate tRTP or tRC. That is the point: the
hand-built "obviously legal" stream is exactly where an oracle's author is least
reliable, so the legal cases here are as load-bearing as the illegal ones.
"""

import os
import sys

import pytest

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.pumice_dram_configs import (                   # noqa: E402
    ALL_CONFIGS, dram_config,
)
from tbclasses.pumice_cmd_stream_checker import (             # noqa: E402
    CmdStreamChecker, assert_clean, ALL_RULES,
    OP_ACT, OP_RD, OP_WR, OP_PRE, OP_PREA, OP_REF, OP_REFPB,
)

BOARD = 'board_ddr2_300'
FAST = 'ddr2_800_cl6_bl4'


def _t(cfg):
    return dram_config(cfg)[1]


def C(cyc, op, bank=0, row=0x10, col=0, ap=0):
    return dict(cycle=cyc, op=op, bank=bank, row=row, col=col, ap=ap)


def _rules(cmds, cfg=BOARD):
    v, stats = CmdStreamChecker(_t(cfg), label=cfg).check(cmds)
    return sorted({x['rule'] for x in v}), stats


# --------------------------------------------------------------------------
# Legal streams must be silent. Built from the config's OWN numbers rather than
# from literals, so they stay legal as the table grows.
# --------------------------------------------------------------------------
@pytest.mark.parametrize("cfg", ALL_CONFIGS)
def test_pumice_cmd_stream_checker_legal_open_page(cfg):
    """ACT, columns after tRCD, PRE after tRAS/tRTP, re-ACT after tRP/tRC."""
    t = _t(cfg)
    pre = max(t['tRAS'], t['tRCD'] + 1 + t['tRTP'])
    act2 = max(pre + t['tRP'], t['tRC'])
    cmds = [C(0, OP_ACT),
            C(t['tRCD'], OP_RD),
            C(t['tRCD'] + 1, OP_RD),
            C(pre, OP_PRE),
            C(act2, OP_ACT, row=0x20),
            C(act2 + t['tRCD'], OP_RD, row=0x20)]
    bad, _ = _rules(cmds, cfg)
    assert bad == [], f"{cfg}: a legal open-page stream was flagged {bad}"


@pytest.mark.parametrize("cfg", ALL_CONFIGS)
def test_pumice_cmd_stream_checker_legal_auto_precharge(cfg):
    """RDA at tRCD is LEGAL at every point; the next ACT waits for the device.

    JESD79-2F 3.8.1: the device starts the auto-precharge (AL + BL/2) after the
    column "if tRAS(min) and tRTP(min) are satisfied", and "if tRAS(min) is not
    satisfied at the edge, the start point of auto-precharge operation will be
    delayed until tRAS(min) is satisfied". So the CONTROLLER may issue the AP
    column as soon as tRCD allows -- tRAS and tRTP are the device's problem on
    this path, and delaying the column would only cost bandwidth.

    This test previously asserted the opposite, and the checker previously
    enforced it, which produced 16 confident violations against correct RTL at
    DDR2-800. The spec sentence is quoted in the checker beside the code so the
    next reader does not have to re-derive it.
    """
    t = _t(cfg)
    col = t['tRCD']
    act2 = max(col + t['tRTP'] + t['tRP'], t['tRAS'] + t['tRP'], t['tRC'])
    cmds = [C(0, OP_ACT), C(col, OP_RD, ap=1), C(act2, OP_ACT, row=0x20)]
    bad, _ = _rules(cmds, cfg)
    assert bad == [], f"{cfg}: a legal auto-precharge stream was flagged {bad}"


# --------------------------------------------------------------------------
# Each rule must FIRE on a stream that breaks it.
# --------------------------------------------------------------------------
def test_pumice_cmd_stream_checker_col_on_closed_bank():
    """The pumice BUG-003 signature: a column issued after a PRE, with no ACT."""
    t = _t(BOARD)
    bad, _ = _rules([C(0, OP_ACT), C(t['tRCD'], OP_RD),
                     C(t['tRAS'], OP_PRE), C(t['tRAS'] + 2, OP_RD)])
    assert 'col_on_closed' in bad


def test_pumice_cmd_stream_checker_col_on_wrong_row():
    """A stale row image issues a column against a row the bank does not hold.

    The oracle this replaces tracked open-vs-closed ONLY, so this case -- just as
    illegal, and the direct product of a stale registered bank image -- was
    invisible to it.
    """
    t = _t(BOARD)
    bad, _ = _rules([C(0, OP_ACT, row=0x10), C(t['tRCD'], OP_RD, row=0x99)])
    assert bad == ['col_on_wrong_row']


def test_pumice_cmd_stream_checker_act_on_open_bank():
    bad, _ = _rules([C(0, OP_ACT), C(_t(BOARD)['tRC'], OP_ACT)])
    assert 'act_on_open' in bad


def test_pumice_cmd_stream_checker_trcd():
    bad, _ = _rules([C(0, OP_ACT), C(_t(BOARD)['tRCD'] - 1, OP_RD)])
    assert bad == ['tRCD']


def test_pumice_cmd_stream_checker_tras_and_trtp():
    """A PRE too soon after its ACT breaks tRAS, and too soon after a RD tRTP."""
    t = _t(BOARD)
    bad, _ = _rules([C(0, OP_ACT), C(t['tRCD'], OP_RD), C(t['tRCD'] + 1, OP_PRE)])
    assert 'tRAS' in bad and 'tRTP' in bad


def test_pumice_cmd_stream_checker_trp():
    t = _t(BOARD)
    bad, _ = _rules([C(0, OP_ACT), C(t['tRAS'], OP_PRE),
                     C(t['tRAS'] + t['tRP'] - 1, OP_ACT)])
    assert 'tRP' in bad


def test_pumice_cmd_stream_checker_trrd():
    bad, _ = _rules([C(0, OP_ACT, bank=0),
                     C(_t(BOARD)['tRRD'] - 1, OP_ACT, bank=1)])
    assert 'tRRD' in bad


def test_pumice_cmd_stream_checker_tfaw():
    """tFAW needs a config where it can BIND.

    On the board tFAW=4 and tRRD=2, so tRRD alone already spaces four ACTs
    outside any tFAW window and tFAW is unreachable -- a tFAW check there is
    vacuous no matter what the stimulus does. That is not a checker defect, it is
    a property of the operating point, and it is the reason the config sweep
    exists at all: a rule that cannot arm on the board can still arm, and still
    catch something, at another legal point.
    """
    t_board, t_fast = _t(BOARD), _t(FAST)
    assert t_board['tFAW'] <= t_board['tRRD'] * 4, (
        "the board's tFAW is now reachable; this test's premise needs revisiting")
    assert t_fast['tFAW'] > t_fast['tRRD'] * 4, (
        f"{FAST} tFAW={t_fast['tFAW']} no longer binds against "
        f"tRRD={t_fast['tRRD']}; pick another config for this case")
    cmds = [C(i * t_fast['tRRD'], OP_ACT, bank=i) for i in range(5)]
    bad, stats = _rules(cmds, FAST)
    assert 'tFAW' in bad and stats['tFAW'] == 5


def test_pumice_cmd_stream_checker_refresh_needs_precharged_banks():
    t = _t(BOARD)
    bad, _ = _rules([C(0, OP_ACT), C(t['tRCD'], OP_RD), C(t['tRC'] + 4, OP_REF)])
    assert 'ref_with_open_bank' in bad
    bad, _ = _rules([C(0, OP_ACT), C(t['tRCD'], OP_RD),
                     C(t['tRC'] + 4, OP_REFPB)])
    assert 'refpb_on_open_bank' in bad


def test_pumice_cmd_stream_checker_trfc():
    t = _t(BOARD)
    bad, _ = _rules([C(0, OP_REF), C(t['tRFC'] - 1, OP_ACT)])
    assert 'tRFC' in bad


def test_pumice_cmd_stream_checker_one_command_per_cycle():
    bad, _ = _rules([C(0, OP_ACT, bank=0), C(0, OP_ACT, bank=1)])
    assert 'two_cmds_one_cycle' in bad


def test_pumice_cmd_stream_checker_prea_closes_every_bank():
    """PREA must close all banks -- a later column anywhere is then illegal."""
    t = _t(BOARD)
    cmds = [C(0, OP_ACT, bank=0), C(t['tRRD'], OP_ACT, bank=1),
            C(t['tRAS'] + 4, OP_PREA),
            C(t['tRAS'] + 6, OP_RD, bank=1)]
    bad, _ = _rules(cmds)
    assert 'col_on_closed' in bad


# --------------------------------------------------------------------------
# The vacuity guard itself.
# --------------------------------------------------------------------------
def test_pumice_cmd_stream_checker_rejects_a_vacuous_pass():
    """assert_clean must refuse a verdict when a required rule never armed."""
    t = _t(BOARD)
    legal = [C(0, OP_ACT), C(t['tRCD'], OP_RD)]
    assert_clean(legal, t, label="armed", require=('tRCD',))      # fine
    with pytest.raises(AssertionError, match="VACUOUS"):
        assert_clean(legal, t, label="never precharges", require=('tRP',))
    with pytest.raises(AssertionError, match="did not run"):
        assert_clean([], t, label="empty", min_cmds=1)


def test_pumice_cmd_stream_checker_since_replays_from_zero():
    """`since` must gate REPORTING only -- the replay still starts at index 0.

    This is the false-positive that the matrix's first run produced: check only
    the tail of a stream and every bank starts idle, so the first column in the
    tail is reported as a column to a closed bank. The ACT that opened it was
    simply before the slice.
    """
    t = _t(BOARD)
    cmds = [C(0, OP_ACT, bank=3),                     # opens bank 3 ...
            C(t['tRCD'], OP_RD, bank=3),
            C(t['tRCD'] + 4, OP_RD, bank=3)]          # ... still legal here
    # Slicing would lose the ACT and flag the tail. Replaying from 0 does not.
    v, stats = CmdStreamChecker(t).check(cmds, since=2)
    assert [x['rule'] for x in v] == [], (
        f"a legal column was flagged because state before `since` was dropped: "
        f"{[str(x) for x in v]}")
    # And the naive slice really would have failed, so the test has teeth.
    v_naive, _ = CmdStreamChecker(t).check(cmds[2:])
    assert [x['rule'] for x in v_naive] == ['col_on_closed']
    # Reporting is gated: only the one command at/after `since` armed the rule.
    assert stats['col_on_closed'] == 1


def test_pumice_cmd_stream_checker_every_rule_is_reachable():
    """No rule may be dead code. Each ALL_RULES entry must arm somewhere here.

    A rule nobody can trigger is indistinguishable from a rule that is broken,
    and it still contributes a reassuring name to the armed list.
    """
    t_b, t_f = _t(BOARD), _t(FAST)
    streams = [
        (t_b, [C(0, OP_ACT), C(t_b['tRCD'], OP_RD), C(t_b['tRAS'], OP_PRE),
               C(t_b['tRC'], OP_ACT), C(t_b['tRC'] + t_b['tRCD'], OP_WR),
               C(t_b['tRC'] + t_b['tRCD'] + t_b['tWR'], OP_PRE),
               C(t_b['tRC'] * 3, OP_REF), C(t_b['tRC'] * 3 + t_b['tRFC'], OP_ACT)]),
        (t_b, [C(0, OP_ACT, bank=0), C(t_b['tRRD'], OP_ACT, bank=1),
               C(0, OP_ACT, bank=2), C(5, OP_REFPB, bank=3)]),
        (t_b, [C(0, OP_ACT, row=0x10), C(t_b['tRCD'], OP_RD, row=0x99),
               C(t_b['tRAS'], OP_PRE), C(t_b['tRAS'] + 2, OP_RD)]),
        (t_f, [C(i * t_f['tRRD'], OP_ACT, bank=i) for i in range(5)]),
    ]
    armed = set()
    for t, cmds in streams:
        _v, stats = CmdStreamChecker(t).check(cmds)
        armed |= {r for r, n in stats.items() if n}
    # The turnarounds need both directions, in both orders: tRTW is RD -> WR and
    # tWTR is WR -> RD. The first pass of this file exercised only RD -> WR, and
    # this very assertion is what caught the gap.
    rd_then_wr = [C(0, OP_ACT), C(t_b['tRCD'], OP_RD),
                  C(t_b['tRCD'] + t_b['tRTW'], OP_WR)]
    wr_then_rd = [C(0, OP_ACT), C(t_b['tRCD'], OP_WR),
                  C(t_b['tRCD'] + t_b['tWTR'], OP_RD)]
    for cmds in (rd_then_wr, wr_then_rd):
        _v, stats = CmdStreamChecker(t_b).check(cmds)
        armed |= {r for r, n in stats.items() if n}
    dead = sorted(set(ALL_RULES) - armed)
    assert not dead, f"rules never armed by any case in this file: {dead}"
