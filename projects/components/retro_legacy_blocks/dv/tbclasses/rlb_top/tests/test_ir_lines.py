# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_ir_lines
# Purpose: Unit tests for the per-IR-line verdict (RLB TASK-018)
#
# Created: 2026-09-29

"""Unit tests for the rlb_top per-IR-line verdict -- no simulator required.

WHY THIS EXISTS. `_ir_lines_ok` is the check that says an interrupt arrived on
its block's OWN IR line rather than merely reaching the PIC. Its entire value is
in FAILING, and that is silently destructible: the fail-closed branch is one
line, and if it ever returned True instead, all seven rlb_top fabric tests would
keep reporting PASSED while asserting nothing. Nothing would go red. That is the
worst failure mode a suite has, and it is exactly what TASK-017's notes warn
about with the RTC test that "waits 500 cycles and passes anyway".

So the NEGATIVE cases below are the asset. The three positive ones only show the
check is not simply always-false.

This file deliberately imports nothing but the extracted module: no cocotb, no
TB, no DUT. It lives beside the code rather than in dv/tests/ because
make/tests.mk globs `test_*.py` there into area ROOTS, and a unit test is not a
simulation root.
"""

from __future__ import annotations

import os
import sys

# The parent of tests/ IS the rlb_top/ directory, so ir_lines is a sibling
# module -- import it flat rather than as a package, which needs no __init__.py
# and no repo root on the path.
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ir_lines import (CASCADE_IR, FABRIC_SOURCE_IRQ, ir_lines_verdict,
                      master_expectation, source_irq_consistent)


# --- the cascade rule, stated directly -------------------------------------
def test_master_side_only_does_not_expect_the_cascade():
    # PIT(0) and UART(4) land on the master directly; IR2 must NOT be expected.
    assert master_expectation([0]) == {0}
    assert master_expectation([4]) == {4}
    assert master_expectation([0, 4]) == {0, 4}


def test_slave_side_expects_the_cascade_and_not_its_own_number():
    # RTC(8), PM(9), SMBus(10), GPIO(11) reach the master ONLY via slave INT.
    for irq in (8, 9, 10, 11):
        assert master_expectation([irq]) == {CASCADE_IR}


def test_mixed_expects_the_master_bit_and_the_cascade():
    # UART(4) direct + GPIO(11)/PM(9) under the cascade.
    assert master_expectation([4, 9, 11]) == {4, CASCADE_IR}


def test_cascade_bit_is_two():
    assert CASCADE_IR == 2


# --- FAIL-CLOSED: an absent probe must never pass --------------------------
def test_absent_fabric_probe_fails_closed():
    ok, reason = ir_lines_verdict(None, {2}, [11])
    assert ok is False
    assert 'w_fabric_irq probe absent' in reason


def test_absent_master_probe_fails_closed():
    ok, reason = ir_lines_verdict({11}, None, [11])
    assert ok is False
    assert 'w_master_pic_irq probe absent' in reason


def test_both_probes_absent_fails_closed():
    ok, _ = ir_lines_verdict(None, None, [11])
    assert ok is False


def test_absent_fabric_probe_is_reported_before_a_master_problem():
    # Order matters: the fabric diagnostic must win, as in the original method.
    ok, reason = ir_lines_verdict(None, None, [11])
    assert ok is False
    assert 'w_fabric_irq' in reason


# --- the wrong-routing cases this check exists to catch --------------------
def test_source_ored_onto_a_second_fabric_line_fails():
    # The exact bug the aggregate check could not see.
    ok, reason = ir_lines_verdict({11, 12}, {2}, [11])
    assert ok is False
    assert 'fabric IR lines wrong' in reason
    assert 'extra=[12]' in reason


def test_missing_fabric_line_fails():
    ok, reason = ir_lines_verdict(set(), {2}, [11])
    assert ok is False
    assert 'missing=[11]' in reason


def test_slave_side_without_the_cascade_fails():
    # Slave source reached its fabric line but master IR2 never rose.
    ok, reason = ir_lines_verdict({11}, set(), [11])
    assert ok is False
    assert 'master IR lines wrong' in reason
    assert 'missing=[2]' in reason


def test_stray_master_bit_fails():
    ok, reason = ir_lines_verdict({11}, {2, 5}, [11])
    assert ok is False
    assert 'extra=[5]' in reason


def test_master_side_source_that_also_raised_the_cascade_fails():
    # UART is master-side: IR2 rising means something drove the slave too.
    ok, reason = ir_lines_verdict({4}, {4, 2}, [4])
    assert ok is False
    assert 'master IR lines wrong' in reason


# --- the positives, so the check is not merely always-false ----------------
def test_slave_side_correct():
    assert ir_lines_verdict({11}, {2}, [11]) == (True, None)


def test_master_side_correct():
    assert ir_lines_verdict({4}, {4}, [4]) == (True, None)


def test_three_coincident_spanning_both_pics_correct():
    assert ir_lines_verdict({4, 9, 11}, {2, 4}, [4, 9, 11]) == (True, None)


# --- shape robustness -------------------------------------------------------
def test_accepts_any_iterable_not_just_sets():
    assert ir_lines_verdict([11], [2], (11,)) == (True, None)


def test_duplicate_expected_irqs_are_harmless():
    assert ir_lines_verdict({11}, {2}, [11, 11]) == (True, None)


# --- the source/line cross-check (TASK-019 item 2) -------------------------
def test_each_known_source_matches_its_line():
    for src, irq in FABRIC_SOURCE_IRQ.items():
        assert source_irq_consistent(src, irq) == (True, None), src


def test_a_source_asserted_against_the_wrong_line_fails():
    # The exact hole: gpio_irq named, but fabric line 9 asserted. Each half of
    # the verdict passes on its own; together they must not.
    ok, reason = source_irq_consistent('gpio_irq', 9)
    assert ok is False
    assert 'drives fabric line 11' in reason


def test_unknown_source_fails_rather_than_skipping():
    ok, reason = source_irq_consistent('not_a_real_irq', 4)
    assert ok is False
    assert 'not in FABRIC_SOURCE_IRQ' in reason


def test_or_ed_lines_accept_every_sub_source():
    # Bit 0 and bit 8 are ORs; each contributor must map to the same line.
    assert source_irq_consistent('pit_timer_irq', 0)[0] is True
    assert source_irq_consistent('hpet_legacy_irq0', 0)[0] is True
    for s in ('rtc_alarm_irq', 'rtc_second_irq', 'hpet_legacy_irq8'):
        assert source_irq_consistent(s, 8)[0] is True


def test_map_covers_every_line_the_fabric_drives():
    # rlb_top.sv drives exactly these six lines.
    assert set(FABRIC_SOURCE_IRQ.values()) == {0, 4, 8, 9, 10, 11}
