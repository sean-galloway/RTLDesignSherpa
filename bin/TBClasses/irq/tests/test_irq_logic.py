"""Unit tests for the interrupt-line BFM's logic -- no simulator required.

The sampling coroutine needs cocotb running; the DECOMPOSITION does not, and
that is where the bugs would live. `diff_to_packets` was extracted precisely so
these cases are checkable in plain Python.
"""

from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.dirname(os.path.abspath(__file__))))))

from TBClasses.irq import IRQMonitor, IRQMonitorGroup, IRQPacket
from TBClasses.irq.irq_components import diff_to_packets, _resolve


# --- fakes, so the constructor can be exercised without a DUT --------------
class _FakeSignal:
    def __init__(self, value, width=1, raises=False):
        self._v, self._w, self._raises = value, width, raises

    @property
    def value(self):
        if self._raises:
            raise ValueError("unresolvable (X/Z)")
        return self._v

    def __len__(self):
        return self._w


class _FakeEntity:
    def __init__(self, **sigs):
        for k, v in sigs.items():
            setattr(self, k, v)


# --- diff_to_packets -------------------------------------------------------
def test_scalar_assert_has_no_index():
    pkts = diff_to_packets(0, 1, 'gpio_irq', 1, True, 10.0)
    assert len(pkts) == 1
    assert pkts[0].event == 'assert'
    assert pkts[0].index is None
    assert pkts[0].line == 'gpio_irq'


def test_scalar_deassert():
    pkts = diff_to_packets(1, 0, 'gpio_irq', 1, True, 10.0)
    assert [p.event for p in pkts] == ['deassert']


def test_no_change_yields_nothing():
    assert diff_to_packets(0b101, 0b101, 'x', 3, False, 0.0) == []


def test_vector_two_bits_assert_together():
    pkts = diff_to_packets(0b00, 0b11, 'pit_timer_irq', 3, False, 5.0)
    assert len(pkts) == 2
    assert [p.index for p in pkts] == [0, 1]
    assert all(p.event == 'assert' for p in pkts)
    # the WHOLE vector is carried, so coincidence is recoverable
    assert all(p.value == 0b11 for p in pkts)


def test_simultaneous_fall_and_rise_in_one_transition():
    """The case an OR fabric gets wrong: bit 0 falls as bit 1 rises."""
    pkts = diff_to_packets(0b01, 0b10, 'pit_timer_irq', 3, False, 7.0)
    assert len(pkts) == 2
    by_index = {p.index: p.event for p in pkts}
    assert by_index == {0: 'deassert', 1: 'assert'}


def test_count_continues_from_start():
    pkts = diff_to_packets(0b000, 0b101, 'v', 3, False, 1.0, start_count=7)
    assert [p.count for p in pkts] == [7, 8]


def test_vector_line_label_includes_index():
    p = IRQPacket(name='pit_timer_irq', index=2, event='assert')
    assert p.line == 'pit_timer_irq[2]'


# --- _resolve --------------------------------------------------------------
def test_resolve_returns_none_on_unresolvable():
    assert _resolve(_FakeSignal(0, raises=True)) is None


def test_resolve_returns_int():
    assert _resolve(_FakeSignal(3)) == 3


# --- monitor construction --------------------------------------------------
def test_width_is_auto_detected():
    ent = _FakeEntity(pit_timer_irq=_FakeSignal(0, width=3))
    mon = IRQMonitor(ent, 'T', 'pit_timer_irq', clock=None)
    assert mon.width == 3


def test_monitor_is_never_falsy_even_when_idle():
    """The documented cocotb trap: an empty-queue monitor must NOT be falsy."""
    ent = _FakeEntity(gpio_irq=_FakeSignal(0))
    mon = IRQMonitor(ent, 'T', 'gpio_irq', clock=None)
    assert len(mon.recv_queue) == 0
    assert bool(mon) is True
    assert not hasattr(IRQMonitor, '__len__')


def test_is_asserted_tolerates_x():
    ent = _FakeEntity(gpio_irq=_FakeSignal(0, raises=True))
    mon = IRQMonitor(ent, 'T', 'gpio_irq', clock=None)
    assert mon.is_asserted() is False


# --- group expect_only -----------------------------------------------------
def _group(**counts):
    ent = _FakeEntity(**{n: _FakeSignal(0) for n in counts})
    g = IRQMonitorGroup(ent, None, {n: None for n in counts})
    for n, c in counts.items():
        g.monitors[n]._assert_count = c
    return g


def test_expect_only_exact_match():
    g = _group(a=1, b=0)
    ok, missing, unexpected = g.expect_only(['a'])
    assert (ok, missing, unexpected) == (True, [], [])


def test_expect_only_names_the_missing_line():
    g = _group(a=0, b=0)
    ok, missing, unexpected = g.expect_only(['a'])
    assert ok is False and missing == ['a'] and unexpected == []


def test_expect_only_names_the_unexpected_line():
    g = _group(a=1, b=1)
    ok, missing, unexpected = g.expect_only(['a'])
    assert ok is False and missing == [] and unexpected == ['b']


def test_group_skips_signals_absent_from_the_dut():
    ent = _FakeEntity(present=_FakeSignal(0))
    g = IRQMonitorGroup(ent, None, {'present': None, 'absent': None})
    assert set(g.monitors) == {'present'}
