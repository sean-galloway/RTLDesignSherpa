#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Board-less tests for the sequence container.

The two guarantees under test are the ones whose absence is SILENT on hardware:
an unknown or out-of-order sequence name must raise BEFORE any device traffic,
and a sequence must reach its registers only through the injected context.
"""

from __future__ import annotations

import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from sequence import (RunReport, Sequence, SequenceContext, SequenceError,  # noqa: E402
                      SequenceRunner, sequence)


class FakeBus:
    """Records every register touch, so a test can assert that nothing ran."""

    def __init__(self):
        self.writes = []

    def write(self, name, **fields):
        self.writes.append((name, fields))


def make_runner(**seqs):
    ctx = SequenceContext(bus=FakeBus(), log=lambda m: None)
    return SequenceRunner(ctx, log=lambda m: None), ctx


class Init(Sequence):
    name = "init"
    description = "bring the controller up"

    def run(self, ctx):
        ctx.bus.write("CTRL", init=1)
        return {"levelled": True}


class WriteRead(Sequence):
    name = "write_read"
    requires = ("init",)

    def run(self, ctx):
        assert ctx.result("init")["levelled"]
        ctx.bus.write("KICK", go=1)
        return {"crc_ok": True}


class Boom(Sequence):
    name = "boom"

    def run(self, ctx):
        raise ValueError("device wedged")


class SaysFalse(Sequence):
    name = "says_false"

    def run(self, ctx):
        return False


# ---------------------------------------------------------------------------
# Registration
# ---------------------------------------------------------------------------

def test_register_and_list():
    r, _ = make_runner()
    r.add(Init).add(WriteRead)
    assert r.names == ["init", "write_read"]


def test_duplicate_name_is_rejected():
    class OtherInit(Sequence):
        name = "init"

        def run(self, ctx):
            return None

    r, _ = make_runner()
    r.add(Init)
    with pytest.raises(SequenceError, match="duplicate sequence name"):
        r.add(OtherInit)


def test_nameless_sequence_is_rejected():
    class Anon(Sequence):
        def run(self, ctx):
            return None

    r, _ = make_runner()
    with pytest.raises(SequenceError, match="declares no name"):
        r.add(Anon)


def test_non_sequence_is_rejected():
    r, _ = make_runner()
    with pytest.raises(SequenceError, match="not a Sequence"):
        r.add(object())


# ---------------------------------------------------------------------------
# Resolution -- must fail BEFORE any traffic
# ---------------------------------------------------------------------------

def test_unknown_name_raises_and_touches_nothing():
    r, ctx = make_runner()
    r.add(Init)
    with pytest.raises(SequenceError, match="unknown sequence 'lnit'"):
        r.run(["init", "lnit"])
    assert ctx.bus.writes == []          # the whole point: nothing ran


def test_unknown_name_error_lists_registered_names():
    r, _ = make_runner()
    r.add(Init).add(WriteRead)
    with pytest.raises(SequenceError) as exc:
        r.resolve(["nope"])
    assert "init" in str(exc.value) and "write_read" in str(exc.value)


def test_missing_requirement_raises_and_touches_nothing():
    r, ctx = make_runner()
    r.add(Init).add(WriteRead)
    with pytest.raises(SequenceError, match="requires 'init'"):
        r.run(["write_read"])
    assert ctx.bus.writes == []


def test_requirement_checked_against_order_not_membership():
    # "init" IS in the list -- but after its dependant. That must be an error,
    # not a coin flip.
    r, ctx = make_runner()
    r.add(Init).add(WriteRead)
    with pytest.raises(SequenceError, match="not scheduled before it"):
        r.run(["write_read", "init"])
    assert ctx.bus.writes == []


def test_empty_order_raises():
    r, _ = make_runner()
    r.add(Init)
    with pytest.raises(SequenceError, match="empty sequence order"):
        r.run([])


def test_resolve_accepts_a_valid_plan():
    r, _ = make_runner()
    r.add(Init).add(WriteRead)
    assert [s.name for s in r.resolve(["init", "write_read"])] == ["init", "write_read"]


# ---------------------------------------------------------------------------
# Execution
# ---------------------------------------------------------------------------

def test_run_executes_in_the_requested_order():
    r, ctx = make_runner()
    r.add(Init).add(WriteRead)
    report = r.run(["init", "write_read"])
    assert report.ok
    assert [w[0] for w in ctx.bus.writes] == ["CTRL", "KICK"]


def test_results_flow_from_one_sequence_to_the_next():
    r, ctx = make_runner()
    r.add(Init).add(WriteRead)
    r.run(["init", "write_read"])
    assert ctx.results["init"] == {"levelled": True}
    assert ctx.results["write_read"] == {"crc_ok": True}


def test_raising_sequence_is_reported_not_propagated():
    r, _ = make_runner()
    r.add(Boom)
    report = r.run(["boom"])
    assert not report.ok
    assert isinstance(report.steps[0].error, ValueError)


def test_returning_false_marks_failure():
    r, _ = make_runner()
    r.add(SaysFalse)
    assert not r.run(["says_false"]).ok


def test_failure_stops_later_sequences_by_default():
    # Later steps would measure a board that never came up; their numbers would
    # look like data.
    r, ctx = make_runner()
    r.add(Boom).add(Init)
    report = r.run(["boom", "init"])
    assert [s.name for s in report.steps] == ["boom"]
    assert ctx.bus.writes == []


def test_stop_on_fail_false_runs_everything():
    r, _ = make_runner()
    r.add(Boom).add(Init)
    report = r.run(["boom", "init"], stop_on_fail=False)
    assert [s.name for s in report.steps] == ["boom", "init"]
    assert not report.ok


def test_teardown_runs_even_when_run_raises():
    torn = []

    class T(Sequence):
        name = "t"

        def run(self, ctx):
            raise RuntimeError("x")

        def teardown(self, ctx):
            torn.append(True)

    r, _ = make_runner()
    r.add(T)
    r.run(["t"])
    assert torn == [True]


def test_report_summary_mentions_each_step():
    r, _ = make_runner()
    r.add(Init).add(WriteRead)
    text = r.run(["init", "write_read"]).summary()
    assert "init" in text and "write_read" in text and "ALL PASS" in text


# ---------------------------------------------------------------------------
# Context
# ---------------------------------------------------------------------------

def test_context_result_raises_for_a_sequence_that_did_not_run():
    ctx = SequenceContext(bus=FakeBus())
    with pytest.raises(SequenceError, match="has not run"):
        ctx.result("init")


def test_context_params():
    ctx = SequenceContext(params={"txn": 1024})
    assert ctx.param("txn") == 1024
    assert ctx.param("missing", 7) == 7


# ---------------------------------------------------------------------------
# Decorator form
# ---------------------------------------------------------------------------

def test_decorator_builds_a_usable_sequence():
    @sequence("quick", requires=(), description="a one-liner")
    def quick(ctx):
        ctx.bus.write("Q", v=1)
        return "done"

    r, ctx = make_runner()
    r.add(quick)
    report = r.run(["quick"])
    assert report.ok
    assert ctx.results["quick"] == "done"
    assert ctx.bus.writes == [("Q", {"v": 1})]


# ---------------------------------------------------------------------------
# Discovery
# ---------------------------------------------------------------------------

def test_discover_registers_sequences_from_files(tmp_path):
    (tmp_path / "seq_alpha.py").write_text(
        "from sequence import Sequence\n"
        "class Alpha(Sequence):\n"
        "    name = 'alpha'\n"
        "    def run(self, ctx): return 1\n")
    (tmp_path / "seq_beta.py").write_text(
        "from sequence import Sequence\n"
        "class Beta(Sequence):\n"
        "    name = 'beta'\n"
        "    requires = ('alpha',)\n"
        "    def run(self, ctx): return 2\n")

    r, _ = make_runner()
    r.discover(str(tmp_path))
    assert r.names == ["alpha", "beta"]
    assert r.run(["alpha", "beta"]).ok


def test_discover_raises_when_nothing_found(tmp_path):
    # An empty area means the run would do nothing while reporting success.
    r, _ = make_runner()
    with pytest.raises(SequenceError, match="no sequences found"):
        r.discover(str(tmp_path))
