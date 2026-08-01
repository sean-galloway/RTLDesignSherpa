#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Generic sequence container: named, ordered, dependency-checked test steps.

An area (pumice, rapids, stream, cdc) owns a set of sequences -- one init
sequence and one or more test sequences -- in its own `bin/` directory. A
`run_<test>.py` composes the transport once and asks the runner for an order:

    runner = SequenceRunner(ctx)
    runner.discover("projects/fpga-systems/NexysA7/pumice/bin")
    report = runner.run(["init", "write_read"])

Two rules this module enforces, because both failure modes are silent:

  1. A SEQUENCE NEVER OPENS ITS OWN PORT. It is handed a `SequenceContext`
     carrying an already-built bus, so the identical sequence runs against the
     FPGA and against a cocotb sim -- only the injected bridge differs. A
     sequence that took a `--port` would break that equivalence, which is the
     one property the whole harness stack exists to preserve.
  2. NAMES ARE DECLARED AND RESOLVED UP FRONT. Every sequence declares
     `name`; the runner resolves the whole requested order, plus every
     `requires`, BEFORE any UART traffic. A misspelled name raises immediately
     rather than skipping a step -- a skipped init looks exactly like a DDR2
     timing bug, and costs the same hour to chase.

`requires` is checked against what has actually RUN, not against the order you
typed, so "init" listed after its dependant is an error, not a coin flip.
"""

from __future__ import annotations

import time
import traceback
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, Iterable, List, Optional, Sequence as Seq


class SequenceError(RuntimeError):
    """Raised for structural problems: unknown name, unmet requirement, or a
    duplicate registration. Always raised before any device traffic."""


# ---------------------------------------------------------------------------
# Context -- everything a sequence is allowed to touch
# ---------------------------------------------------------------------------

@dataclass
class SequenceContext:
    """What a sequence gets. Note what is NOT here: no port, no baud rate, no
    bitstream path. Transport is already resolved by the runner's caller.

    `bus`      the by-name register interface (a `DeviceBus`, a `Device`, or an
               area-specific driver). Sequences address registers by name only.
    `board`    the `Board` this is running against, or None in sim.
    `params`   run-level knobs from the `run_*.py` CLI.
    `results`  what earlier sequences returned, keyed by sequence name. This is
               how a test sequence consumes init's output (leveling taps, say)
               without either one knowing about the other's internals.
    """

    bus: Any = None
    board: Any = None
    params: Dict[str, Any] = field(default_factory=dict)
    results: Dict[str, Any] = field(default_factory=dict)
    log: Optional[Callable[[str], None]] = None

    def say(self, msg: str) -> None:
        (self.log or print)(msg)

    def param(self, key: str, default: Any = None) -> Any:
        return self.params.get(key, default)

    def result(self, name: str) -> Any:
        """Output of an earlier sequence, by name. Raises if it did not run --
        the caller is asserting a dependency, so silence would be wrong."""
        if name not in self.results:
            raise SequenceError(
                f"no result for {name!r}; it has not run (declare it in requires)")
        return self.results[name]


# ---------------------------------------------------------------------------
# Sequence
# ---------------------------------------------------------------------------

class Sequence:
    """One named step. Subclass and implement `run(ctx)`.

        class Init(Sequence):
            name = "init"
            description = "bring up the controller and level the read path"
            def run(self, ctx):
                ctx.bus["pumice"].set_page_policy(1)
                return {"levelled": True}

    The return value is stored in `ctx.results[name]` for later sequences.
    """

    name: str = ""
    description: str = ""
    requires: Seq[str] = ()

    def run(self, ctx: SequenceContext) -> Any:  # pragma: no cover - abstract
        raise NotImplementedError(f"{type(self).__name__}.run() not implemented")

    # Optional hooks; default to no-ops so simple sequences stay simple.
    def setup(self, ctx: SequenceContext) -> None:
        pass

    def teardown(self, ctx: SequenceContext) -> None:
        pass

    def __repr__(self) -> str:
        return f"<Sequence {self.name!r}>"


def sequence(name: str, requires: Seq[str] = (), description: str = ""):
    """Decorator turning a plain function into a `Sequence`, for steps that do
    not need setup/teardown.

        @sequence("write_read", requires=("init",))
        def write_read(ctx): ...
    """
    def deco(fn: Callable[[SequenceContext], Any]):
        cls = type(
            fn.__name__,
            (Sequence,),
            {
                "name": name,
                "requires": tuple(requires),
                "description": description or (fn.__doc__ or "").strip().split("\n")[0],
                "run": lambda self, ctx, _fn=fn: _fn(ctx),
            },
        )
        cls._wrapped = fn
        return cls
    return deco


# ---------------------------------------------------------------------------
# Results
# ---------------------------------------------------------------------------

@dataclass
class StepResult:
    name: str
    ok: bool
    value: Any = None
    seconds: float = 0.0
    error: Optional[BaseException] = None

    @property
    def status(self) -> str:
        return "PASS" if self.ok else "FAIL"


@dataclass
class RunReport:
    steps: List[StepResult] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return all(s.ok for s in self.steps)

    @property
    def seconds(self) -> float:
        return sum(s.seconds for s in self.steps)

    def summary(self) -> str:
        width = max((len(s.name) for s in self.steps), default=4)
        lines = [f"  {s.name:<{width}}  {s.status}  {s.seconds:7.2f}s"
                 + (f"  {type(s.error).__name__}: {s.error}" if s.error else "")
                 for s in self.steps]
        head = f"{len(self.steps)} sequence(s), {self.seconds:.2f}s total: " \
               f"{'ALL PASS' if self.ok else 'FAILURES'}"
        return "\n".join([head] + lines)

    def __bool__(self) -> bool:
        return self.ok


# ---------------------------------------------------------------------------
# Registry + runner
# ---------------------------------------------------------------------------

class SequenceRunner:
    """Holds the registry for one area and runs a requested order against a ctx."""

    def __init__(self, ctx: Optional[SequenceContext] = None,
                 log: Optional[Callable[[str], None]] = None):
        self.ctx = ctx or SequenceContext()
        self.log = log or print
        if self.ctx.log is None:
            self.ctx.log = self.log
        self._registry: Dict[str, Sequence] = {}

    # ---- registration ------------------------------------------------------

    def add(self, seq) -> "SequenceRunner":
        """Register a Sequence subclass or instance."""
        inst = seq() if isinstance(seq, type) else seq
        if not isinstance(inst, Sequence):
            raise SequenceError(f"{seq!r} is not a Sequence")
        if not inst.name:
            raise SequenceError(f"{type(inst).__name__} declares no name")
        if inst.name in self._registry:
            raise SequenceError(
                f"duplicate sequence name {inst.name!r} "
                f"({type(self._registry[inst.name]).__name__} and "
                f"{type(inst).__name__}) -- names must be unique within an area")
        self._registry[inst.name] = inst
        return self

    def discover(self, path: str, pattern: str = "seq_*.py") -> "SequenceRunner":
        """Import every `seq_*.py` in `path` and register the Sequences it
        defines. Discovery is by CONTENT (subclasses found in the module), not
        by filename convention, so a file named oddly still contributes and a
        name typo shows up as a missing name at resolve time -- loudly."""
        import importlib.util
        import glob as _glob
        import os

        found = 0
        for file in sorted(_glob.glob(os.path.join(path, pattern))):
            mod_name = os.path.splitext(os.path.basename(file))[0]
            spec = importlib.util.spec_from_file_location(mod_name, file)
            if spec is None or spec.loader is None:
                continue
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            for attr in vars(module).values():
                if (isinstance(attr, type) and issubclass(attr, Sequence)
                        and attr is not Sequence and getattr(attr, "name", "")):
                    self.add(attr)
                    found += 1
        if found == 0:
            raise SequenceError(
                f"no sequences found in {path!r} matching {pattern!r} -- "
                f"nothing would run")
        return self

    # ---- introspection -----------------------------------------------------

    @property
    def names(self) -> List[str]:
        return sorted(self._registry)

    def get(self, name: str) -> Sequence:
        if name not in self._registry:
            raise SequenceError(
                f"unknown sequence {name!r}; registered: "
                f"{', '.join(self.names) or '(none)'}")
        return self._registry[name]

    def catalog(self) -> str:
        width = max((len(n) for n in self.names), default=4)
        return "\n".join(
            f"  {n:<{width}}  {self._registry[n].description}"
            + (f"  (requires {', '.join(self._registry[n].requires)})"
               if self._registry[n].requires else "")
            for n in self.names)

    # ---- resolution --------------------------------------------------------

    def resolve(self, order: Iterable[str]) -> List[Sequence]:
        """Validate the whole plan before anything runs.

        Every requested name must exist, and every `requires` must be satisfied
        by something EARLIER in the order. Missing dependencies are reported as
        an error, not auto-inserted: quietly running an init the caller did not
        ask for is its own surprise, and the fix is one word in the run script.
        """
        wanted = list(order)
        if not wanted:
            raise SequenceError("empty sequence order -- nothing to run")

        resolved = [self.get(n) for n in wanted]   # raises on unknown names

        seen: List[str] = []
        for seq in resolved:
            missing = [r for r in seq.requires if r not in seen]
            if missing:
                raise SequenceError(
                    f"sequence {seq.name!r} requires {', '.join(missing)!r}, "
                    f"which {'is' if len(missing) == 1 else 'are'} not scheduled "
                    f"before it (order so far: {' -> '.join(seen) or '(empty)'})")
            seen.append(seq.name)
        return resolved

    # ---- execution ---------------------------------------------------------

    def run(self, order: Iterable[str], stop_on_fail: bool = True) -> RunReport:
        """Resolve, then execute in order, recording a `StepResult` per step.

        `stop_on_fail` defaults True because these run against hardware: once
        init fails, later steps measure a controller that was never brought up,
        and their numbers are worse than useless -- they look like data.
        """
        plan = self.resolve(order)                 # fails before any traffic
        report = RunReport()

        self.log(f"[run] {len(plan)} sequence(s): "
                 f"{' -> '.join(s.name for s in plan)}")

        for seq in plan:
            self.log(f"[seq] {seq.name}"
                     + (f" -- {seq.description}" if seq.description else ""))
            started = time.time()
            try:
                seq.setup(self.ctx)
                value = seq.run(self.ctx)
                self.ctx.results[seq.name] = value
                ok = value is not False        # explicit False means failed
                step = StepResult(seq.name, ok, value, time.time() - started)
            except Exception as exc:  # noqa: BLE001 - report, do not mask
                step = StepResult(seq.name, False, None, time.time() - started, exc)
                self.log(f"[seq] {seq.name} raised: {type(exc).__name__}: {exc}")
                self.log(traceback.format_exc())
            finally:
                try:
                    seq.teardown(self.ctx)
                except Exception as exc:  # noqa: BLE001
                    self.log(f"[seq] {seq.name} teardown raised: {exc}")

            report.steps.append(step)
            self.log(f"[seq] {seq.name} {step.status} ({step.seconds:.2f}s)")
            if not step.ok and stop_on_fail:
                self.log("[run] stopping: later sequences would measure a "
                         "board that never came up")
                break

        self.log("[run] " + report.summary())
        return report
