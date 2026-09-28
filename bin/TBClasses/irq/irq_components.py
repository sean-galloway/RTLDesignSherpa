# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: IRQMonitor / IRQMonitorGroup
# Purpose: BFM for plain interrupt lines -- level or pulse, scalar or vector
#
# Created: 2026-09-28

"""Interrupt-line BFM.

WHY THIS EXISTS. Every block in a legacy-peripheral subsystem exposes an
interrupt, and before this the tests observed them by hand -- `int(dut.sig.value)`
polled inside a loop, in twelve different places, each with its own idea of how
long to wait and what counts as an event. That is the "hand-rolled monitor"
the handbook warns about: it misses narrow pulses between polls, it cannot say
WHEN something asserted, and no two call sites agree.

WHAT THIS IS NOT. An interrupt line has no handshake. Anything with
valid/ready -- the IOAPIC's `irq_out_valid`/`irq_out_ready`/`irq_out_retry`
delivery channel, for instance -- is GAXI's job, not this module's. Use this
only for plain level or pulse lines.

PLACEMENT (2026-09-28, owner's call): this lives in bin/TBClasses rather than
in RDS-DV so it can be iterated on without a package reinstall. The package
layout deliberately mirrors an RDS-DV component family (__init__ / _packet /
_components), so promoting it later is a directory move, not a rewrite. Do not
"correct" it into RDS-DV without that conversation.

THE FALSY-MONITOR TRAP, STRUCTURALLY AVOIDED. cocotb's Monitor defines
__len__ as queue depth, so an idle monitor is FALSY and `mon.get_stats() if mon
else {}` silently returns {}. An idle interrupt line is the NORMAL case here,
so that trap would fire constantly. This class does not inherit cocotb.Monitor
and does not define __len__: `if mon:` is always True. Check `is not None` if
you must, but you no longer have to remember why.
"""

import logging
from collections import deque
from typing import Any, Callable, Dict, List, Optional, Sequence, Set

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.utils import get_sim_time

from .irq_packet import IRQPacket


def _resolve(sig) -> Optional[int]:
    """Read a signal as an int, or None if it is X/Z.

    Interrupt lines are X before reset deasserts, and a monitor that raises
    there dies inside its own coroutine -- silently, because nothing awaits it.
    Returning None lets the caller treat unresolvable as "no event" without
    pretending it saw a 0.
    """
    try:
        return int(sig.value)
    except (ValueError, TypeError):
        return None


def diff_to_packets(prev: int, cur: int, name: str, width: int,
                    scalar: bool, time_ns: float,
                    start_count: int = 0) -> List[IRQPacket]:
    """Decompose one transition into a packet per CHANGED bit. Pure function.

    Extracted from the sampling coroutine deliberately: this is the only real
    logic in the monitor, and inside a cocotb coroutine it could not be tested
    without standing up a whole simulation. Here it is checkable in plain
    Python, including the case an OR fabric is most likely to get wrong -- one
    bit falling while another rises in the SAME transition.
    """
    packets: List[IRQPacket] = []
    changed = cur ^ prev
    n = start_count
    for bit in range(width):
        if not (changed >> bit) & 1:
            continue
        rising = bool((cur >> bit) & 1)
        packets.append(IRQPacket(
            time_ns=time_ns,
            count=n,
            name=name,
            index=None if scalar else bit,
            event='assert' if rising else 'deassert',
            value=cur,
        ))
        n += 1
    return packets


class IRQMonitor:
    """Passive monitor for one interrupt line, scalar or vector.

    Samples on a clock edge and emits one IRQPacket per CHANGED BIT. Level and
    pulse lines are both handled: what is recorded is the transition, so a
    level that stays high produces exactly one 'assert'.
    """

    def __init__(self, entity, title: str, signal_name: str,
                 clock: Any,
                 width: Optional[int] = None,
                 log: Optional[logging.Logger] = None,
                 callback: Optional[Callable[[IRQPacket], None]] = None):
        """
        Args:
            entity:      DUT handle
            title:       label for logging
            signal_name: attribute name on the DUT, e.g. 'pit_timer_irq'
            clock:       the clock to sample on
            width:       bit width; auto-detected when omitted
            log:         optional logger
            callback:    optional per-packet callback
        """
        self.entity = entity
        self.title = title
        self.signal_name = signal_name
        self.signal = getattr(entity, signal_name)
        self.clock = clock
        self.callback = callback
        self.log = log or logging.getLogger(f"cocotb.irq.{title}")

        if width is not None:
            self.width = width
        else:
            try:
                self.width = len(self.signal)
            except TypeError:
                self.width = 1
        # A 1-bit vector and a scalar are reported differently: index None for
        # a true scalar, so a test reads 'gpio_irq' not 'gpio_irq[0]'.
        self._scalar = self.width == 1

        self._recv_queue: deque = deque()
        self._assert_count = 0
        self._deassert_count = 0
        self._prev: Optional[int] = None
        self._running = False
        self._task = None

    # -- observation ------------------------------------------------------
    @property
    def recv_queue(self) -> deque:
        return self._recv_queue

    @property
    def assert_count(self) -> int:
        return self._assert_count

    @property
    def deassert_count(self) -> int:
        return self._deassert_count

    def is_asserted(self, index: Optional[int] = None) -> bool:
        """Current level. index is required for a vector wider than 1."""
        v = _resolve(self.signal)
        if v is None:
            return False
        if index is None:
            return v != 0
        return bool((v >> index) & 1)

    def events(self, event: Optional[str] = None,
               index: Optional[int] = None) -> List[IRQPacket]:
        """Captured packets, optionally filtered by event and/or bit index."""
        out = list(self._recv_queue)
        if event is not None:
            out = [p for p in out if p.event == event]
        if index is not None:
            out = [p for p in out if p.index == index]
        return out

    def get_stats(self) -> Dict[str, Any]:
        return {
            'title': self.title,
            'signal': self.signal_name,
            'width': self.width,
            'asserts': self._assert_count,
            'deasserts': self._deassert_count,
            'captured': len(self._recv_queue),
        }

    def clear(self):
        """Drop captured events and counts; keeps the sampled level."""
        self._recv_queue.clear()
        self._assert_count = 0
        self._deassert_count = 0

    # -- lifecycle --------------------------------------------------------
    def start(self):
        if not self._running:
            self._running = True
            self._prev = _resolve(self.signal)
            self._task = cocotb.start_soon(self._monitor_recv())
            self.log.debug(f"IRQ monitor '{self.title}' started on "
                           f"{self.signal_name}[{self.width}]")

    def stop(self):
        self._running = False
        if self._task:
            self._task.kill()
            self._task = None

    def sample(self, time_ns: float):
        """Sample once and record any transition. Pure of triggers.

        Split out so a GROUP can drive twelve monitors from ONE coroutine.
        Twelve monitors each awaiting RisingEdge every clock costs twelve
        scheduler wakeups per edge, and on a long rlb_top run that was
        measurable -- the suite went 187s -> 359s when the group was first
        wired in with a task per line.
        """
        cur = _resolve(self.signal)
        if cur is None:              # X/Z -- not an event, and not a 0 either
            return
        if self._prev is None:
            self._prev = cur
            return
        if cur != self._prev:
            for pkt in diff_to_packets(
                    self._prev, cur, self.signal_name, self.width,
                    self._scalar, time_ns,
                    self._assert_count + self._deassert_count):
                self._recv_queue.append(pkt)
                if pkt.event == 'assert':
                    self._assert_count += 1
                else:
                    self._deassert_count += 1
                self.log.debug(f"{self.title}: {pkt}")
                if self.callback:
                    self.callback(pkt)
        self._prev = cur

    async def _monitor_recv(self):
        while self._running:
            await RisingEdge(self.clock)
            cur = _resolve(self.signal)
            if cur is None:          # X/Z -- not an event, and not a 0 either
                continue
            if self._prev is None:
                self._prev = cur
                continue
            if cur != self._prev:
                for pkt in diff_to_packets(
                        self._prev, cur, self.signal_name, self.width,
                        self._scalar, get_sim_time('ns'),
                        self._assert_count + self._deassert_count):
                    self._recv_queue.append(pkt)
                    if pkt.event == 'assert':
                        self._assert_count += 1
                    else:
                        self._deassert_count += 1
                    self.log.debug(f"{self.title}: {pkt}")
                    if self.callback:
                        self.callback(pkt)
            self._prev = cur

    async def wait_for_assert(self, index: Optional[int] = None,
                              timeout_ns: int = 10000) -> bool:
        """Await an assertion on this line. True if seen within the timeout.

        Returns immediately if the line is ALREADY asserted -- a level that
        went high before the call is still an assertion, and a test that
        waits for an edge it already missed hangs for the full timeout.
        """
        if self.is_asserted(index):
            return True
        start = get_sim_time('ns')
        while (get_sim_time('ns') - start) < timeout_ns:
            await RisingEdge(self.clock)
            if self.is_asserted(index):
                return True
        return False


class IRQMonitorGroup:
    """Several interrupt lines watched as one unit.

    The point of the group is the NEGATIVE assertion. A routing test wants to
    say "GPIO fired, so exactly these lines moved and no others" -- and the
    line that must NOT have moved (a cascade input, a neighbouring IRQ) is
    where the real bugs are. Per-line monitors alone make that awkward; here
    it is `lines_asserted()` against an expected set.
    """

    def __init__(self, entity, clock, lines: Dict[str, Optional[int]],
                 title: str = "IRQ", log: Optional[logging.Logger] = None):
        """
        Args:
            entity: DUT handle
            clock:  sampling clock
            lines:  {signal_name: width or None}; None auto-detects
            title:  label prefix for the per-line monitors
        """
        self.log = log or logging.getLogger(f"cocotb.irq.{title}")
        self._clock = clock
        self._running = False
        self._task = None
        self.monitors: Dict[str, IRQMonitor] = {}
        for name, width in lines.items():
            if not hasattr(entity, name):
                self.log.warning(f"{title}: DUT has no signal '{name}' -- skipped")
                continue
            self.monitors[name] = IRQMonitor(
                entity, f"{title}.{name}", name, clock, width=width, log=self.log)

    def start(self):
        """Start ONE sampling coroutine for the whole group.

        Not twelve. Each monitor's own start() would await RisingEdge
        independently; one shared wait and a loop over the monitors gives the
        same events for a twelfth of the scheduler traffic.
        """
        if self._running:
            return
        self._running = True
        for m in self.monitors.values():
            m._prev = _resolve(m.signal)
        self._task = cocotb.start_soon(self._sample_loop())

    def stop(self):
        self._running = False
        if self._task:
            self._task.kill()
            self._task = None

    async def _sample_loop(self):
        while self._running:
            await RisingEdge(self._clock)
            now = get_sim_time('ns')
            for m in self.monitors.values():
                m.sample(now)

    def clear(self):
        for m in self.monitors.values():
            m.clear()

    def lines_asserted(self) -> Set[str]:
        """Names of lines that saw at least one assert since the last clear()."""
        return {n for n, m in self.monitors.items() if m.assert_count > 0}

    def currently_asserted(self) -> Set[str]:
        """Names of lines whose level is high RIGHT NOW."""
        return {n for n, m in self.monitors.items() if m.is_asserted()}

    def all_events(self) -> List[IRQPacket]:
        """Every captured packet across the group, in time order."""
        out: List[IRQPacket] = []
        for m in self.monitors.values():
            out.extend(m.recv_queue)
        return sorted(out, key=lambda p: (p.time_ns, p.line))

    def expect_only(self, expected: Sequence[str]) -> tuple:
        """Check that exactly `expected` asserted. -> (ok, missing, unexpected).

        Returns the two difference sets rather than a bare bool so a failing
        test can say WHICH line was wrong, which is the whole diagnostic value.
        """
        want = set(expected)
        got = self.lines_asserted()
        return (got == want, sorted(want - got), sorted(got - want))

    def get_stats(self) -> Dict[str, Dict[str, Any]]:
        return {n: m.get_stats() for n, m in self.monitors.items()}
