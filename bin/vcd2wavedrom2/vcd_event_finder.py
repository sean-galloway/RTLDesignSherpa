#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: VCD Event Finder
# Purpose: Parse VCD files to find specific events and suggest time windows
#          for wavedrom generation
#
# Author: Claude (AI Assistant)
# Created: 2025-12-06

"""
VCD Event Finder - Helper for vcd2wavedrom2

This script parses VCD files to find specific signal events and suggests
appropriate time windows for wavedrom generation.

Usage:
    python vcd_event_finder.py -i dump.vcd --find-transitions valid
    python vcd_event_finder.py -i dump.vcd --find-pattern "valid.*ready"
    python vcd_event_finder.py -i dump.vcd --list-signals
    python vcd_event_finder.py -i dump.vcd --find-handshakes valid ready
    python vcd_event_finder.py -i dump.vcd --summary
"""

import argparse
import re
import sys
from dataclasses import dataclass
from typing import Optional
from vcdvcd import VCDVCD


@dataclass
class SignalEvent:
    """Represents a signal transition event"""
    signal_name: str
    time: int
    old_value: str
    new_value: str

    def __str__(self):
        return f"{self.time}: {self.signal_name} {self.old_value} -> {self.new_value}"


@dataclass
class TimeWindow:
    """Represents a suggested time window for wavedrom"""
    start_ns: int
    end_ns: int
    description: str
    events: list

    def __str__(self):
        return f"{self.start_ns}ns - {self.end_ns}ns: {self.description}"


class VCDEventFinder:
    """Parse VCD files and find interesting events for wavedrom generation"""

    def __init__(self, vcd_path: str):
        """Initialize with VCD file path"""
        self.vcd_path = vcd_path
        self.vcd = VCDVCD(vcd_path)
        self.timescale = self.vcd.timescale
        self.timescale_ns = self._get_timescale_ns()

    def _get_timescale_ns(self) -> float:
        """Convert timescale to nanoseconds multiplier"""
        unit = self.timescale['unit']
        magnitude = float(self.timescale['magnitude'])  # Convert Decimal to float

        unit_to_ns = {
            'fs': 1e-6,
            'ps': 1e-3,
            'ns': 1,
            'us': 1e3,
            'ms': 1e6,
            's': 1e9
        }

        return magnitude * unit_to_ns.get(unit, 1)

    def time_to_ns(self, vcd_time: int) -> float:
        """Convert VCD time to nanoseconds"""
        return vcd_time * self.timescale_ns

    def ns_to_vcd_time(self, ns: float) -> int:
        """Convert nanoseconds to VCD time"""
        return int(ns / self.timescale_ns)

    def list_signals(self, pattern: Optional[str] = None) -> list:
        """List all signals in VCD, optionally filtered by pattern"""
        signals = []
        for signal_id in self.vcd.data:
            if signal_id == '$end':
                continue
            for ref in self.vcd.data[signal_id].references:
                if pattern is None or re.search(pattern, ref, re.IGNORECASE):
                    size = self.vcd.data[signal_id].size
                    signals.append((ref, size))
        return sorted(signals, key=lambda x: x[0])

    def get_signal_transitions(self, signal_pattern: str) -> list:
        """Get all transitions for signals matching pattern"""
        events = []
        for signal_id in self.vcd.data:
            if signal_id == '$end':
                continue
            for ref in self.vcd.data[signal_id].references:
                if re.search(signal_pattern, ref, re.IGNORECASE):
                    tv_pairs = self.vcd.data[signal_id].tv
                    prev_value = None
                    for time, value in tv_pairs:
                        if prev_value is not None and prev_value != value:
                            events.append(SignalEvent(
                                signal_name=ref,
                                time=time,
                                old_value=prev_value,
                                new_value=value
                            ))
                        prev_value = value
        return sorted(events, key=lambda x: x.time)

    def find_rising_edges(self, signal_pattern: str) -> list:
        """Find all rising edges (0->1) for signals matching pattern"""
        transitions = self.get_signal_transitions(signal_pattern)
        return [e for e in transitions if e.old_value == '0' and e.new_value == '1']

    def find_falling_edges(self, signal_pattern: str) -> list:
        """Find all falling edges (1->0) for signals matching pattern"""
        transitions = self.get_signal_transitions(signal_pattern)
        return [e for e in transitions if e.old_value == '1' and e.new_value == '0']

    def find_handshakes(self, valid_pattern: str, ready_pattern: str,
                        window_before_ns: int = 50, window_after_ns: int = 100) -> list:
        """
        Find valid/ready handshake events and suggest time windows.

        A handshake occurs when both valid and ready are high simultaneously.
        """
        windows = []

        # Get all valid rising edges
        valid_rises = self.find_rising_edges(valid_pattern)

        for valid_event in valid_rises:
            # Look for ready signal activity near this time
            time_ns = self.time_to_ns(valid_event.time)

            # Suggest a window around this event
            start_ns = max(0, time_ns - window_before_ns)
            end_ns = time_ns + window_after_ns

            windows.append(TimeWindow(
                start_ns=int(start_ns),
                end_ns=int(end_ns),
                description=f"Handshake: {valid_event.signal_name}",
                events=[valid_event]
            ))

        return windows

    def find_first_activity(self, signal_pattern: str,
                           window_before_ns: int = 20,
                           window_after_ns: int = 200) -> Optional[TimeWindow]:
        """Find the first activity on signals matching pattern"""
        transitions = self.get_signal_transitions(signal_pattern)
        if not transitions:
            return None

        first = transitions[0]
        time_ns = self.time_to_ns(first.time)

        return TimeWindow(
            start_ns=max(0, int(time_ns - window_before_ns)),
            end_ns=int(time_ns + window_after_ns),
            description=f"First activity: {first.signal_name}",
            events=[first]
        )

    def get_summary(self) -> dict:
        """Get summary of VCD file"""
        signals = self.list_signals()

        # Find max time
        max_time = 0
        for signal_id in self.vcd.data:
            if signal_id == '$end':
                continue
            if self.vcd.data[signal_id].tv:
                last_time = self.vcd.data[signal_id].tv[-1][0]
                max_time = max(max_time, last_time)

        # Categorize signals
        clocks = [s for s, _ in signals if 'clk' in s.lower()]
        resets = [s for s, _ in signals if 'rst' in s.lower() or 'reset' in s.lower()]
        valids = [s for s, _ in signals if 'valid' in s.lower()]
        readys = [s for s, _ in signals if 'ready' in s.lower()]

        return {
            'file': self.vcd_path,
            'timescale': f"{self.timescale['magnitude']}{self.timescale['unit']}",
            'total_signals': len(signals),
            'duration_ns': self.time_to_ns(max_time),
            'clocks': clocks,
            'resets': resets,
            'valid_signals': valids,
            'ready_signals': readys
        }

    def suggest_windows(self,
                        valid_pattern: str = r'valid',
                        ready_pattern: str = r'ready',
                        max_windows: int = 5) -> list:
        """
        Automatically suggest interesting time windows for wavedrom.

        Looks for:
        1. First activity after reset
        2. Handshake events (valid & ready)
        3. Error conditions
        """
        windows = []

        # Find reset deassertion
        reset_events = self.find_rising_edges(r'rst_n|resetn|rstn')
        if reset_events:
            reset_time_ns = self.time_to_ns(reset_events[0].time)
            windows.append(TimeWindow(
                start_ns=max(0, int(reset_time_ns - 20)),
                end_ns=int(reset_time_ns + 100),
                description="Reset deassertion",
                events=[reset_events[0]]
            ))

        # Find handshakes
        handshakes = self.find_handshakes(valid_pattern, ready_pattern)
        windows.extend(handshakes[:max_windows])

        # Sort by time and limit
        windows = sorted(windows, key=lambda w: w.start_ns)[:max_windows]

        return windows


def main():
    parser = argparse.ArgumentParser(
        description='Find events in VCD files for wavedrom generation',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # List all signals
  python vcd_event_finder.py -i dump.vcd --list-signals

  # Find signals matching pattern
  python vcd_event_finder.py -i dump.vcd --list-signals --pattern "apb.*valid"

  # Find transitions on a signal
  python vcd_event_finder.py -i dump.vcd --find-transitions "apb_cmd_valid"

  # Find handshakes
  python vcd_event_finder.py -i dump.vcd --find-handshakes apb_cmd_valid apb_cmd_ready

  # Get suggested time windows
  python vcd_event_finder.py -i dump.vcd --suggest-windows

  # Get VCD summary
  python vcd_event_finder.py -i dump.vcd --summary
"""
    )

    parser.add_argument('-i', '--input', required=True, help='Input VCD file')
    parser.add_argument('--list-signals', action='store_true', help='List all signals')
    parser.add_argument('--pattern', help='Filter pattern for list-signals')
    parser.add_argument('--find-transitions', metavar='PATTERN', help='Find transitions matching pattern')
    parser.add_argument('--find-rising', metavar='PATTERN', help='Find rising edges')
    parser.add_argument('--find-falling', metavar='PATTERN', help='Find falling edges')
    parser.add_argument('--find-handshakes', nargs=2, metavar=('VALID', 'READY'),
                        help='Find valid/ready handshakes')
    parser.add_argument('--suggest-windows', action='store_true',
                        help='Suggest time windows for wavedrom')
    parser.add_argument('--summary', action='store_true', help='Show VCD summary')
    parser.add_argument('--max-events', type=int, default=20, help='Max events to show')

    args = parser.parse_args()

    finder = VCDEventFinder(args.input)

    if args.summary:
        summary = finder.get_summary()
        print(f"\n{'='*60}")
        print(f"VCD Summary: {summary['file']}")
        print(f"{'='*60}")
        print(f"Timescale:     {summary['timescale']}")
        print(f"Duration:      {summary['duration_ns']:.1f} ns")
        print(f"Total signals: {summary['total_signals']}")
        print(f"\nClocks ({len(summary['clocks'])}):")
        for c in summary['clocks'][:5]:
            print(f"  - {c}")
        print(f"\nResets ({len(summary['resets'])}):")
        for r in summary['resets'][:5]:
            print(f"  - {r}")
        print(f"\nValid signals ({len(summary['valid_signals'])}):")
        for v in summary['valid_signals'][:10]:
            print(f"  - {v}")
        print(f"\nReady signals ({len(summary['ready_signals'])}):")
        for r in summary['ready_signals'][:10]:
            print(f"  - {r}")

    if args.list_signals:
        signals = finder.list_signals(args.pattern)
        print(f"\nSignals ({len(signals)}):")
        for name, size in signals:
            print(f"  [{int(size):3d}] {name}")

    if args.find_transitions:
        events = finder.get_signal_transitions(args.find_transitions)
        print(f"\nTransitions matching '{args.find_transitions}' ({len(events)} total):")
        for e in events[:args.max_events]:
            time_ns = finder.time_to_ns(e.time)
            print(f"  {time_ns:10.1f}ns: {e.signal_name} {e.old_value} -> {e.new_value}")
        if len(events) > args.max_events:
            print(f"  ... and {len(events) - args.max_events} more")

    if args.find_rising:
        events = finder.find_rising_edges(args.find_rising)
        print(f"\nRising edges matching '{args.find_rising}' ({len(events)} total):")
        for e in events[:args.max_events]:
            time_ns = finder.time_to_ns(e.time)
            print(f"  {time_ns:10.1f}ns: {e.signal_name}")
        if len(events) > args.max_events:
            print(f"  ... and {len(events) - args.max_events} more")

    if args.find_falling:
        events = finder.find_falling_edges(args.find_falling)
        print(f"\nFalling edges matching '{args.find_falling}' ({len(events)} total):")
        for e in events[:args.max_events]:
            time_ns = finder.time_to_ns(e.time)
            print(f"  {time_ns:10.1f}ns: {e.signal_name}")
        if len(events) > args.max_events:
            print(f"  ... and {len(events) - args.max_events} more")

    if args.find_handshakes:
        valid_pat, ready_pat = args.find_handshakes
        windows = finder.find_handshakes(valid_pat, ready_pat)
        print(f"\nHandshake windows for '{valid_pat}'/'{ready_pat}' ({len(windows)} found):")
        for w in windows[:args.max_events]:
            print(f"  {w.start_ns}ns - {w.end_ns}ns: {w.description}")
            print(f"    vcd2wavedrom2 args: -s {w.start_ns}ns -e {w.end_ns}ns")

    if args.suggest_windows:
        windows = finder.suggest_windows()
        print(f"\nSuggested time windows for wavedrom:")
        print(f"{'='*60}")
        for i, w in enumerate(windows, 1):
            print(f"\n{i}. {w.description}")
            print(f"   Time: {w.start_ns}ns - {w.end_ns}ns")
            print(f"   vcd2wavedrom2 args: -s {w.start_ns}ns -e {w.end_ns}ns")


if __name__ == '__main__':
    main()
