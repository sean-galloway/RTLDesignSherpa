#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: SignalInfo
# Purpose: Signal Naming Conflict Auditor
#
# Documentation: rtl/common/PRD.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2025-10-18

"""
Signal Naming Conflict Auditor

Scans SystemVerilog RTL files and markdown documentation to detect potential
signal naming conflicts that could confuse AXI4/GAXI factory functions.

The AXI4 factories use pattern matching with prefixes like "desc_" and will
find BOTH internal signals and external AXI ports if naming overlaps.

Usage:
    ./bin/audit_signal_naming_conflicts.py rtl/rapids/rapids_macro/scheduler_group.sv
    ./bin/audit_signal_naming_conflicts.py rtl/rapids/          # Scan directory
    ./bin/audit_signal_naming_conflicts.py --markdown rtl/    # Check markdown docs

Examples of Conflicts Detected:
    Internal:  desc_valid, desc_ready       (simple valid/ready handshake)
    External:  desc_ar_valid, desc_ar_ready (AXI AR channel)
    Conflict:  Both match prefix "desc_" + pattern "*valid"

Author: Claude Code / RTL Design Sherpa Project
Date: 2025-10-15
"""

import argparse
import re
import sys
from pathlib import Path
from typing import List, Dict, Set, Tuple
from collections import defaultdict
from dataclasses import dataclass, field


@dataclass
class SignalInfo:
    """Information about a signal"""
    name: str
    file: Path
    line_number: int
    direction: str  # 'input', 'output', 'inout', 'wire', 'internal'
    context: str    # Line of code where signal appears

    def __hash__(self):
        return hash(self.name)


@dataclass
class ConflictReport:
    """Report of a potential conflict"""
    prefix: str
    internal_signals: List[SignalInfo] = field(default_factory=list)
    external_signals: List[SignalInfo] = field(default_factory=list)
    severity: str = "MEDIUM"  # LOW, MEDIUM, HIGH, CRITICAL

    def has_conflict(self) -> bool:
        """Check if this represents an actual conflict"""
        return len(self.internal_signals) > 0 and len(self.external_signals) > 0


class SignalNamingAuditor:
    """Audit SystemVerilog files for signal naming conflicts"""

    # AXI4 channel patterns that might conflict with internal signals
    AXI4_PATTERNS = [
        'ar_valid', 'ar_ready',  # AR channel
        'r_valid', 'r_ready',    # R channel
        'aw_valid', 'aw_ready',  # AW channel
        'w_valid', 'w_ready',    # W channel
        'b_valid', 'b_ready',    # B channel
    ]

    # Simple internal patterns that might conflict
    INTERNAL_PATTERNS = [
        '_valid', '_ready',      # Generic handshake
        'valid', 'ready',        # Without underscore
    ]

    # Common prefixes that might have conflicts
    COMMON_PREFIXES = [
        'desc', 'prog', 'data', 'cmd', 'resp',
        'm_axi', 's_axi', 'axi',
    ]

    def __init__(self, verbose: bool = False):
        self.verbose = verbose
        self.signals_by_file: Dict[Path, List[SignalInfo]] = {}
        self.conflicts: List[ConflictReport] = []

    def scan_file(self, file_path: Path) -> List[SignalInfo]:
        """Scan a single SystemVerilog file for signal declarations"""
        signals = []

        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                lines = f.readlines()

            for line_num, line in enumerate(lines, 1):
                # Skip comments
                if line.strip().startswith('//'):
                    continue

                # Look for port declarations
                port_match = re.match(
                    r'\s*(input|output|inout)\s+(?:logic|wire|reg)?\s*(?:\[.*?\])?\s+(\w+)',
                    line
                )
                if port_match:
                    direction, signal_name = port_match.groups()
                    signals.append(SignalInfo(
                        name=signal_name,
                        file=file_path,
                        line_number=line_num,
                        direction=direction,
                        context=line.strip()
                    ))

                # Look for wire/logic declarations (internal signals)
                wire_match = re.match(
                    r'\s*(logic|wire|reg)\s+(?:\[.*?\])?\s+(\w+)',
                    line
                )
                if wire_match:
                    signal_type, signal_name = wire_match.groups()
                    signals.append(SignalInfo(
                        name=signal_name,
                        file=file_path,
                        line_number=line_num,
                        direction='internal',
                        context=line.strip()
                    ))

        except Exception as e:
            print(f"Error reading {file_path}: {e}", file=sys.stderr)

        return signals

    def scan_directory(self, dir_path: Path) -> None:
        """Recursively scan directory for SystemVerilog files"""
        sv_files = list(dir_path.rglob('*.sv'))
        v_files = list(dir_path.rglob('*.v'))
        all_files = sv_files + v_files

        print(f"Scanning {len(all_files)} SystemVerilog files in {dir_path}...")

        for file_path in all_files:
            signals = self.scan_file(file_path)
            if signals:
                self.signals_by_file[file_path] = signals
                if self.verbose:
                    print(f"  {file_path.name}: {len(signals)} signals")

    def detect_conflicts(self) -> List[ConflictReport]:
        """Detect potential conflicts in scanned signals"""
        self.conflicts = []

        for file_path, signals in self.signals_by_file.items():
            # Group signals by potential prefix
            for prefix in self.COMMON_PREFIXES:
                # Find all signals that start with this prefix
                matching_signals = [s for s in signals if s.name.startswith(prefix)]

                if len(matching_signals) < 2:
                    continue  # Need at least 2 signals to have a conflict

                # Separate internal vs external (port) signals
                internal = [s for s in matching_signals if s.direction == 'internal']
                external = [s for s in matching_signals if s.direction in ('input', 'output', 'inout')]

                # Check for potential pattern conflicts
                for internal_sig in internal:
                    for external_sig in external:
                        if self._could_conflict(internal_sig.name, external_sig.name, prefix):
                            # Create or update conflict report
                            conflict = self._find_or_create_conflict(prefix, file_path)
                            if internal_sig not in conflict.internal_signals:
                                conflict.internal_signals.append(internal_sig)
                            if external_sig not in conflict.external_signals:
                                conflict.external_signals.append(external_sig)

        # Calculate severity for each conflict
        for conflict in self.conflicts:
            conflict.severity = self._calculate_severity(conflict)

        return [c for c in self.conflicts if c.has_conflict()]

    def _could_conflict(self, internal_name: str, external_name: str, prefix: str) -> bool:
        """Check if two signal names could conflict during pattern matching"""
        # Remove prefix from both names
        internal_suffix = internal_name[len(prefix):]
        external_suffix = external_name[len(prefix):]

        # Check if internal matches simple pattern while external matches AXI pattern
        for simple_pattern in self.INTERNAL_PATTERNS:
            if internal_suffix.endswith(simple_pattern) or internal_suffix == simple_pattern.lstrip('_'):
                for axi_pattern in self.AXI4_PATTERNS:
                    if axi_pattern in external_suffix:
                        # Both match *valid or *ready patterns - potential conflict!
                        return True

        return False

    def _find_or_create_conflict(self, prefix: str, file_path: Path) -> ConflictReport:
        """Find existing conflict report or create new one"""
        for conflict in self.conflicts:
            if conflict.prefix == prefix:
                return conflict

        new_conflict = ConflictReport(prefix=prefix)
        self.conflicts.append(new_conflict)
        return new_conflict

    def _calculate_severity(self, conflict: ConflictReport) -> str:
        """Calculate severity of a conflict"""
        num_internal = len(conflict.internal_signals)
        num_external = len(conflict.external_signals)

        # Check if external signals include multiple AXI channels
        axi_channels = set()
        for sig in conflict.external_signals:
            for channel in ['ar_', 'r_', 'aw_', 'w_', 'b_']:
                if channel in sig.name:
                    axi_channels.add(channel)

        if len(axi_channels) >= 2:
            return "HIGH"  # Multiple AXI channels affected
        elif num_internal >= 2 and num_external >= 2:
            return "HIGH"  # Many signals involved
        elif num_internal >= 1 and num_external >= 1:
            return "MEDIUM"  # At least one of each
        else:
            return "LOW"

    def print_report(self) -> None:
        """Print conflict report to console"""
        if not self.conflicts:
            print("\n✅ No signal naming conflicts detected!")
            return

        print(f"\n⚠️  Found {len(self.conflicts)} potential signal naming conflicts:\n")
        print("=" * 80)

        for idx, conflict in enumerate(self.conflicts, 1):
            print(f"\nConflict #{idx}: Prefix '{conflict.prefix}' [{conflict.severity}]")
            print("-" * 80)

            print(f"\nInternal Signals ({len(conflict.internal_signals)}):")
            for sig in conflict.internal_signals:
                print(f"  - {sig.name:<30} [{sig.file.name}:{sig.line_number}]")
                if self.verbose:
                    print(f"    {sig.context}")

            print(f"\nExternal Signals ({len(conflict.external_signals)}):")
            for sig in conflict.external_signals:
                print(f"  + {sig.name:<30} [{sig.file.name}:{sig.line_number}] ({sig.direction})")
                if self.verbose:
                    print(f"    {sig.context}")

            print(f"\n📋 Impact:")
            print(f"   When using AXI factory with prefix='{conflict.prefix}_', the factory will find")
            print(f"   BOTH internal and external signals, causing initialization to fail.")

            print(f"\n💡 Solutions:")
            print(f"   1. Rename internal signals: {conflict.internal_signals[0].name} → {conflict.internal_signals[0].name}_to_sched")
            print(f"   2. Use explicit signal_map parameter in factory call")
            print(f"   3. Test at higher integration level where internal signals are hidden")

        print("\n" + "=" * 80)
        print(f"\nTotal conflicts: {len(self.conflicts)}")
        print(f"  HIGH:   {sum(1 for c in self.conflicts if c.severity == 'HIGH')}")
        print(f"  MEDIUM: {sum(1 for c in self.conflicts if c.severity == 'MEDIUM')}")
        print(f"  LOW:    {sum(1 for c in self.conflicts if c.severity == 'LOW')}")

    def print_markdown_report(self, output_file: Path) -> None:
        """Generate markdown report of conflicts"""
        if not self.conflicts:
            return

        with open(output_file, 'w') as f:
            f.write("# Signal Naming Conflict Report\n\n")
            f.write(f"**Generated:** {Path(__file__).name}\n")
            f.write(f"**Conflicts Found:** {len(self.conflicts)}\n\n")
            f.write("---\n\n")

            for idx, conflict in enumerate(self.conflicts, 1):
                f.write(f"## Conflict #{idx}: Prefix `{conflict.prefix}` [{conflict.severity}]\n\n")

                f.write("### Internal Signals\n\n")
                for sig in conflict.internal_signals:
                    f.write(f"- `{sig.name}` - {sig.file.name}:{sig.line_number}\n")
                    f.write(f"  ```systemverilog\n  {sig.context}\n  ```\n")

                f.write("\n### External Signals\n\n")
                for sig in conflict.external_signals:
                    f.write(f"- `{sig.name}` ({sig.direction}) - {sig.file.name}:{sig.line_number}\n")
                    f.write(f"  ```systemverilog\n  {sig.context}\n  ```\n")

                f.write("\n### Impact\n\n")
                f.write(f"When using AXI factory with `prefix=\"{conflict.prefix}_\"`, the factory ")
                f.write("will find BOTH internal and external signals, causing initialization to fail.\n\n")

                f.write("### Recommended Solutions\n\n")
                f.write(f"1. **Rename internal signals:** `{conflict.internal_signals[0].name}` → ")
                f.write(f"`{conflict.internal_signals[0].name}_to_sched`\n")
                f.write("2. **Use explicit signal_map** parameter in factory call\n")
                f.write("3. **Test at higher integration level** where internal signals are hidden\n\n")
                f.write("---\n\n")

        print(f"\n📄 Markdown report written to: {output_file}")


def main():
    parser = argparse.ArgumentParser(
        description="Audit SystemVerilog files for signal naming conflicts",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Scan single file
  %(prog)s rtl/rapids/rapids_macro/scheduler_group.sv

  # Scan directory
  %(prog)s rtl/rapids/

  # Generate markdown report
  %(prog)s rtl/rapids/ --markdown rtl/rapids/signal_conflicts.md

  # Verbose output
  %(prog)s rtl/rapids/ -v
        """
    )

    parser.add_argument('path', type=Path,
                        help='SystemVerilog file or directory to audit')
    parser.add_argument('-v', '--verbose', action='store_true',
                        help='Enable verbose output')
    parser.add_argument('--markdown', type=Path, metavar='OUTPUT',
                        help='Generate markdown report to specified file')

    args = parser.parse_args()

    # Validate path
    if not args.path.exists():
        print(f"Error: Path '{args.path}' does not exist", file=sys.stderr)
        sys.exit(1)

    # Create auditor
    auditor = SignalNamingAuditor(verbose=args.verbose)

    # Scan path
    if args.path.is_file():
        signals = auditor.scan_file(args.path)
        auditor.signals_by_file[args.path] = signals
        print(f"Scanned {args.path.name}: {len(signals)} signals")
    else:
        auditor.scan_directory(args.path)

    # Detect conflicts
    conflicts = auditor.detect_conflicts()

    # Print report
    auditor.print_report()

    # Generate markdown if requested
    if args.markdown:
        auditor.print_markdown_report(args.markdown)

    # Exit with error code if conflicts found
    if conflicts:
        sys.exit(1)
    else:
        sys.exit(0)


if __name__ == '__main__':
    main()
