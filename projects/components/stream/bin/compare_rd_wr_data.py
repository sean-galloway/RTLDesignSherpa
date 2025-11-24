#!/usr/bin/env python3
"""
Read/Write Data Comparison Tool for Asymmetric Bursts

Compares R (read) vs W (write) data beats from rdeng/wreng logs,
ignoring AR/AW transaction boundaries. This allows validation of
asymmetric burst configurations where rd_burst != wr_burst.

Example:
  - rd_burst=16, wr_burst=8
  - AR transactions: 16 beats each
  - AW transactions: 8 beats each
  - But R and W data should match beat-for-beat!

Usage:
    ./compare_rd_wr_data.py <logfile> [--channel N] [--output FILE]

The script extracts:
  - All R beats from rdeng interface (in timestamp order)
  - All W beats from wreng interface (in timestamp order)
  - Compares data content beat-by-beat
  - Reports matches, mismatches, and coverage statistics

Author: RTL Design Sherpa - STREAM Performance Team
Version: 1.0
"""

import sys
import re
import argparse
from dataclasses import dataclass
from typing import List, Optional


@dataclass
class DataBeat:
    """Generic data beat (R or W)"""
    timestamp: float
    data: str
    beat_type: str  # 'R' or 'W'
    channel: int = -1  # Channel ID from user field (W) or context (R)
    beat_index: int = 0  # Sequential beat number


class DataComparator:
    """Compare R and W data beats from log file"""

    def __init__(self, logfile: str, channel_filter: Optional[int] = None):
        self.logfile = logfile
        self.channel_filter = channel_filter
        self.r_beats: List[DataBeat] = []
        self.w_beats: List[DataBeat] = []

        # Compile regex patterns
        self.patterns = self._build_patterns()

    def _build_patterns(self):
        """Build regex patterns for R and W beats"""
        patterns = {}

        # R: Read Data beats from rdeng interface
        patterns['r_data'] = re.compile(
            r'Master\(R_Master.*rdeng.*Transaction.*at\s+(\d+\.\d+)ns:.*'
            r'last=(Last|Not Last).*data=0x([0-9A-Fa-f]+)',
            re.IGNORECASE
        )

        # W: Write Data beats from wreng interface
        patterns['w_data'] = re.compile(
            r'GAXIMonitorBase\(W_.*wreng.*Transaction at\s+(\d+\.\d+)ns:.*'
            r'user=0[xb]([0-9A-Fa-f]+).*last=(Last|Not Last).*data=0x([0-9A-Fa-f]+)',
            re.IGNORECASE
        )

        return patterns

    def extract_beats(self):
        """Extract all R and W data beats from log file"""
        print(f"Extracting data beats from {self.logfile}...")

        with open(self.logfile, 'r') as f:
            for line in f:
                self._parse_r_beat(line)
                self._parse_w_beat(line)

        # Sort by timestamp
        self.r_beats.sort(key=lambda b: b.timestamp)
        self.w_beats.sort(key=lambda b: b.timestamp)

        # Assign beat indices
        for i, beat in enumerate(self.r_beats):
            beat.beat_index = i
        for i, beat in enumerate(self.w_beats):
            beat.beat_index = i

        print(f"  R beats extracted: {len(self.r_beats)}")
        print(f"  W beats extracted: {len(self.w_beats)}")

        # Filter by channel if specified
        if self.channel_filter is not None:
            self.r_beats = [b for b in self.r_beats if b.channel == self.channel_filter]
            self.w_beats = [b for b in self.w_beats if b.channel == self.channel_filter]
            print(f"  After channel {self.channel_filter} filter: R={len(self.r_beats)}, W={len(self.w_beats)}")

    def _parse_r_beat(self, line: str):
        """Parse R beat from rdeng log line"""
        match = self.patterns['r_data'].search(line)
        if match:
            timestamp, last_str, data = match.groups()

            # Try to extract channel from context (if present in line)
            # Format: "CHANNEL N descriptor"
            channel = -1
            channel_match = re.search(r'CHANNEL\s+(\d+)', line, re.IGNORECASE)
            if channel_match:
                channel = int(channel_match.group(1))

            beat = DataBeat(
                timestamp=float(timestamp),
                data=data.upper(),  # Normalize to uppercase
                beat_type='R',
                channel=channel
            )
            self.r_beats.append(beat)

    def _parse_w_beat(self, line: str):
        """Parse W beat from wreng log line"""
        match = self.patterns['w_data'].search(line)
        if match:
            timestamp, user_hex, last_str, data = match.groups()

            # Parse user field (channel ID)
            # Line contains either "user=0xN" or "user=0bN"
            user_match = re.search(r'user=(0[xb][0-9A-Fa-f]+)', line, re.IGNORECASE)
            if user_match:
                user_str = user_match.group(1)
                channel = int(user_str, 0)  # base=0 means auto-detect from prefix
            else:
                channel = int(user_hex, 16)

            beat = DataBeat(
                timestamp=float(timestamp),
                data=data.upper(),  # Normalize to uppercase
                beat_type='W',
                channel=channel
            )
            self.w_beats.append(beat)

    def compare_beats(self, output_file: Optional[str] = None):
        """Compare R vs W beats and generate report"""

        # Open output file if specified
        if output_file:
            f = open(output_file, 'w')
        else:
            f = sys.stdout

        try:
            self._write_report(f)
        finally:
            if output_file:
                f.close()
                print(f"\nComparison report written to: {output_file}")

    def _write_report(self, f):
        """Write comparison report to file/stdout"""

        # Header
        f.write("=" * 80 + "\n")
        f.write("Read/Write Data Beat Comparison Report\n")
        f.write("=" * 80 + "\n\n")

        f.write(f"Log file: {self.logfile}\n")
        if self.channel_filter is not None:
            f.write(f"Channel filter: {self.channel_filter}\n")
        f.write(f"R beats: {len(self.r_beats)}\n")
        f.write(f"W beats: {len(self.w_beats)}\n\n")

        # Check for count mismatch
        if len(self.r_beats) != len(self.w_beats):
            f.write("⚠️  WARNING: Beat count mismatch!\n")
            f.write(f"   R beats: {len(self.r_beats)}\n")
            f.write(f"   W beats: {len(self.w_beats)}\n")
            f.write(f"   Difference: {abs(len(self.r_beats) - len(self.w_beats))}\n\n")

        # Compare beat-by-beat
        f.write("-" * 80 + "\n")
        f.write("Beat-by-Beat Comparison\n")
        f.write("-" * 80 + "\n\n")

        matches = 0
        mismatches = 0
        mismatch_details = []

        min_beats = min(len(self.r_beats), len(self.w_beats))
        for i in range(min_beats):
            r_beat = self.r_beats[i]
            w_beat = self.w_beats[i]

            if r_beat.data == w_beat.data:
                matches += 1
                # Only show first 10 matches to avoid clutter
                if matches <= 10:
                    f.write(f"Beat {i:4d}: ✓ MATCH\n")
                    f.write(f"  R[{r_beat.timestamp:7.1f}ns]: 0x{r_beat.data}\n")
                    f.write(f"  W[{w_beat.timestamp:7.1f}ns]: 0x{w_beat.data}\n\n")
                elif matches == 11:
                    f.write(f"... (showing first 10 matches, {min_beats - 10} more beats to compare)\n\n")
            else:
                mismatches += 1
                mismatch_details.append((i, r_beat, w_beat))
                f.write(f"Beat {i:4d}: ✗ MISMATCH\n")
                f.write(f"  R[{r_beat.timestamp:7.1f}ns]: 0x{r_beat.data}\n")
                f.write(f"  W[{w_beat.timestamp:7.1f}ns]: 0x{w_beat.data}\n\n")

        # Summary
        f.write("=" * 80 + "\n")
        f.write("Summary\n")
        f.write("=" * 80 + "\n\n")

        f.write(f"Total beats compared: {min_beats}\n")
        f.write(f"Matches:   {matches} ({100*matches/min_beats:.1f}%)\n" if min_beats > 0 else "Matches:   0 (0.0%)\n")
        f.write(f"Mismatches: {mismatches} ({100*mismatches/min_beats:.1f}%)\n\n" if min_beats > 0 else "Mismatches: 0 (0.0%)\n\n")

        # Extra beats
        if len(self.r_beats) > min_beats:
            f.write(f"Extra R beats (not matched): {len(self.r_beats) - min_beats}\n")
            for i in range(min_beats, min(min_beats + 5, len(self.r_beats))):
                beat = self.r_beats[i]
                f.write(f"  Beat {i}: R[{beat.timestamp:7.1f}ns] = 0x{beat.data}\n")
            if len(self.r_beats) > min_beats + 5:
                f.write(f"  ... ({len(self.r_beats) - min_beats - 5} more)\n")
            f.write("\n")

        if len(self.w_beats) > min_beats:
            f.write(f"Extra W beats (not matched): {len(self.w_beats) - min_beats}\n")
            for i in range(min_beats, min(min_beats + 5, len(self.w_beats))):
                beat = self.w_beats[i]
                f.write(f"  Beat {i}: W[{beat.timestamp:7.1f}ns] = 0x{beat.data}\n")
            if len(self.w_beats) > min_beats + 5:
                f.write(f"  ... ({len(self.w_beats) - min_beats - 5} more)\n")
            f.write("\n")

        # Result
        if mismatches == 0 and len(self.r_beats) == len(self.w_beats):
            f.write("✓ PASS: All beats match!\n")
        else:
            f.write("✗ FAIL: Data mismatches detected\n")
            if len(mismatch_details) > 0:
                f.write(f"\nFirst mismatch at beat {mismatch_details[0][0]}\n")


def main():
    parser = argparse.ArgumentParser(
        description='Compare R (read) vs W (write) data beats for asymmetric burst validation',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s logs/test_params21.log
  %(prog)s logs/test_params21.log --channel 0
  %(prog)s logs/test_params21.log --output comparison_report.txt
        """
    )

    parser.add_argument('logfile', help='Path to CocoTB log file (contains both rdeng and wreng)')
    parser.add_argument('--channel', type=int, metavar='N',
                       help='Filter to show only specific channel')
    parser.add_argument('--output', '-o', metavar='FILE',
                       help='Write report to file instead of stdout')

    args = parser.parse_args()

    # Create comparator
    comparator = DataComparator(
        logfile=args.logfile,
        channel_filter=args.channel
    )

    # Extract beats
    comparator.extract_beats()

    # Compare and report
    comparator.compare_beats(output_file=args.output)


if __name__ == '__main__':
    main()
