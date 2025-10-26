#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Script: trim_wavedrom.py
# Purpose: Trim dead time from WaveJSON files for cleaner waveforms
#
# Usage: python3 bin/trim_wavedrom.py <input.json> [<output.json>]
#        If output not specified, input file is modified in place

"""
WaveDrom Waveform Trimming Script

Removes dead time (idle cycles) from the beginning and end of WaveJSON waveforms
while preserving a small buffer for context.

Features:
- Detects activity in all signals (changes from initial state)
- Preserves 2-3 cycle buffer at edges for clarity
- Handles clock signals (maintains pattern)
- Updates head/foot metadata
- In-place or output-to-file modes
"""

import json
import sys
import argparse
from pathlib import Path


def analyze_signal_activity(wave_string):
    """Analyze a wave string to find first and last activity

    Args:
        wave_string: WaveDrom wave notation string

    Returns:
        (first_active, last_active) - cycle indices, or (None, None) if no activity
    """
    if not wave_string or len(wave_string) == 0:
        return None, None

    first_char = wave_string[0]
    first_active = None
    last_active = None

    for i, char in enumerate(wave_string):
        # Activity = any change from initial character (except '.' for clocks)
        if char != first_char and char != '.':
            if first_active is None:
                first_active = i
            last_active = i
        # For clocks, transitions count as activity
        elif char == 'p' or char == 'n' or char == 'P' or char == 'N':
            if first_active is None:
                first_active = i
            last_active = i

    return first_active, last_active


def find_global_activity_range(signals, buffer_before=2, buffer_after=2):
    """Find the range of cycles containing meaningful activity across all signals

    Args:
        signals: List of signal dictionaries from WaveJSON
        buffer_before: Number of cycles to keep before first activity
        buffer_after: Number of cycles to keep after last activity

    Returns:
        (start_cycle, end_cycle) - inclusive range, or (0, 0) if no activity
    """
    global_first = None
    global_last = None

    for signal in signals:
        wave = signal.get('wave', '')
        if not wave:
            continue

        first, last = analyze_signal_activity(wave)

        if first is not None:
            if global_first is None or first < global_first:
                global_first = first
        if last is not None:
            if global_last is None or last > global_last:
                global_last = last

    # No activity found
    if global_first is None or global_last is None:
        return 0, 0

    # Apply buffer
    start = max(0, global_first - buffer_before)
    end = global_last + buffer_after

    return start, end


def trim_wave_string(wave, start, end):
    """Trim a wave string to the specified range

    Args:
        wave: WaveDrom wave notation string
        start: Starting cycle (inclusive)
        end: Ending cycle (inclusive)

    Returns:
        Trimmed wave string
    """
    if not wave or end < start:
        return wave

    # Ensure we don't exceed string bounds
    actual_end = min(end + 1, len(wave))

    return wave[start:actual_end]


def trim_node_string(node, start, end):
    """Trim a node annotation string to match trimmed wave

    Args:
        node: WaveDrom node notation string
        start: Starting cycle (inclusive)
        end: Ending cycle (inclusive)

    Returns:
        Trimmed node string
    """
    if not node:
        return node

    # Ensure we don't exceed string bounds
    actual_end = min(end + 1, len(node))

    return node[start:actual_end]


def trim_wavejson(input_path, output_path=None, buffer_before=2, buffer_after=2, verbose=False):
    """Trim dead time from a WaveJSON file

    Args:
        input_path: Path to input WaveJSON file
        output_path: Path to output file (None = overwrite input)
        buffer_before: Cycles to keep before first activity
        buffer_after: Cycles to keep after last activity
        verbose: Print detailed information

    Returns:
        True on success, False on failure
    """
    input_path = Path(input_path)

    if not input_path.exists():
        print(f"Error: Input file not found: {input_path}")
        return False

    # Read input JSON
    try:
        with open(input_path, 'r') as f:
            wavejson = json.load(f)
    except Exception as e:
        print(f"Error reading JSON: {e}")
        return False

    signals = wavejson.get('signal', [])
    if not signals:
        print("Warning: No signals found in WaveJSON")
        return False

    # Find activity range
    start, end = find_global_activity_range(signals, buffer_before, buffer_after)

    if start == 0 and end == 0:
        print("Warning: No activity detected in waveforms")
        return False

    # Calculate original length (from first signal)
    original_length = len(signals[0].get('wave', ''))
    trimmed_length = end - start + 1
    removed_before = start
    removed_after = original_length - end - 1

    if verbose:
        print(f"Original waveform length: {original_length} cycles")
        print(f"Activity range: cycle {start} to {end}")
        print(f"Removing {removed_before} cycles from beginning")
        print(f"Removing {removed_after} cycles from end")
        print(f"Trimmed waveform length: {trimmed_length} cycles")

    # Trim all signals
    for signal in signals:
        if 'wave' in signal:
            signal['wave'] = trim_wave_string(signal['wave'], start, end)

        # Trim node annotations if present
        if 'node' in signal:
            signal['node'] = trim_node_string(signal['node'], start, end)

        # Trim data arrays if present
        if 'data' in signal and isinstance(signal['data'], list):
            # Data arrays should align with wave length
            if len(signal['data']) > trimmed_length:
                signal['data'] = signal['data'][start:end+1]

    # Update metadata if present
    if 'foot' in wavejson:
        original_foot = wavejson['foot'].get('text', '')
        wavejson['foot']['text'] = f"{original_foot} | Trimmed: {trimmed_length} cycles"

    # Write output
    output_path = output_path or input_path
    try:
        with open(output_path, 'w') as f:
            json.dump(wavejson, f, indent=2)
        if verbose:
            print(f"✓ Trimmed waveform saved to: {output_path}")
        return True
    except Exception as e:
        print(f"Error writing output: {e}")
        return False


def main():
    parser = argparse.ArgumentParser(
        description='Trim dead time from WaveJSON waveform files',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Trim in place
  python3 bin/trim_wavedrom.py waveform.json

  # Trim to new file
  python3 bin/trim_wavedrom.py waveform.json trimmed.json

  # Custom buffers
  python3 bin/trim_wavedrom.py waveform.json -b 3 -a 5

  # Verbose output
  python3 bin/trim_wavedrom.py waveform.json -v
        """
    )

    parser.add_argument('input', help='Input WaveJSON file')
    parser.add_argument('output', nargs='?', help='Output file (default: overwrite input)')
    parser.add_argument('-b', '--buffer-before', type=int, default=2,
                       help='Cycles to keep before first activity (default: 2)')
    parser.add_argument('-a', '--buffer-after', type=int, default=2,
                       help='Cycles to keep after last activity (default: 2)')
    parser.add_argument('-v', '--verbose', action='store_true',
                       help='Verbose output')

    args = parser.parse_args()

    success = trim_wavejson(
        args.input,
        args.output,
        args.buffer_before,
        args.buffer_after,
        args.verbose
    )

    return 0 if success else 1


if __name__ == '__main__':
    sys.exit(main())
