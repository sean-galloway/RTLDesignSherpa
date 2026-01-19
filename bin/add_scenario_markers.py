#!/usr/bin/env python3
"""
Add scenario markers to Rapids test TB classes for testplan traceability.

This script automates adding scenario markers to test methods in TB classes.
"""

import re
import sys
from pathlib import Path

# Mapping of TB file to scenario markers
SCENARIO_MAPPINGS = {
    'descriptor_engine_tb.py': [
        ('test_descriptor_chaining', '=== Scenario DESC-04: Backpressure handling ===\n        self.log.info("=== Scenario DESC-06: Mixed APB/AXI operations ===")'),
        ('test_address_range_validation', '=== Scenario DESC-05: Error handling ==='),
        ('test_channel_reset', '=== Scenario DESC-04: Backpressure handling ==='),
        ('test_monitor_bus_events', '=== Scenario DESC-02: AXI descriptor fetch ==='),
        ('test_invalid_descriptor', '=== Scenario DESC-05: Error handling ==='),
        # Note: DESC-07 (Rapid descriptor submission) is covered by parameterized num_descriptors in basic_flow
    ],
    'alloc_ctrl_beats_tb.py': [
        ('test_basic_alloc_drain', '=== Scenario ALLOC-01: Basic alloc/drain cycle ==='),
        ('test_full_detection', '=== Scenario ALLOC-02: Full detection ==='),
        ('test_empty_detection', '=== Scenario ALLOC-03: Empty detection ==='),
        ('test_variable_size_alloc', '=== Scenario ALLOC-04: Variable size allocation ==='),
        ('test_stress_rapid_operations', '=== Scenario ALLOC-05: Stress rapid operations ==='),
    ],
    'drain_ctrl_beats_tb.py': [
        ('test_basic_write_drain', '=== Scenario DRAIN-01: Basic drain operation ==='),
        ('test_empty_detection', '=== Scenario DRAIN-02: Empty detection ==='),
        ('test_almost_empty', '=== Scenario DRAIN-03: Almost empty detection ==='),
        ('test_rapid_drain', '=== Scenario DRAIN-04: Rapid drain operations ==='),
        ('test_drain_backpressure', '=== Scenario DRAIN-05: Drain with backpressure ==='),
    ],
    'latency_bridge_beats_tb.py': [
        ('test_basic_latency', '=== Scenario BRIDGE-01: Basic latency insertion ==='),
        ('test_backpressure', '=== Scenario BRIDGE-02: Backpressure propagation ==='),
        ('test_data_integrity', '=== Scenario BRIDGE-03: Data integrity ==='),
        ('test_rapid_transactions', '=== Scenario BRIDGE-04: Rapid transactions ==='),
        ('test_multi_stage', '=== Scenario BRIDGE-05: Multiple pipeline stages ==='),
    ],
    'ctrlrd_engine_tb.py': [
        ('test_basic_read_match', '=== Scenario CTRLRD-01: Basic read-match ==='),
        ('test_null_address', '=== Scenario CTRLRD-02: Null address handling ==='),
        ('test_read_retry_match', '=== Scenario CTRLRD-03: Read-retry-match ==='),
        ('test_max_retries_exceeded', '=== Scenario CTRLRD-04: Max retries exceeded ==='),
        ('test_masked_comparison', '=== Scenario CTRLRD-05: Masked comparison ==='),
        ('test_axi_error', '=== Scenario CTRLRD-06: AXI error handling ==='),
        ('test_channel_reset', '=== Scenario CTRLRD-07: Channel reset ==='),
        ('test_back_to_back', '=== Scenario CTRLRD-08: Back-to-back operations ==='),
        ('test_mixed_scenarios', '=== Scenario CTRLRD-09: Mixed scenarios ==='),
    ],
    'ctrlwr_engine_tb.py': [
        ('test_basic_write', '=== Scenario CTRLWR-01: Basic write ==='),
        ('test_null_address', '=== Scenario CTRLWR-02: Null address handling ==='),
        ('test_byte_enables', '=== Scenario CTRLWR-03: Byte enable patterns ==='),
        ('test_axi_error', '=== Scenario CTRLWR-04: AXI error handling ==='),
        ('test_channel_reset', '=== Scenario CTRLWR-05: Channel reset ==='),
        ('test_back_to_back', '=== Scenario CTRLWR-06: Back-to-back operations ==='),
        ('test_mixed_scenarios', '=== Scenario CTRLWR-07: Mixed scenarios ==='),
    ],
}


def add_scenario_marker(filepath: Path, method_name: str, marker: str):
    """Add scenario marker to a test method."""
    content = filepath.read_text()

    # Find the test method
    pattern = rf'(    async def {method_name}\([^)]*\):[^\n]*\n(?:        """[^"]*"""[^\n]*\n)?)(        self\.log\.info\()'

    replacement = rf'\1        self.log.info("{marker}")\n\2'

    new_content = re.sub(pattern, replacement, content, count=1)

    if new_content != content:
        filepath.write_text(new_content)
        return True
    else:
        print(f"Warning: Could not find method {method_name} in {filepath.name}")
        return False


def main():
    """Main function to add all scenario markers."""
    tb_dir = Path('/mnt/data/github/rtldesignsherpa/projects/components/rapids/dv/tbclasses')

    total = 0
    success = 0

    for filename, mappings in SCENARIO_MAPPINGS.items():
        filepath = tb_dir / filename
        if not filepath.exists():
            print(f"Warning: File {filepath} does not exist")
            continue

        print(f"Processing {filename}...")
        for method_name, marker in mappings:
            total += 1
            if add_scenario_marker(filepath, method_name, marker):
                success += 1
                print(f"  ✓ Added marker to {method_name}")
            else:
                print(f"  ✗ Failed to add marker to {method_name}")

    print(f"\nCompleted: {success}/{total} markers added")
    return 0 if success == total else 1


if __name__ == '__main__':
    sys.exit(main())
