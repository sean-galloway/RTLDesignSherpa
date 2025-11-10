#!/usr/bin/env python3
"""
Script to update STREAM test files to val/common compliance standard.

Updates:
1. Test files: Add REG_LEVEL/TEST_LEVEL/WAVES support
2. TB classes: Add environment variable reading for TEST_LEVEL

Author: sean galloway
Created: 2025-10-27
"""

import os
import re
import sys
from pathlib import Path

# Repository root
REPO_ROOT = Path(__file__).parent.parent

# Test files to update (excluding test_datapath_rd_test.py which is already done)
TEST_FILES = [
    'projects/components/stream/dv/tests/fub_tests/test_datapath_wr_test.py',
    'projects/components/stream/dv/tests/fub_tests/test_perf_profiler.py',
    'projects/components/stream/dv/tests/fub_tests/test_apbtodescr.py',
    'projects/components/stream/dv/tests/fub_tests/test_simple_sram.py',
    'projects/components/stream/dv/tests/fub_tests/test_axi_read_engine.py',
    'projects/components/stream/dv/tests/fub_tests/test_axi_write_engine.py',
    'projects/components/stream/dv/tests/fub_tests/test_descriptor_engine.py',
    'projects/components/stream/dv/tests/fub_tests/test_scheduler.py',
    'projects/components/stream/dv/tests/fub_tests/test_sram_controller.py',
    'projects/components/stream/dv/tests/fub_tests/test_datapath_burst_sweep.py',
    'projects/components/stream/dv/tests/fub_tests/test_datapath_integrated.py',
]

# TB classes to update
TB_FILES = [
    'projects/components/stream/dv/tbclasses/datapath_wr_test_tb.py',
    'projects/components/stream/dv/tbclasses/perf_profiler_tb.py',
    'projects/components/stream/dv/tbclasses/apbtodescr_tb.py',
    'projects/components/stream/dv/tbclasses/simple_sram_tb.py',
    'projects/components/stream/dv/tbclasses/axi_read_engine_tb.py',
    'projects/components/stream/dv/tbclasses/axi_write_engine_tb.py',
    'projects/components/stream/dv/tbclasses/descriptor_engine_tb.py',
    'projects/components/stream/dv/tbclasses/scheduler_tb.py',
    'projects/components/stream/dv/tbclasses/sram_controller_tb.py',
]


def update_tb_class(file_path):
    """Update TB class to read TEST_LEVEL environment variable."""
    full_path = REPO_ROOT / file_path

    if not full_path.exists():
        print(f"  ⚠️  TB file not found: {file_path}")
        return False

    with open(full_path, 'r') as f:
        content = f.read()

    # Check if already updated
    if 'self.TEST_LEVEL' in content:
        print(f"  ✓ TB already updated: {file_path}")
        return False

    # Find __init__ method and add environment variable reading
    # Pattern: match __init__ right after super().__init__(dut)
    init_pattern = r'(def __init__\(self, dut[^\)]*\):.*?super\(\).__init__\(dut\)\n)'

    env_vars_code = '''
        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic').lower()
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Validate test level
        valid_levels = ['basic', 'medium', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'basic'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'basic'
'''

    # Add environment variable reading after super().__init__(dut)
    content = re.sub(init_pattern, r'\1' + env_vars_code, content, flags=re.DOTALL)

    with open(full_path, 'w') as f:
        f.write(content)

    print(f"  ✓ Updated TB: {file_path}")
    return True


def update_test_file(file_path):
    """Update test file with REG_LEVEL/TEST_LEVEL/WAVES support."""
    full_path = REPO_ROOT / file_path

    if not full_path.exists():
        print(f"  ⚠️  Test file not found: {file_path}")
        return False

    with open(full_path, 'r') as f:
        content = f.read()

    # Check if already updated
    if 'REG_LEVEL' in content and 'test_level' in content:
        print(f"  ✓ Test already updated: {file_path}")
        return False

    # 1. Update generate_params() function to use REG_LEVEL
    # Find existing generate_params function
    params_pattern = r'def generate_params\(\):.*?return \[(.*?)\]'
    params_match = re.search(params_pattern, content, re.DOTALL)

    if params_match:
        # Extract current parameter tuple
        current_params = params_match.group(1).strip()

        # Create new generate_params with REG_LEVEL support
        new_generate_params = '''def generate_params():
    """
    Generate parameters for tests based on REG_LEVEL.

    REG_LEVEL=GATE: 1 test (smoke test - basic config)
    REG_LEVEL=FUNC: 1 test (functional coverage) - default
    REG_LEVEL=FULL: 3 tests (comprehensive validation - all test levels)

    Parameters: (..., test_level)
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        # Minimal - smoke test only
        params = [
            (''' + current_params + ''', 'basic'),
        ]
    elif reg_level == 'FUNC':
        # Functional coverage - default configuration with basic level
        params = [
            (''' + current_params + ''', 'basic'),
        ]
    else:  # FULL
        # Comprehensive - test all levels
        params = [
            (''' + current_params + ''', 'basic'),
            (''' + current_params + ''', 'medium'),
            (''' + current_params + ''', 'full'),
        ]

    return params'''

        content = re.sub(params_pattern, new_generate_params, content, flags=re.DOTALL)

    # 2. Update @pytest.mark.parametrize decorators to include test_level
    # Count how many parameters are currently in the decorator
    param_decorator_pattern = r'@pytest\.mark\.parametrize\("([^"]+)", params\)'
    param_decorators = re.findall(param_decorator_pattern, content)

    if param_decorators:
        for old_params in set(param_decorators):
            new_params = old_params + ', test_level'
            content = content.replace(
                f'@pytest.mark.parametrize("{old_params}", params)',
                f'@pytest.mark.parametrize("{new_params}", params)'
            )

    # 3. Update function signatures to include test_level parameter
    # Match test functions and add test_level to signature
    func_sig_pattern = r'def (test_\w+)\(request, ([^\)]+)\):'

    def add_test_level_param(match):
        func_name = match.group(1)
        params = match.group(2)
        if 'test_level' not in params:
            params += ', test_level'
        return f'def {func_name}(request, {params}):'

    content = re.sub(func_sig_pattern, add_test_level_param, content)

    # 4. Update test_name_plus_params to include test_level
    # This is tricky because the format varies. Try to match and append _{test_level}
    test_name_pattern = r'(test_name_plus_params = f"test_\w+[^"]*)"'
    content = re.sub(test_name_pattern, r'\1_{test_level}"', content)

    # 5. Update extra_env to add TEST_LEVEL, TEST_DEBUG, and WAVES support
    old_extra_env_pattern = r"extra_env = \{[^}]+\}"

    # This is a simplified replacement - matches the common pattern
    new_extra_env = """extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_LEVEL': test_level,
        'TEST_DEBUG': '0',
    }

    # WAVES support - conditionally set COCOTB_TRACE_FILE for VCD generation
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')"""

    content = re.sub(old_extra_env_pattern, new_extra_env, content)

    # 6. Update print statements to include test_level
    # Match success messages
    content = re.sub(
        r'print\(f"✓ ([^"]+) PASSED"\)',
        r'print(f"✓ \1 PASSED ({test_level} level)")',
        content
    )

    content = re.sub(
        r'print\(f"✗ ([^"]+) FAILED: \{str\(e\)\}"\)',
        r'print(f"✗ \1 FAILED ({test_level} level): {str(e)}")',
        content
    )

    with open(full_path, 'w') as f:
        f.write(content)

    print(f"  ✓ Updated test: {file_path}")
    return True


def main():
    """Main function to update all STREAM test files."""
    print("=" * 70)
    print("Updating STREAM Test Files to val/common Compliance Standard")
    print("=" * 70)

    # Update TB classes
    print("\n[1/2] Updating TB Classes...")
    tb_updated = 0
    for tb_file in TB_FILES:
        if update_tb_class(tb_file):
            tb_updated += 1

    print(f"\nTB Classes: {tb_updated} updated, {len(TB_FILES) - tb_updated} skipped")

    # Update test files
    print("\n[2/2] Updating Test Files...")
    test_updated = 0
    for test_file in TEST_FILES:
        if update_test_file(test_file):
            test_updated += 1

    print(f"\nTest Files: {test_updated} updated, {len(TEST_FILES) - test_updated} skipped")

    print("\n" + "=" * 70)
    print("✓ STREAM Test Compliance Update Complete!")
    print("=" * 70)
    print("\nUpdates Applied:")
    print("  1. TB classes now read TEST_LEVEL environment variable")
    print("  2. Test files use REG_LEVEL for parameter generation")
    print("  3. Test files include test_level in all pytest wrappers")
    print("  4. Test files support WAVES environment variable for VCD generation")
    print("\nUsage:")
    print("  - Regular test:  pytest test_module.py -v")
    print("  - With waves:    WAVES=1 pytest test_module.py -v")
    print("  - Using ptw:     ptw test_module.py")
    print("  - Smoke test:    REG_LEVEL=GATE pytest test_module.py -v")
    print("  - Full test:     REG_LEVEL=FULL pytest test_module.py -v")
    print("=" * 70)


if __name__ == '__main__':
    main()
