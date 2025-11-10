#!/usr/bin/env python3
"""
Script to update Bridge test files to val/common compliance standard.

Updates:
1. Test files: Add REG_LEVEL/TEST_LEVEL/WAVES support
2. TB classes: Add environment variable reading for TEST_LEVEL

Author: sean galloway
Created: 2025-10-28
"""

import os
import re
import sys
from pathlib import Path

# Repository root
REPO_ROOT = Path(__file__).parent.parent

# Test files to update
TEST_FILES = [
    'projects/components/bridge/dv/tests/test_bridge_axi4_2x2.py',
    'projects/components/bridge/dv/tests/test_bridge_cam.py',
    'projects/components/bridge/dv/tests/test_bridge_ooo.py',
]

# TB classes to update
TB_FILES = [
    'projects/components/bridge/dv/tbclasses/bridge_axi4_flat_tb.py',
    'projects/components/bridge/dv/tbclasses/bridge_cam_tb.py',
    'projects/components/bridge/dv/tbclasses/bridge_ooo_tb.py',
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
    init_pattern = r'(def __init__\(self,[^\)]+\):.*?super\(\).__init__\(dut\)\n)'

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
    if 'REG_LEVEL' in content and "os.environ.get('REG_LEVEL'" in content:
        print(f"  ✓ Test already updated: {file_path}")
        return False

    # 1. Update generate_*_params() function to use REG_LEVEL
    # Find the function name first
    func_match = re.search(r'def (generate_\w+_params)\(\):', content)
    if not func_match:
        print(f"  ⚠️  No generate params function found in {file_path}")
        return False

    func_name = func_match.group(1)

    # Find existing generate_params function body
    params_pattern = rf'def {func_name}\(\):.*?(?=\n(?:bridge_params|cam_params|ooo_params) =)'
    params_match = re.search(params_pattern, content, re.DOTALL)

    if params_match:
        old_function = params_match.group(0)

        # Extract current parameter lines (looking for params.append lines)
        param_lines = re.findall(r'params\.append\([^\)]+\)', old_function)

        # Create new generate_params with REG_LEVEL support
        new_generate_params = f'''def {func_name}():
    """
    Generate test parameters based on REG_LEVEL.

    REG_LEVEL=GATE: 1 test (smoke test - minimal config)
    REG_LEVEL=FUNC: 2-3 tests (functional coverage) - default
    REG_LEVEL=FULL: 5+ tests (comprehensive validation - all configs)

    Returns list of tuples: (..., test_case)
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    params = []

    if reg_level == 'GATE':
        # Minimal - smoke test only (first config, basic test case)
        {param_lines[0] if param_lines else '# TODO: Add params'}
    elif reg_level == 'FUNC':
        # Functional coverage - default configurations with basic test case
'''

        # Add first 2-3 params for FUNC
        func_count = min(3, len(param_lines))
        for i in range(func_count):
            new_generate_params += f'        {param_lines[i]}\n'

        new_generate_params += '''    else:  # FULL
        # Comprehensive - all configurations and test levels
'''

        # Add all params for FULL
        for param_line in param_lines:
            new_generate_params += f'        {param_line}\n'

        new_generate_params += '\n    return params\n'

        content = content.replace(old_function, new_generate_params)

    # 2. Update extra_env to add TEST_LEVEL, TEST_DEBUG, and WAVES support
    # Find extra_env dictionary assignments
    extra_env_pattern = r"extra_env = \{[^}]+\}"

    def replace_extra_env(match):
        """Replace extra_env with compliant version"""
        return """extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_LEVEL': test_case,
        'TEST_DEBUG': '0',
    }

    # WAVES support - conditionally set COCOTB_TRACE_FILE for VCD generation
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')"""

    content = re.sub(extra_env_pattern, replace_extra_env, content)

    # 3. Add import for random if not present
    if 'import random' not in content:
        # Find the imports section and add random
        import_section = re.search(r'(import os\nimport sys)', content)
        if import_section:
            content = content.replace(import_section.group(1),
                                     import_section.group(1) + '\nimport random')

    with open(full_path, 'w') as f:
        f.write(content)

    print(f"  ✓ Updated test: {file_path}")
    return True


def main():
    """Main function to update all Bridge test files."""
    print("=" * 70)
    print("Updating Bridge Test Files to val/common Compliance Standard")
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
    print("✓ Bridge Test Compliance Update Complete!")
    print("=" * 70)
    print("\nUpdates Applied:")
    print("  1. TB classes now read TEST_LEVEL environment variable")
    print("  2. Test files use REG_LEVEL for parameter generation")
    print("  3. Test files include test_case in all pytest wrappers")
    print("  4. Test files support WAVES environment variable for VCD generation")
    print("\nUsage:")
    print("  - Regular test:  pytest test_bridge_axi4_2x2.py -v")
    print("  - With waves:    WAVES=1 pytest test_bridge_axi4_2x2.py -v")
    print("  - Using ptw:     ptw test_bridge_axi4_2x2.py")
    print("  - Smoke test:    REG_LEVEL=GATE pytest test_bridge_axi4_2x2.py -v")
    print("  - Full test:     REG_LEVEL=FULL pytest test_bridge_axi4_2x2.py -v")
    print("=" * 70)


if __name__ == '__main__':
    main()
