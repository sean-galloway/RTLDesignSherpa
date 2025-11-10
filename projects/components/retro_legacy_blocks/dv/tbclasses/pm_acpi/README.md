# PM_ACPI Testbench Classes

**Status:** 📋 Planned - Structure Created

---

## Overview

This directory contains testbench classes for the PM_ACPI block.

## File Organization

### Main Testbench
`pm_acpi_tb.py` - Main testbench class
- Inherits from TBBase
- Manages DUT signals
- Provides helper methods for common operations
- Implements MANDATORY methods:
  - `async def setup_clocks_and_reset(self)`
  - `async def assert_reset(self)`
  - `async def deassert_reset(self)`

### Test Suites
- `pm_acpi_tests_basic.py` - Basic test suite (4-6 tests)
- `pm_acpi_tests_medium.py` - Medium test suite (5-8 tests)
- `pm_acpi_tests_full.py` - Full test suite (3-5 tests)

## Import Pattern

Test files should import from project area:

```python
import os, sys
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../..'))
sys.path.insert(0, repo_root)

# Import from PROJECT AREA (not framework!)
from projects.components.retro_legacy_blocks.dv.tbclasses.pm_acpi.pm_acpi_tb import PM_ACPITB

# Shared framework utilities
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
```

## Design Standards

All testbench classes MUST:
- Follow repository reset macro standards
- Implement 3 mandatory methods (setup/assert/deassert)
- Be located in project area (not framework)
- Provide clear documentation

---

**Last Updated:** 2025-10-29
