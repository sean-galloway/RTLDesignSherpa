# PIT_8254 Testbench Classes

**Status:** 📋 Planned - Structure Created

---

## Overview

This directory contains testbench classes for the PIT_8254 block.

## File Organization

### Main Testbench
`pit_8254_tb.py` - Main testbench class
- Inherits from TBBase
- Manages DUT signals
- Provides helper methods for common operations
- Implements MANDATORY methods:
  - `async def setup_clocks_and_reset(self)`
  - `async def assert_reset(self)`
  - `async def deassert_reset(self)`

### Test Suites
- `pit_8254_tests_basic.py` - Basic test suite (4-6 tests)
- `pit_8254_tests_medium.py` - Medium test suite (5-8 tests)
- `pit_8254_tests_full.py` - Full test suite (3-5 tests)

## Import Pattern

Test files should import from project area:

```python
import os, sys
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../..'))
sys.path.insert(0, repo_root)

# Import from PROJECT AREA (not framework!)
from projects.components.retro_legacy_blocks.dv.tbclasses.pit_8254.pit_8254_tb import PIT_8254TB

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
