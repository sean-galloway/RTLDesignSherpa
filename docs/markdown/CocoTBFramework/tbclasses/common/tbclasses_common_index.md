<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# CocoTBFramework Testing Modules Directory

This directory contains specialized testbench classes for various digital circuit components. Each module provides comprehensive testing capabilities for specific circuit architectures.

## Directory Structure

```
CocoTBFramework/
├── tbclasses/
│   ├── misc/
│   │   └── tbbase.py                    # Base testbench class (reference)
│   └── common/
│       ├── adder_testing.py             # Adder testbench implementations
│       ├── cam_testing.py               # Content Addressable Memory testing
│       ├── crc_testing.py               # CRC (Cyclic Redundancy Check) testing
│       ├── divider_testing.py           # Divider circuit testing
│       ├── multiplier_testing.py        # Multiplier circuit testing
│       └── subtractor_testing.py        # Subtractor circuit testing
```

## Module Overview

| Module | Purpose | Key Features |
|--------|---------|--------------|
| **adder_testing.py** | Test various adder architectures | Full adders, half adders, carry-save adders |
| **cam_testing.py** | Test Content Addressable Memory | Tag validation, full/empty detection |
| **crc_testing.py** | Test CRC calculation circuits | Multiple CRC standards, configurable parameters |
| **divider_testing.py** | Test divider implementations | Integer division, remainder calculation |
| **multiplier_testing.py** | Test multiplier circuits | Booth algorithm, various bit widths |
| **subtractor_testing.py** | Test subtractor implementations | Full/half subtractors, borrow propagation |

## Getting Started

1. Each testing module inherits from `TBBase` (in `misc/tbbase.py`)
2. Modules are designed to be imported and instantiated in your cocotb tests
3. Configuration is typically done through environment variables
4. Each module provides comprehensive test suites with multiple test levels

## Common Features

All testing modules provide:
- **Configurable test levels**: basic, medium, full
- **Comprehensive logging**: Detailed test progress and failure analysis
- **Random and deterministic testing**: Both exhaustive and sampled test vectors
- **Pattern-based testing**: Walking ones, alternating patterns, corner cases
- **Statistical reporting**: Pass/fail counts and detailed error analysis

## Usage Pattern

```python
import cocotb
from CocoTBFramework.tbclasses.common.adder_testing import AdderTB

@cocotb.test()
async def test_adder(dut):
    tb = AdderTB(dut)
    tb.print_settings()
    await tb.run_comprehensive_tests()
```

## Documentation

- [Overview](tbclasses_common_overview.md) - Detailed framework overview
- [Adder Testing](tbclasses_common_adder_testing.md) - Adder testbench documentation
- [CAM Testing](tbclasses_common_cam_testing.md) - CAM testbench documentation  
- [CRC Testing](tbclasses_common_crc_testing.md) - CRC testbench documentation
- [Divider Testing](tbclasses_common_divider_testing.md) - Divider testbench documentation
- [Multiplier Testing](tbclasses_common_multiplier_testing.md) - Multiplier testbench documentation
- [Subtractor Testing](tbclasses_common_subtractor_testing.md) - Subtractor testbench documentation