# FUTURE - HP/LP Test Components

This directory contains test components for High-Performance (HP) and Low-Power (LP) AXI4 monitoring modules that have been moved here for future development.

## Files in this Directory:

### Test Functions:
- `lp_hp_test_functions.py` - Contains the `_test_high_performance()` and `_test_low_power()` functions that were removed from the main test suite

### Simulation Build Directories:
- Various `test_axi4_master_rd_*p_mon_*` directories from previous test runs

## Original Test Configurations:

The following test matrix entries were commented out in `test_axi4_matrix_integration.py`:

```python
# Removed from test matrix:
("master_rd_hp", "high_performance"),
("master_rd_lp", "low_power"),
("power_modes", "power_management"),

# Removed from config_map:
"master_rd_hp": {
    "dut_name": "axi4_master_rd_hp_mon",
    "test_focus": "high_performance",
    "enable_features": ["filtering", "clock_gating", "high_performance", "histograms", "qos"],
    "agent_id": 15,
},
"master_rd_lp": {
    "dut_name": "axi4_master_rd_lp_mon",
    "test_focus": "low_power",
    "enable_features": ["filtering", "clock_gating", "low_power", "sleep_mode", "dvfs"],
    "agent_id": 16,
},
```

## Re-enabling Instructions:

1. Move RTL files back from `rtl/amba/axi4/FUTURE/`
2. Uncomment test configurations in `test_axi4_matrix_integration.py`
3. Add the test functions from `lp_hp_test_functions.py` back to the main test file
4. Ensure all power management RTL issues are resolved first

## Status:

- **HP Module**: Was working but moved for consistency
- **LP Module**: Had timeout/deadlock issues requiring RTL debugging