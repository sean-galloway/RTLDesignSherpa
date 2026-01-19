# Retro Legacy Blocks - Testplan Directory

**Created:** 2026-01-18
**Purpose:** YAML testplans mapping functional scenarios to verification coverage

---

## Overview

This directory contains testplan YAML files for all 9 subsystems in the retro_legacy_blocks component. Each testplan documents:

- Module parameters
- Functional test scenarios (basic/medium/full levels)
- Test level coverage status
- Parameter combinations tested
- Implied coverage calculations

**Format Reference:** `/mnt/data/github/rtldesignsherpa/val/amba/testplans/axil4_slave_wr_testplan.yaml`

---

## Testplan Files

### 1. `apb_gpio_testplan.yaml`
- **Status:** Basic tests only (needs medium/full)
- **Basic Tests:** 7/7 passing (100%)
- **Coverage:** 64% overall (basic only)
- **RTL:** `rtl/gpio/apb_gpio.sv` (5 modules)
- **Test:** `dv/tests/test_apb_gpio.py`
- **Missing:** Edge/level interrupts, mixed mode, CDC stress

### 2. `apb_hpet_testplan.yaml` ✅ 100% COMPLETE
- **Status:** ALL LEVELS IMPLEMENTED
- **Basic Tests:** 7/7 passing (100%)
- **Medium Tests:** 5/5 passing (100%)
- **Full Tests:** 4/4 passing (100%)
- **Coverage:** 100% overall
- **RTL:** `rtl/hpet/apb_hpet.sv` (5 modules)
- **Test:** `dv/tests/test_apb_hpet.py`
- **Production Ready:** Reference implementation

### 3. `apb_ioapic_testplan.yaml`
- **Status:** Basic tests only (needs medium/full)
- **Basic Tests:** 5/5 passing (100%)
- **Coverage:** 45% overall (basic only)
- **RTL:** `rtl/ioapic/apb_ioapic.sv` (5 modules)
- **Test:** `dv/tests/test_apb_ioapic.py`
- **Missing:** Priority handling, edge/level, routing, stress

### 4. `apb_pic_8259_testplan.yaml`
- **Status:** Basic tests only (needs medium/full)
- **Basic Tests:** 5/5 passing (100%)
- **Coverage:** 45% overall (basic only)
- **RTL:** `rtl/pic_8259/apb_pic_8259.sv` (5 modules)
- **Test:** `dv/tests/test_apb_pic_8259.py`
- **Missing:** Multiple IRQs, specific EOI, edge/level, rotation, cascade

### 5. `apb_pit_8254_testplan.yaml`
- **Status:** Basic tests only (needs medium/full)
- **Basic Tests:** 5/5 passing (100%)
- **Coverage:** 42% overall (basic only)
- **RTL:** `rtl/pit_8254/apb_pit_8254.sv` (6 modules)
- **Test:** `dv/tests/test_apb_pit_8254.py`
- **Missing:** Modes 1/3/4/5, multiple counters, BCD counting

### 6. `apb_pm_acpi_testplan.yaml` ✅ 100% COMPLETE
- **Status:** ALL LEVELS IMPLEMENTED
- **Basic Tests:** 8/8 passing (100%)
- **Medium Tests:** 5/5 passing (100%)
- **Full Tests:** 3/3 passing (100%)
- **Coverage:** 100% overall
- **RTL:** `rtl/pm_acpi/apb_pm_acpi.sv` (5 modules)
- **Test:** `dv/tests/test_apb_pm_acpi.py`
- **Production Ready:** Second block to achieve 100%

### 7. `apb_rtc_testplan.yaml`
- **Status:** Basic tests only (needs medium/full)
- **Basic Tests:** 5/5 passing (100%)
- **Coverage:** 45% overall (basic only)
- **RTL:** `rtl/rtc/apb_rtc.sv` (4 modules)
- **Test:** `dv/tests/test_apb_rtc.py`
- **Missing:** Alarm, date rollover, leap year, periodic interrupt, battery backup

### 8. `apb_smbus_testplan.yaml`
- **Status:** Basic tests only (needs medium/full)
- **Basic Tests:** 6/6 passing (100%)
- **Coverage:** 40% overall (basic only)
- **RTL:** `rtl/smbus/apb_smbus.sv` (7 modules)
- **Test:** `dv/tests/test_apb_smbus.py`
- **Missing:** Block transfers, PEC, FIFO, process call, multi-master

### 9. `apb_uart_16550_testplan.yaml` ✅ 100% COMPLETE
- **Status:** ALL LEVELS IMPLEMENTED
- **Basic Tests:** 7/7 passing (100%)
- **Medium Tests:** 7/7 passing (100%)
- **Full Tests:** 5/5 passing (100%)
- **Coverage:** 100% overall
- **RTL:** `rtl/uart_16550/apb_uart_16550.sv` (5 modules)
- **Test:** `dv/tests/test_apb_uart_16550.py`
- **Production Ready:** Third block to achieve 100%

---

## Summary Statistics

### Completion Status

| Status | Blocks | Percentage |
|--------|--------|------------|
| 100% Complete (all levels) | 3 | 33% |
| Basic Only (needs medium/full) | 6 | 67% |
| **Total Blocks** | **9** | **100%** |

### Test Level Coverage

| Test Level | Implemented | Not Implemented |
|------------|-------------|-----------------|
| Basic | 9/9 (100%) | 0/9 (0%) |
| Medium | 3/9 (33%) | 6/9 (67%) |
| Full | 3/9 (33%) | 6/9 (67%) |

### Production Ready Blocks

1. **HPET** - 100% complete (reference implementation)
2. **PM_ACPI** - 100% complete
3. **UART 16550** - 100% complete

### Blocks Needing Medium/Full Tests

1. **GPIO** - Needs edge/level interrupts, mixed mode, CDC stress
2. **IOAPIC** - Needs priority, edge/level, routing, stress
3. **PIC 8259** - Needs multiple IRQs, specific EOI, rotation, cascade
4. **PIT 8254** - Needs modes 1/3/4/5, multiple counters, BCD
5. **RTC** - Needs alarm, date rollover, leap year, battery backup
6. **SMBus** - Needs block transfers, PEC, FIFO, multi-master

---

## Testplan Format

Each testplan YAML file contains:

```yaml
module: <module_name>
rtl_file: <path_to_rtl>
test_file: <path_to_test>

parameters:
  - name: <param_name>
    default: <value>
    description: <description>

functional_scenarios:
  - id: <ID>
    name: <name>
    description: <description>
    test_function: <function_name>
    test_level: basic|medium|full
    priority: high|medium|low
    status: verified|not_implemented

test_level_coverage:
  basic:
    implemented: true|false
    test_count: <count>
    coverage_percentage: <percentage>
    status: <status_message>

  medium:
    implemented: true|false
    test_count: <count>
    coverage_percentage: <percentage>
    status: <status_message>

  full:
    implemented: true|false
    test_count: <count>
    coverage_percentage: <percentage>
    status: <status_message>

parameter_coverage:
  - <param1>: <value1>
    <param2>: <value2>
    test_level: basic|medium|full
    status: verified|not_implemented

implied_coverage:
  total_<block>_features: <count>
  basic_features_covered: <count>
  medium_features_covered: <count>
  full_features_covered: <count>
  basic_percentage: <percentage>
  overall_percentage: <percentage>

notes: |
  <detailed notes about current status, missing tests, etc.>
```

---

## Next Steps

### For Users Working on Existing Blocks

1. Review the testplan for your block
2. Identify missing medium/full tests
3. Implement missing test scenarios
4. Update testplan YAML when tests are added

### For Users Adding New Blocks

1. Create testplan YAML following the format above
2. Start with basic tests (4-6 scenarios)
3. Add medium tests (5-8 scenarios)
4. Add full tests (3-5 scenarios)
5. Target 100% coverage across all levels

---

## References

- **Master PRD:** `projects/components/retro_legacy_blocks/PRD.md`
- **Component README:** `projects/components/retro_legacy_blocks/README.md`
- **Global Requirements:** `/GLOBAL_REQUIREMENTS.md`
- **Component CLAUDE.md:** `projects/components/retro_legacy_blocks/CLAUDE.md`
- **Format Reference:** `val/amba/testplans/axil4_slave_wr_testplan.yaml`

---

**Maintained By:** RTL Design Sherpa Project
**Last Updated:** 2026-01-18
