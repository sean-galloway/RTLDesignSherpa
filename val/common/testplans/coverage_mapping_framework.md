# Functional-to-Line Coverage Mapping Framework

## Overview

This framework maps functional test scenarios to expected line coverage points,
addressing Verilator's limitation with combinational logic coverage tracking.

## Problem Statement

Verilator line coverage doesn't track:
- `always_comb` case statement branches
- Generate block assignments
- Combinational arithmetic paths

This causes modules to show artificially low coverage (e.g., 10-50%) even when
tests exercise all functionality.

## Solution: Functional Coverage Mapping

For each module, we define:
1. **Coverage Points**: Lines that Verilator annotates (from `--coverage-line`)
2. **Functional Scenarios**: Test scenarios that exercise specific functionality
3. **Scenario-to-Line Mapping**: Which scenarios cover which lines

### Coverage Point Categories

| Category | Verilator Tracks? | Our Approach |
|----------|-------------------|--------------|
| Sequential (always_ff) | Yes | Use direct line coverage |
| Combinational case | No | Map functional scenarios |
| Generate blocks | No | Map to parameter combinations |
| Port declarations | Yes (toggle) | Track input/output activity |

## Testplan Format (YAML)

```yaml
module: hex_to_7seg
rtl_file: rtl/common/hex_to_7seg.sv
coverage_file: val/common/local_sim_build/test_hex_to_7seg_*/coverage.dat

# Lines Verilator annotates (extracted from --annotate output)
coverage_points:
  - line: 21
    type: port
    description: "input hex[3:0]"
  - line: 22
    type: port
    description: "output seg[6:0]"
  - line: 36
    type: always_comb
    description: "always_comb begin"
  - line: 37
    type: case
    description: "casez (hex)"
  - lines: [38-54]
    type: case_branch
    description: "case branches 0x0-0xF + default"

# Functional scenarios that exercise the coverage points
functional_scenarios:
  - id: S1
    name: "All hex digits"
    description: "Test all 16 hex input values (0x0-0xF)"
    test_function: "test_all_hex_values"
    covers_lines: [36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53]
    status: verified  # verified, partial, not_tested

  - id: S2
    name: "Input toggle coverage"
    description: "All input bits toggle 0->1 and 1->0"
    test_function: "test_all_hex_values"
    covers_lines: [21]
    status: verified

  - id: S3
    name: "Output toggle coverage"
    description: "All output segment bits toggle"
    test_function: "test_all_hex_values"
    covers_lines: [22]
    status: verified

  - id: S4
    name: "Default case"
    description: "Invalid input handling (if applicable)"
    test_function: "N/A - all 4-bit inputs are valid"
    covers_lines: [54]
    status: not_applicable

# Implied coverage calculation
implied_coverage:
  total_points: 21
  covered_by_scenarios: 20
  not_applicable: 1
  implied_percentage: 100.0%
```

## Coverage Tracking Script

The script `bin/cov_utils/functional_coverage_tracker.py` will:

1. Parse testplan YAML files
2. Check test execution status (from pytest results)
3. Calculate implied coverage based on executed scenarios
4. Generate reports showing:
   - Verilator raw coverage
   - Functional scenario coverage
   - Implied line coverage

## Directory Structure

```
val/common/testplans/
├── coverage_mapping_framework.md  # This document
├── hex_to_7seg_testplan.yaml
├── decoder_testplan.yaml
├── counter_freq_invariant_testplan.yaml
├── ... (other module testplans)
└── templates/
    ├── combinational_module.yaml
    ├── sequential_module.yaml
    └── fsm_module.yaml
```

## Usage

```bash
# Generate testplan from module coverage data
python bin/cov_utils/generate_testplan.py \
    --module hex_to_7seg \
    --coverage val/common/local_sim_build/test_hex_to_7seg_*/coverage.dat

# Calculate implied coverage
python bin/cov_utils/functional_coverage_tracker.py \
    --testplan val/common/testplans/hex_to_7seg_testplan.yaml \
    --results val/common/logs/results_*.xml

# Generate coverage report
python bin/cov_utils/generate_coverage_report.py \
    --dir val/common \
    --include-functional
```

## Benefits

1. **Accurate Coverage**: Shows true test completeness for combinational modules
2. **Traceability**: Links test scenarios to coverage points
3. **Gap Analysis**: Identifies untested functionality
4. **CI Integration**: Can fail builds if implied coverage drops
