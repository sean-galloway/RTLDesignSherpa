# Test Plan: arbiter_priority_encoder

## Module: rtl/common/arbiter_priority_encoder.sv
## Test File: val/common/test_arbiter_priority_encoder.py
## Current Coverage: 100% (VERIFIED 2026-01-17)

## Module Overview

Optimized priority encoder for arbitration with:
- Specialized implementations for 4, 8, 16, 32 clients
- Generic loop-based implementation for other sizes
- Support for masked and unmasked request inputs
- Priority order: lower index = higher priority

## Scenarios

| ID | Scenario | Description | Tested | Coverage Gap |
|----|----------|-------------|--------|--------------|
| APE-01 | Single request | Only one bit set | YES | - |
| APE-02 | Priority order | Lower index wins | YES | - |
| APE-03 | All requests | All bits set simultaneously | YES | - |
| APE-04 | No requests | requests = 0 | YES | - |
| APE-05 | Masked requests | requests_masked input | YES | - |
| APE-06 | Unmasked requests | requests_unmasked input | YES | - |
| APE-07 | Any masked flag | any_masked_requests input | YES | - |
| APE-08 | Winner output | Verify winner encoding | YES | - |
| APE-09 | Winner valid | Verify winner_valid flag | YES | - |
| APE-10 | 4-client config | CLIENTS=4 | YES | - |
| APE-11 | 8-client config | CLIENTS=8 | YES | - |
| APE-12 | Walking ones | Single bit walks through | YES | - |

## Coverage Status

**VERIFIED: 100% line/branch coverage achieved (2026-01-17)**

All test scenarios fully covered by `test_arbiter_priority_encoder.py` via `ArbiterPriorityEncoderTB`:
- `test_priority_order()` - Covers APE-01, APE-02, APE-03
- `test_masked_vs_unmasked()` - Covers APE-05, APE-06, APE-07
- `test_no_requests()` - Covers APE-04
- `test_all_clients()` - Covers APE-08, APE-09, APE-12
- `test_all_combinations()` - Comprehensive coverage for small client counts

The testbench exercises both `requests_masked` and `requests_unmasked` inputs with
the `any_masked_requests` selector.

## Test Configurations

REG_LEVEL Control:
- GATE: 2 tests (4 optimized, 5 generic)
- FUNC: 6 tests (all configurations)
- FULL: 6 tests (same as FUNC)

Tested configurations:
- CLIENTS=4 (optimized unrolled casez)
- CLIENTS=8 (optimized unrolled casez)
- CLIENTS=16 (optimized unrolled casez)
- CLIENTS=32 (optimized unrolled casez)
- CLIENTS=5 (generic loop-based)
- CLIENTS=12 (generic loop-based)

## Test Commands

```bash
# Run with coverage
COVERAGE=1 REG_LEVEL=FUNC pytest val/common/test_arbiter_priority_encoder.py -v
```

## Priority

**NONE** - All coverage goals achieved.
