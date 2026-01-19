# Converters Component Testplans

**Purpose:** YAML testplans mapping functional test scenarios to Verilator coverage points for all converter modules.

**Format Reference:** See `/mnt/data/github/rtldesignsherpa/val/amba/testplans/axil4_slave_wr_testplan.yaml` for format details.

---

## Testplan Files

### 1. Data Width Converters

**File:** `axi4_dwidth_converter_rd_testplan.yaml`
- **Module:** axi4_dwidth_converter_rd.sv
- **Test:** test_axi4_dwidth_converter_rd.py
- **Coverage:** 100% (15 scenarios)
- **Status:** Well tested - upsize/downsize, bursts, accumulation, splitting
- **Verilator:** ~40% (skid buffers and conversion logic)

**File:** `axi4_dwidth_converter_wr_testplan.yaml`
- **Module:** axi4_dwidth_converter_wr.sv
- **Test:** test_axi4_dwidth_converter_wr.py
- **Coverage:** 100% (16 scenarios)
- **Status:** Well tested - upsize/downsize, WSTRB conversion, WLAST handling
- **Verilator:** ~42% (skid buffers and conversion logic)

---

### 2. Protocol Converters (AXI4 ↔ AXI4-Lite)

**File:** `axi4_to_axil4_testplan.yaml`
- **Modules:** axi4_to_axil4_rd.sv, axi4_to_axil4_wr.sv
- **Tests:** test_axi4_to_axil4_rd.py, test_axi4_to_axil4_wr.py
- **Coverage:** 100% (18 scenarios total - 9 read, 9 write)
- **Status:** Well tested - burst decomposition, ID preservation, response accumulation
- **Verilator:** ~38% (FSM and burst tracking)

**File:** `axil4_to_axi4_testplan.yaml`
- **Modules:** axil4_to_axi4_rd.sv, axil4_to_axi4_wr.sv
- **Tests:** test_axil4_to_axi4_rd.py, test_axil4_to_axi4_wr.py
- **Coverage:** 100% (18 scenarios total - 9 read, 9 write)
- **Status:** Well tested - simple passthrough with default field assignment
- **Verilator:** ~92% (mostly passthrough logic)

---

### 3. Protocol Converters (AXI4 → APB)

**File:** `axi4_to_apb_testplan.yaml`
- **Modules:** axi4_to_apb_convert.sv, axi4_to_apb_shim.sv
- **Tests:** test_axi2apb_shim.py
- **Coverage:** 17.4% (4 tested, 10 gaps)
- **Status:** CRITICAL GAPS - convert module untested, width conversion untested
- **Verilator:** ~35% (only shim tested)

**GAPS:**
- axi4_to_apb_convert.sv has NO standalone test
- Burst decomposition FSM UNTESTED
- Width conversion logic UNTESTED
- Side queue tracking UNTESTED
- Error scenarios UNTESTED

**RECOMMENDATION:** Create test_axi4_to_apb_convert.py for standalone testing

---

### 4. UART to AXI4-Lite Bridge

**File:** `uart_axil_bridge_testplan.yaml`
- **Modules:** uart_axil_bridge.sv, uart_rx.sv, uart_tx.sv
- **Tests:** test_uart_axil_bridge.py
- **Coverage:** 35.7% (10 tested, 6 gaps)
- **Status:** Moderate gaps - happy path tested, error paths missing
- **Verilator:** ~45% (bridge FSM and UART integration)

**GAPS:**
- uart_rx.sv and uart_tx.sv have NO standalone tests (integration only)
- UART framing errors UNTESTED
- Invalid command handling UNTESTED
- AXI error responses UNTESTED
- TX backpressure UNTESTED

**RECOMMENDATION:** Current coverage adequate for happy path, consider error injection tests

---

## Coverage Summary

| Module | Scenarios | Tested | Coverage | Priority |
|--------|-----------|--------|----------|----------|
| axi4_dwidth_converter_rd | 15 | 15 | 100% | ✅ Complete |
| axi4_dwidth_converter_wr | 16 | 16 | 100% | ✅ Complete |
| axi4_to_axil4 (rd/wr) | 18 | 18 | 100% | ✅ Complete |
| axil4_to_axi4 (rd/wr) | 18 | 18 | 100% | ✅ Complete |
| axi4_to_apb | 14 | 4 | 17.4% | 🔴 Critical gaps |
| uart_axil_bridge | 16 | 10 | 35.7% | 🟡 Moderate gaps |

**Total:** 97 scenarios, 81 tested (83.5% overall)

---

## Module Coverage vs Testing Gaps

### Well Tested Modules (12 total)
1. axi4_dwidth_converter_rd.sv ✅
2. axi4_dwidth_converter_wr.sv ✅
3. axi_data_upsize.sv ✅ (via dwidth tests)
4. axi_data_dnsize.sv ✅ (via dwidth tests)
5. axi4_to_axil4.sv ✅ (wrapper - via rd/wr)
6. axi4_to_axil4_rd.sv ✅
7. axi4_to_axil4_wr.sv ✅
8. axil4_to_axi4.sv ✅ (wrapper - via rd/wr)
9. axil4_to_axi4_rd.sv ✅
10. axil4_to_axi4_wr.sv ✅
11. peakrdl_to_cmdrsp.sv ✅ (has test)
12. uart_axil_bridge.sv 🟡 (partial)

### Modules with Gaps (4 total)
13. axi4_to_apb_convert.sv 🔴 NO TEST
14. axi4_to_apb_shim.sv 🟡 MINIMAL TEST
15. uart_rx.sv 🟡 NO STANDALONE TEST
16. uart_tx.sv 🟡 NO STANDALONE TEST

---

## Testplan Usage

### For Developers

**Adding new tests:**
1. Update appropriate testplan YAML file
2. Add functional scenario with test_function reference
3. Map to coverage_points (line numbers)
4. Update implied_coverage calculation

**Reviewing coverage:**
```bash
# View testplan
cat projects/components/converters/dv/testplans/<module>_testplan.yaml

# Check for gaps
grep "status: not_tested" <module>_testplan.yaml

# View gap summary
grep -A 20 "gap_summary:" <module>_testplan.yaml
```

### For CI/CD

Testplans can be parsed to:
- Generate coverage reports
- Identify untested scenarios
- Track regression test progress
- Document test requirements

---

## Format Details

Each testplan includes:
- **Module metadata:** Name, RTL file, test file
- **Parameters:** Configurable parameters with defaults
- **Coverage points:** Line numbers mapped to ports/logic
- **Functional scenarios:** Test descriptions with coverage mapping
- **Parameter coverage:** Tested parameter combinations
- **Implied coverage:** Calculation showing functional vs Verilator coverage
- **Notes:** Module description, gaps, recommendations

**Line numbers:** Estimated based on module structure, verify with actual RTL

---

## Maintenance

**When updating RTL:**
1. Check if line numbers in testplan need updating
2. Add new coverage points for new functionality
3. Update functional scenarios if behavior changes
4. Recalculate implied coverage

**When adding tests:**
1. Update status from "not_tested" to "verified"
2. Add new scenarios if test covers additional functionality
3. Update gap_summary section
4. Increment implied_coverage counters

---

**Created:** 2026-01-18
**Format Version:** 1.0 (matches val/amba/testplans/)
