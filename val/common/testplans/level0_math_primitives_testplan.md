# Level 0 Testplan: Math Primitives

## Modules Covered
- math_adder_half.sv
- math_adder_full.sv
- math_subtractor_half.sv
- math_subtractor_full.sv
- math_adder_carry_save.sv

## Target Coverage: 95%+

---

## math_adder_half.sv

### Truth Table (Exhaustive)
| i_a | i_b | ow_sum | ow_carry |
|-----|-----|--------|----------|
| 0 | 0 | 0 | 0 |
| 0 | 1 | 1 | 0 |
| 1 | 0 | 1 | 0 |
| 1 | 1 | 0 | 1 |

### Scenarios
| ID | Scenario | Description | Priority |
|----|----------|-------------|----------|
| HA-01 | All combinations | Test all 4 input combinations | HIGH |
| HA-02 | Random patterns | 100 random input pairs | MEDIUM |
| HA-03 | Timing check | Verify combinational delay | LOW |

### Test Commands
```bash
COVERAGE=1 pytest val/common/test_math_adder_half.py -v
```

---

## math_adder_full.sv

### Truth Table (Exhaustive)
| i_a | i_b | i_c | ow_sum | ow_carry |
|-----|-----|-----|--------|----------|
| 0 | 0 | 0 | 0 | 0 |
| 0 | 0 | 1 | 1 | 0 |
| 0 | 1 | 0 | 1 | 0 |
| 0 | 1 | 1 | 0 | 1 |
| 1 | 0 | 0 | 1 | 0 |
| 1 | 0 | 1 | 0 | 1 |
| 1 | 1 | 0 | 0 | 1 |
| 1 | 1 | 1 | 1 | 1 |

### Scenarios
| ID | Scenario | Description | Priority |
|----|----------|-------------|----------|
| FA-01 | All combinations | Test all 8 input combinations | HIGH |
| FA-02 | Carry propagation | Verify carry out for sum ≥ 2 | HIGH |
| FA-03 | Random patterns | 100 random input triples | MEDIUM |

### Test Commands
```bash
COVERAGE=1 pytest val/common/test_math_adder_full.py -v
```

---

## math_subtractor_half.sv

### Truth Table (Exhaustive)
| i_a | i_b | ow_diff | ow_borrow |
|-----|-----|---------|-----------|
| 0 | 0 | 0 | 0 |
| 0 | 1 | 1 | 1 |
| 1 | 0 | 1 | 0 |
| 1 | 1 | 0 | 0 |

### Scenarios
| ID | Scenario | Description | Priority |
|----|----------|-------------|----------|
| HS-01 | All combinations | Test all 4 input combinations | HIGH |
| HS-02 | Borrow generation | Verify borrow when a < b | HIGH |
| HS-03 | Random patterns | 100 random input pairs | MEDIUM |

### Test Commands
```bash
COVERAGE=1 pytest val/common/test_math_subtractor_half.py -v
```

---

## math_subtractor_full.sv

### Truth Table (Exhaustive)
| i_a | i_b | i_borrow_in | ow_diff | ow_borrow |
|-----|-----|-------------|---------|-----------|
| 0 | 0 | 0 | 0 | 0 |
| 0 | 0 | 1 | 1 | 1 |
| 0 | 1 | 0 | 1 | 1 |
| 0 | 1 | 1 | 0 | 1 |
| 1 | 0 | 0 | 1 | 0 |
| 1 | 0 | 1 | 0 | 0 |
| 1 | 1 | 0 | 0 | 0 |
| 1 | 1 | 1 | 1 | 1 |

### Scenarios
| ID | Scenario | Description | Priority |
|----|----------|-------------|----------|
| FS-01 | All combinations | Test all 8 input combinations | HIGH |
| FS-02 | Borrow propagation | Verify borrow chain behavior | HIGH |
| FS-03 | Random patterns | 100 random input triples | MEDIUM |

### Test Commands
```bash
COVERAGE=1 pytest val/common/test_math_subtractor_full.py -v
# Note: May be in test_math_subtractor_full_nbit.py
```

---

## math_adder_carry_save.sv

### Description
3-input, 2-output adder cell: sum + carry_out = a + b + c

### Scenarios
| ID | Scenario | Description | Priority |
|----|----------|-------------|----------|
| CSA-01 | All combinations | Test all 8 input combinations | HIGH |
| CSA-02 | Output verification | sum = a⊕b⊕c, carry = majority(a,b,c) | HIGH |
| CSA-03 | Multi-bit test | Test N-bit configuration | MEDIUM |

### Test Commands
```bash
COVERAGE=1 pytest val/common/test_math_adder_carry_save.py -v
```

---

## Batch Test Command

```bash
# Run all Level 0 math primitive tests
cd /mnt/data/github/rtldesignsherpa/val/common
PYTHONPATH=/mnt/data/github/rtldesignsherpa/bin:$PYTHONPATH \
COVERAGE=1 REG_LEVEL=FUNC SIM=verilator WAVES=0 \
pytest test_math_adder_half.py test_math_adder_full.py \
  test_math_subtractor_half.py test_math_adder_carry_save.py -v
```

## Coverage Verification

After running tests:
```bash
# Check coverage annotation
verilator_coverage --annotate-all --annotate /tmp/level0_math \
  val/common/coverage_data/merged/merged_coverage_*.dat

# View per-module coverage
for f in /tmp/level0_math/math_adder*.sv /tmp/level0_math/math_subtractor*.sv; do
  echo "=== $(basename $f) ==="
  grep -c "%000000" "$f" || echo "0 uncovered"
done
```
