# Level 0 Testplan: Encoders and Decoders

## Modules Covered
- encoder.sv
- decoder.sv
- encoder_priority_enable.sv
- bin2gray.sv
- gray2bin.sv
- bin_to_bcd.sv

## Target Coverage: 95%+

---

## encoder.sv

### Description
N-input to log2(N)-output binary encoder. Outputs index of highest set bit.

### Scenarios
| ID | Scenario | Description | Priority |
|----|----------|-------------|----------|
| ENC-01 | Single bit set | Test each input bit position | HIGH |
| ENC-02 | No bits set | Verify output when input = 0 | HIGH |
| ENC-03 | Multiple bits | Verify priority (highest wins) | MEDIUM |
| ENC-04 | All bits set | Input = all 1s | MEDIUM |
| ENC-05 | Parameter N=4 | Default width | HIGH |
| ENC-06 | Parameter N=8 | Larger width | MEDIUM |

### Test Matrix (N=4)
| Input | Expected Output |
|-------|-----------------|
| 0001 | 0 |
| 0010 | 1 |
| 0100 | 2 |
| 1000 | 3 |
| 1111 | 3 (highest) |

### Test Commands
```bash
COVERAGE=1 pytest val/common/test_encoder.py -v
```

---

## decoder.sv

### Description
log2(N)-input to N-output one-hot decoder.

### Scenarios
| ID | Scenario | Description | Priority |
|----|----------|-------------|----------|
| DEC-01 | All inputs | Test each input value 0 to N-1 | HIGH |
| DEC-02 | Enable low | Output = 0 when disabled | HIGH |
| DEC-03 | Parameter N=4 | 2-to-4 decoder | HIGH |
| DEC-04 | Parameter N=8 | 3-to-8 decoder | MEDIUM |

### Test Matrix (N=4)
| Input | Enable | Expected Output |
|-------|--------|-----------------|
| 00 | 1 | 0001 |
| 01 | 1 | 0010 |
| 10 | 1 | 0100 |
| 11 | 1 | 1000 |
| XX | 0 | 0000 |

### Test Commands
```bash
COVERAGE=1 pytest val/common/test_decoder.py -v
```

---

## encoder_priority_enable.sv

### Description
Priority encoder with per-bit enable. Outputs index of lowest enabled set bit.

### Scenarios
| ID | Scenario | Description | Priority |
|----|----------|-------------|----------|
| EPE-01 | Single request | One bit enabled and set | HIGH |
| EPE-02 | Priority order | Lower index wins | HIGH |
| EPE-03 | Enable masking | Disabled bits ignored | HIGH |
| EPE-04 | No valid bits | All disabled or cleared | HIGH |
| EPE-05 | Walking ones | Test each position | MEDIUM |

### Test Commands
```bash
COVERAGE=1 pytest val/common/test_encoder_priority_enable.py -v
```

---

## bin2gray.sv

### Description
Binary to Gray code converter. Gray code changes only 1 bit per increment.

### Conversion Formula
```
gray[n] = binary[n]                    (MSB)
gray[i] = binary[i+1] ^ binary[i]      (other bits)
```

### Scenarios
| ID | Scenario | Description | Priority |
|----|----------|-------------|----------|
| B2G-01 | All values | Test 0 to 2^N-1 | HIGH |
| B2G-02 | Single-bit change | Verify adjacent values differ by 1 bit | HIGH |
| B2G-03 | Parameter WIDTH=4 | Default width | HIGH |
| B2G-04 | Parameter WIDTH=8 | Larger width | MEDIUM |

### Test Matrix (WIDTH=4)
| Binary | Gray |
|--------|------|
| 0000 | 0000 |
| 0001 | 0001 |
| 0010 | 0011 |
| 0011 | 0010 |
| 0100 | 0110 |
| ... | ... |

### Test Commands
```bash
COVERAGE=1 pytest val/common/test_bin2gray.py -v
```

---

## gray2bin.sv

### Description
Gray code to binary converter. Inverse of bin2gray.

### Conversion Formula
```
binary[n] = gray[n]                    (MSB)
binary[i] = binary[i+1] ^ gray[i]      (other bits, XOR cascade)
```

### Scenarios
| ID | Scenario | Description | Priority |
|----|----------|-------------|----------|
| G2B-01 | All values | Test all Gray codes 0 to 2^N-1 | HIGH |
| G2B-02 | Round-trip | bin→gray→bin = bin | HIGH |
| G2B-03 | Parameter WIDTH=4 | Default width | HIGH |
| G2B-04 | Parameter WIDTH=8 | Larger width | MEDIUM |

### Test Commands
```bash
COVERAGE=1 pytest val/common/test_gray2bin.py -v
```

---

## bin_to_bcd.sv

### Description
Binary to BCD (Binary-Coded Decimal) converter using double-dabble algorithm.

### Scenarios
| ID | Scenario | Description | Priority |
|----|----------|-------------|----------|
| BCD-01 | Single digit | Values 0-9 | HIGH |
| BCD-02 | Two digits | Values 10-99 | HIGH |
| BCD-03 | Max value | Maximum for bit width | HIGH |
| BCD-04 | Zero | Input = 0 | HIGH |
| BCD-05 | Random values | Sample of random inputs | MEDIUM |

### Test Commands
```bash
COVERAGE=1 pytest val/common/test_bin_to_bcd.py -v
```

---

## Batch Test Command

```bash
# Run all Level 0 encoder/decoder tests
cd /mnt/data/github/rtldesignsherpa/val/common
PYTHONPATH=/mnt/data/github/rtldesignsherpa/bin:$PYTHONPATH \
COVERAGE=1 REG_LEVEL=FUNC SIM=verilator WAVES=0 \
pytest test_encoder.py test_decoder.py test_encoder_priority_enable.py \
  test_bin2gray.py test_bin_to_bcd.py -v
```

## Coverage Verification

```bash
# Check encoder/decoder coverage
for f in /tmp/level0_enc/encoder*.sv /tmp/level0_enc/decoder*.sv; do
  module=$(basename "$f" .sv)
  total=$(grep -cE "^[ %][0-9]{6}" "$f")
  uncovered=$(grep -c "%000000" "$f")
  covered=$((total - uncovered))
  pct=$((covered * 100 / total))
  echo "$module: $pct% ($covered/$total)"
done
```
