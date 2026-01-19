# Level 0 Testplan: Data Integrity Primitives

## Modules Covered
- dataint_parity.sv
- dataint_checksum.sv

## Target Coverage: 95%+

---

## dataint_parity.sv

### Description
Parameterized parity generator/checker. Supports even and odd parity.

### Parameters
- DATA_WIDTH: Width of data input
- PARITY_TYPE: 0=even, 1=odd

### Scenarios
| ID | Scenario | Description | Priority |
|----|----------|-------------|----------|
| PAR-01 | Even parity gen | XOR all bits | HIGH |
| PAR-02 | Odd parity gen | Inverted XOR | HIGH |
| PAR-03 | Zero data | All zeros input | HIGH |
| PAR-04 | All ones | All ones input | HIGH |
| PAR-05 | Single bit | Each bit position | HIGH |
| PAR-06 | Check mode | Verify parity check logic | HIGH |
| PAR-07 | Error injection | Wrong parity detected | MEDIUM |
| PAR-08 | Random data | 100 random patterns | MEDIUM |

### Truth Table (4-bit even parity)
| Data | Expected Parity |
|------|-----------------|
| 0000 | 0 |
| 0001 | 1 |
| 0011 | 0 |
| 0111 | 1 |
| 1111 | 0 |

### Test Commands
```bash
COVERAGE=1 pytest val/common/test_dataint_parity.py -v
```

---

## dataint_checksum.sv

### Description
Simple additive checksum calculator. Sums all bytes/words.

### Parameters
- DATA_WIDTH: Width of input data
- CHUNK_WIDTH: Width of each chunk to sum

### Scenarios
| ID | Scenario | Description | Priority |
|----|----------|-------------|----------|
| CHK-01 | Zero data | Checksum of zeros = 0 | HIGH |
| CHK-02 | Single chunk | One non-zero chunk | HIGH |
| CHK-03 | Multiple chunks | Sum several values | HIGH |
| CHK-04 | Overflow wrap | Sum exceeds checksum width | HIGH |
| CHK-05 | Max values | All chunks at max | MEDIUM |
| CHK-06 | Verify mode | Check existing checksum | HIGH |
| CHK-07 | Random data | 100 random patterns | MEDIUM |

### Example (8-bit checksum, 4 bytes)
```
Data: 0x12 0x34 0x56 0x78
Sum:  0x12 + 0x34 + 0x56 + 0x78 = 0x114
Checksum (8-bit): 0x14 (truncated)
```

### Test Commands
```bash
COVERAGE=1 pytest val/common/test_dataint_checksum.py -v
```

---

## Batch Test Command

```bash
# Run all Level 0 data integrity tests
cd /mnt/data/github/rtldesignsherpa/val/common
PYTHONPATH=/mnt/data/github/rtldesignsherpa/bin:$PYTHONPATH \
COVERAGE=1 REG_LEVEL=FUNC SIM=verilator WAVES=0 \
pytest test_dataint_parity.py test_dataint_checksum.py -v
```

## Coverage Gaps to Watch

### dataint_parity.sv
- Different DATA_WIDTH configurations
- Both PARITY_TYPE settings
- Parity check error detection path

### dataint_checksum.sv
- Overflow/wrap behavior
- Different CHUNK_WIDTH settings
- Checksum verification mode
