# Level 0 Testplan: Simple Counters

## Modules Covered
- counter_ring.sv
- counter_johnson.sv

## Target Coverage: 95%+

---

## counter_ring.sv

### Description
One-hot ring counter. Single bit rotates through WIDTH positions.

### Sequence (WIDTH=4)
```
State 0: 0001
State 1: 0010
State 2: 0100
State 3: 1000
State 4: 0001 (wraps)
```

### Scenarios
| ID | Scenario | Description | Priority |
|----|----------|-------------|----------|
| RC-01 | Reset state | Output = 1 (LSB set) | HIGH |
| RC-02 | Full rotation | Complete WIDTH cycles | HIGH |
| RC-03 | Wraparound | State N-1 → State 0 | HIGH |
| RC-04 | Enable control | Hold when enable=0 | HIGH |
| RC-05 | Enable toggle | Pause and resume | MEDIUM |
| RC-06 | Reset mid-rotate | Reset during sequence | MEDIUM |
| RC-07 | One-hot check | Only 1 bit set at any time | HIGH |
| RC-08 | Parameter WIDTH=4 | Default configuration | HIGH |
| RC-09 | Parameter WIDTH=8 | Larger configuration | MEDIUM |

### Test Commands
```bash
COVERAGE=1 pytest val/common/test_counter_ring.py -v
```

---

## counter_johnson.sv

### Description
Johnson (twisted ring) counter. MSB inverted and fed to LSB.
Produces 2*WIDTH unique states.

### Sequence (WIDTH=4)
```
State 0: 0000
State 1: 0001
State 2: 0011
State 3: 0111
State 4: 1111
State 5: 1110
State 6: 1100
State 7: 1000
State 8: 0000 (wraps)
```

### Properties
- 2*WIDTH unique states
- Only 1 bit changes per transition (Gray-like)
- Glitch-free decoding

### Scenarios
| ID | Scenario | Description | Priority |
|----|----------|-------------|----------|
| JC-01 | Reset state | Output = 0000 | HIGH |
| JC-02 | Fill sequence | 0→1→11→111→1111 | HIGH |
| JC-03 | Drain sequence | 1111→1110→1100→1000 | HIGH |
| JC-04 | Full cycle | All 2*WIDTH states | HIGH |
| JC-05 | Wraparound | State 2N-1 → State 0 | HIGH |
| JC-06 | Enable control | Hold when enable=0 | HIGH |
| JC-07 | Enable toggle | Pause and resume | MEDIUM |
| JC-08 | Reset mid-cycle | Reset during sequence | MEDIUM |
| JC-09 | Single-bit change | Verify each transition | MEDIUM |
| JC-10 | Parameter WIDTH=4 | Default configuration | HIGH |
| JC-11 | Parameter WIDTH=8 | Larger configuration | MEDIUM |

### Test Commands
```bash
COVERAGE=1 pytest val/common/test_counter_johnson.py -v
```

---

## Batch Test Command

```bash
# Run all Level 0 simple counter tests
cd /mnt/data/github/rtldesignsherpa/val/common
PYTHONPATH=/mnt/data/github/rtldesignsherpa/bin:$PYTHONPATH \
COVERAGE=1 REG_LEVEL=FUNC SIM=verilator WAVES=0 \
pytest test_counter_ring.py test_counter_johnson.py -v
```

## Coverage Verification

```bash
# After running tests
for f in /tmp/cov/counter_ring.sv /tmp/cov/counter_johnson.sv; do
  module=$(basename "$f" .sv)
  total=$(grep -cE "^[ %][0-9]{6}" "$f")
  uncovered=$(grep -c "%000000" "$f")
  covered=$((total - uncovered))
  echo "$module: $covered/$total covered"
done
```

## Coverage Gaps to Watch

### counter_ring.sv
- Enable=0 hold path (low hit count)
- Reset during rotation
- Different WIDTH parameters

### counter_johnson.sv
- Enable=0 hold path (low hit count)
- Reset during cycle
- Full 2*WIDTH state coverage
- Transition between fill and drain phases
