# Level 0 Testplan: Clock Utilities

## Modules Covered
- clock_divider.sv
- clock_gate_ctrl.sv
- clock_pulse.sv

## Target Coverage: 95%+

---

## clock_divider.sv

### Description
Programmable clock frequency divider. Outputs clock at input_freq/DIVISOR.

### Scenarios
| ID | Scenario | Description | Priority |
|----|----------|-------------|----------|
| CD-01 | Divide by 2 | Basic 50% duty cycle | HIGH |
| CD-02 | Divide by 4 | Quarter frequency | HIGH |
| CD-03 | Divide by odd | Asymmetric duty cycle | MEDIUM |
| CD-04 | Divide by 1 | Pass-through mode | HIGH |
| CD-05 | Reset behavior | Output low on reset | HIGH |
| CD-06 | Enable control | Hold output when disabled | MEDIUM |

### Timing Verification
- Count rising edges of input vs output
- Verify ratio matches DIVISOR parameter
- Check duty cycle where applicable

### Test Commands
```bash
COVERAGE=1 pytest val/common/test_clock_divider.py -v
```

---

## clock_gate_ctrl.sv

### Description
Glitch-free clock gating control cell. Gates clock based on enable signal.

### Key Requirements
1. No glitches on gated clock output
2. Enable sampled on falling edge of clock
3. Output transitions only on clock edges

### Scenarios
| ID | Scenario | Description | Priority |
|----|----------|-------------|----------|
| CGC-01 | Enable high | Clock passes through | HIGH |
| CGC-02 | Enable low | Clock gated (output low) | HIGH |
| CGC-03 | Enable toggle | Switch while running | HIGH |
| CGC-04 | Glitch-free | No partial pulses | HIGH |
| CGC-05 | Reset behavior | Output state on reset | MEDIUM |
| CGC-06 | Rapid toggle | Fast enable on/off | MEDIUM |

### Glitch Detection
```python
# Monitor for pulses shorter than half clock period
async def check_glitch(signal, min_width):
    while True:
        await RisingEdge(signal)
        start = get_sim_time()
        await FallingEdge(signal)
        width = get_sim_time() - start
        assert width >= min_width, "Glitch detected!"
```

### Test Commands
```bash
COVERAGE=1 pytest val/common/test_clock_gate_ctrl.py -v
```

---

## clock_pulse.sv

### Description
Generates a single-cycle pulse from a level signal (edge detector).

### Scenarios
| ID | Scenario | Description | Priority |
|----|----------|-------------|----------|
| CP-01 | Rising edge | Pulse on 0→1 transition | HIGH |
| CP-02 | Falling edge | Pulse on 1→0 transition (if supported) | MEDIUM |
| CP-03 | Pulse width | Exactly 1 clock cycle | HIGH |
| CP-04 | Back-to-back | Rapid input toggles | MEDIUM |
| CP-05 | Long high | Input stays high, only one pulse | HIGH |
| CP-06 | Reset during pulse | Reset clears state | MEDIUM |

### Timing Diagram
```
input:  ____/‾‾‾‾‾‾‾‾‾\____
output: ____/‾\_____________   (single cycle pulse)
```

### Test Commands
```bash
COVERAGE=1 pytest val/common/test_clock_pulse.py -v
```

---

## Batch Test Command

```bash
# Run all Level 0 clock utility tests
cd /mnt/data/github/rtldesignsherpa/val/common
PYTHONPATH=/mnt/data/github/rtldesignsherpa/bin:$PYTHONPATH \
COVERAGE=1 REG_LEVEL=FUNC SIM=verilator WAVES=0 \
pytest test_clock_divider.py test_clock_gate_ctrl.py test_clock_pulse.py -v
```

## Coverage Gaps to Watch

### clock_gate_ctrl.sv
Common uncovered paths:
- Clock gate toggle during active operation
- Race condition avoidance logic
- Scan mode bypass (if present)

### clock_divider.sv
Common uncovered paths:
- Edge cases at DIVISOR boundaries
- Counter overflow handling
- Odd divisor asymmetric output

### clock_pulse.sv
Common uncovered paths:
- Multiple rapid edges
- Reset during pulse generation
- Enable/disable transitions
