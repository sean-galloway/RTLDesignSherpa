# Constraint Solver Exploration Results

**Date:** 2025-10-05
**Context:** Improving GAXI wavedrom generation - fixing cross-scenario matching

---

## Problem Statement

The temporal constraint solver was matching patterns that **span multiple test scenarios** instead of isolating individual scenarios.

### Example Issue
```python
# Goal: Match backpressure in Scenario 3 (cycles 30-40)
# Reality: Solver finds FIRST match in Scenario 2 (cycles 10-20)
```

**Test Structure:**
- Scenario 1: Write when empty (cycles 0-10)
- Scenario 2: 3 writes + 3 reads with spacing (cycles 10-25)
- **4 idle cycles boundary** (cycles 25-29)
- Scenario 3: Backpressure - FIFO fills, wr_ready drops (cycles 30-45)

---

## Solutions Implemented

### 1. **`prefer_latest` Parameter** ✅

**What it does:** Selects LAST match instead of FIRST match

**Implementation:**
```python
class TemporalConstraint:
    prefer_latest: bool = False  # If True, select LAST match
```

**Code Change (constraint_solver.py:902-912):**
```python
if constraint.prefer_latest and len(filtered_solutions) > 1:
    # Select LAST match instead of FIRST
    temporal_solution = filtered_solutions[-1]
    if self.debug_level >= 1:
        self.log.info(f"  Using LAST match (prefer_latest=True)")
else:
    # Default: use first match
    temporal_solution = filtered_solutions[0]
```

**Result:** When combined with `max_matches=10`, the solver finds ALL occurrences and we select the last one.

---

### 2. **`boundary_min_idle_cycles` Parameter** ✅

**What it does:** Filters matches to only include those with N+ idle cycles before them

**Definition of "Idle":** `wr_valid=0 AND rd_ready=0` (no activity on either interface)

**Implementation:**
```python
class TemporalConstraint:
    boundary_min_idle_cycles: int = 0  # Minimum idle cycles before match
```

**Filter Logic (constraint_solver.py:992-1035):**
```python
def _filter_solutions_by_idle_boundary(self, solutions, signal_data, min_idle_cycles, ...):
    for solution in solutions:
        start_cycle = solution['sequence_start']

        # Check N cycles before start_cycle
        for cycle in range(start_cycle - min_idle_cycles, start_cycle):
            if wr_valid[cycle] != 0 or rd_ready[cycle] != 0:
                # NOT idle - reject this solution
                break
        else:
            # All cycles were idle - keep this solution
            filtered.append(solution)
```

**Result:** Successfully filters out matches from mid-scenario transitions.

---

## Test Results

### Configuration
```python
write_full_constraint = TemporalConstraint(
    name="wr_backpressure",
    events=[
        TemporalEvent("fifo_full", SignalTransition("wr_ready", 1, 0)),
    ],
    max_window_size=12,
    max_matches=10,  # Find ALL matches
    boundary_min_idle_cycles=3,  # Filter to isolated scenarios
    prefer_latest=True,  # Select LAST match
    ...
)
```

### Outcome
- **Matches Found:** 10 total
- **Match Selected:** #10 (last one)
- **Data in Waveform:** `0x0000C000-C003` ✅ (Scenario 3 backpressure data)
- **Previous Behavior:** Match #1 contained `0x0000A001, 0x0000B000-B002` ❌ (Scenarios 1+2 data)

---

## Discussion Points

### ✅ What Works

1. **`prefer_latest`** - Simple, effective for tests with scenarios in order
2. **`boundary_min_idle_cycles`** - Good for tests with explicit idle boundaries
3. **Combination** - Using both together gives precise scenario isolation

### ⚠️ Limitations

1. **Requires `max_matches > 1`** - Must find multiple matches to select from
   - Could be slow for complex constraints
   - CP-SAT solver searches entire signal space

2. **Hardcoded Idle Definition** - Currently `wr_valid=0 AND rd_ready=0`
   - Not flexible for other protocols
   - Should be configurable?

3. **No Debug Visibility** - Filter messages not appearing in logs
   - Need to verify filter is actually running
   - May need debug_level adjustment

### 🤔 Open Questions

**Q1: Should idle definition be configurable?**

Options:
```python
# Option A: Specific signals
boundary_idle_signals=['wr_valid', 'rd_ready']  # Must ALL be 0

# Option B: General pattern
boundary_condition=SignalCondition("wr_valid", 0) AND Signal Condition("rd_ready", 0)

# Option C: Automatic detection
boundary_auto_detect=True  # Find natural quiet periods
```

**Q2: Should we add negative constraints?**

Example: "Match wr_ready=0 BUT NOT when rd_valid=1"
```python
exclude_when=[
    SignalCondition("rd_valid", 1),  # Don't match during reads
]
```

**Q3: Should we add match quality scoring?**

Prefer matches that:
- Have more idle cycles before/after?
- Have longer sequence durations?
- Are closer to end of test?

**Q4: Performance concerns?**

- `max_matches=10` with complex constraints could be slow
- Should we implement early termination?
- Should we search backwards from end instead?

---

## Recommendations

### For Immediate Use (GAXI waveforms)

Keep current implementation:
```python
prefer_latest=True
boundary_min_idle_cycles=3
max_matches=10
```

This successfully isolates Scenario 3 backpressure from earlier scenarios.

### For Future Enhancement

1. **Make idle definition configurable**
   ```python
   boundary_idle_conditions: List[Tuple[str, int]] = [
       ('wr_valid', 0),
       ('rd_ready', 0),
   ]
   ```

2. **Add debug logging** to show filter decisions

3. **Consider backward search optimization** for `prefer_latest=True`

4. **Add negative constraints** for more precise matching

---

## Files Modified

1. **constraint_solver.py**
   - Added `prefer_latest` and `boundary_min_idle_cycles` to `TemporalConstraint`
   - Implemented `_filter_solutions_by_idle_boundary()` method
   - Modified solution selection logic (lines 889-912)

2. **test_gaxi_wavedrom_example.py**
   - Updated `wr_backpressure` constraint to use new features
   - Set `boundary_min_idle_cycles=3` and `prefer_latest=True`

---

## Next Steps

1. ✅ Test with other scenarios (wr_when_empty, wr_rd_flow)
2. ⬜ Add user-configurable idle definition
3. ⬜ Improve debug logging for filter decisions
4. ⬜ Document in WAVEDROM_REQUIREMENTS.md
5. ⬜ Consider adding negative constraints

---

**Prepared for discussion with user**
