<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# WaveDrom Requirements and Best Practices

**Version:** 1.2
**Last Updated:** 2025-10-07
**Purpose:** Define mandatory requirements for wavedrom timing diagram generation

---

## Critical Requirements

### 1. **Clock Signal - ALWAYS Required**

**Rule:** Every waveform MUST include the clock signal as the first signal.

**Rationale:** Designers need a timing reference to understand when events occur relative to clock edges.

**Implementation:**
```python
# ALWAYS bind clock first
wave_solver.add_signal_binding('clk', 'axi_aclk')  # or appropriate clock

# ALWAYS include in signals_to_show
signals_to_show=['clk', 'rst_n', ...]  # clk first
```

**WaveJSON Output:**
```json
"signal": [
  {
    "name": "clk",
    "wave": "p............"  // Clock pattern
  },
  ...
]
```

### 2. **Initial Setup Cycles - Never Start at Time 0**

**Rule:** Waveforms MUST have 2-3 cycles of stable initial state before events begin.

**Rationale:** Designers need to see stable initial conditions. Starting events at time 0 makes it impossible to distinguish initial state from transitions.

**Implementation:**
```python
# === Start Sampling ===
await wave_solver.start_sampling()

# === Initial Setup ===
# CRITICAL: Provide stable initial state
dut.signal1.value = 0
dut.signal2.value = 0
await RisingEdge(dut.clk)
await RisingEdge(dut.clk)
await RisingEdge(dut.clk)  # 3 cycles minimum

# NOW start actual test events
dut.signal1.value = 1
...
```

**Context Cycles:** The `context_cycles_before` parameter adds dead cycles BEFORE the matched pattern. To ensure arrows never start at cycle 0:
- **Initial setup (3 cycles):** Stable state at start of entire simulation
- **Context before (≥3):** MUST be at least 3 to push pattern start beyond initial cycles
- **Example:** `context_cycles_before=5` ensures patterns start at cycle 8+ (3 setup + 5 context)

### 3. **Arrows Must Show Meaningful Relationships**

**Rule:** Arrows MUST connect events that have causal or temporal relationships.

**Examples of GOOD arrow usage:**
- ✅ `psel → penable` (APB: setup causes enable)
- ✅ `wr_valid → wr_ready` (GAXI: write request causes ready response)
- ✅ `fifo_full → backpressure` (Full condition causes flow control)
- ✅ `write → read_valid` (Data written propagates to read)

**Examples of BAD arrow usage:**
- ❌ `ready asserted → valid asserts` (This is normal handshake, not a stall)
- ❌ Arrows on unrelated signals
- ❌ Arrows without clear meaning

**Implementation:**
```python
# Good: Shows backpressure (writer blocked)
TemporalEvent("write_blocked", SignalTransition("wr_ready", 1, 0)),
TemporalEvent("writer_waiting", SignalTransition("wr_valid", 1, 1)),
# Concurrent = both happen at same time = stall/backpressure

# Bad: Misinterprets normal operation
TemporalEvent("ready_high", SignalTransition("wr_ready", 1, 1)),
TemporalEvent("then_write", SignalTransition("wr_valid", 0, 1)),
# Sequence = write after ready = NORMAL, not a problem!
```

### 4. **Arrow Types - Use Appropriately**

**Available Arrow Types:**
- `~>` - Squiggly: Async/handshake relationships (GAXI, AXI)
- `->` - Direct: Sequential/causal relationships (APB, state machines)
- `<->` - Bidirectional: Duration/span of sequence
- `->>` - Double: Strong dependency (use sparingly)
- `=>` - Thick: Critical path (use sparingly)

**Auto-Selection Logic:**
```python
if has_valid and has_ready:
    # GAXI/AXI handshake - async
    arrow = f"{start}~>{end} {label}"
elif is_apb:
    # APB sequential
    arrow = f"{start}->{end} {label}"
else:
    # Generic duration
    arrow = f"{start}<->{end} Sequence: {duration} cycles"
```

### 5. **Internal Signals - Show Critical State**

**Rule:** Include internal signals that explain behavior.

**Critical Internals to Show:**
- **FIFO/Buffer:** `count`, `full`, `empty`, `wr_ptr`, `rd_ptr`
- **State Machines:** `state`, `next_state`
- **Arbiters:** `grant`, `request_pending`
- **Monitors:** `transaction_active`, `error_flag`

**Implementation:**
```python
# Bind internal signals
wave_solver.add_signal_binding('count', 'fifo_count')
wave_solver.add_signal_binding('full', 'fifo_full')

# Include in waveform
signals_to_show=['clk', 'wr_valid', 'wr_ready', 'count', 'full']
```

**Rationale:** Internal signals show WHY interface signals behave as they do.

### 6. **Signal Naming - Preserve Interface Prefixes**

**Rule:** Signal names MUST preserve interface prefixes (wr_, rd_, etc.) for clarity.

**Implementation:** Signal display names now automatically preserve prefixes:
```python
# Binding creates unique display names
wave_solver.add_signal_binding('wr_valid', 'wr_valid')
wave_solver.add_signal_binding('rd_valid', 'rd_valid')
wave_solver.add_signal_binding('count', 'count')

signals_to_show=['clk', 'wr_valid', 'wr_ready', 'rd_valid', 'rd_ready', 'count']
```

**WaveJSON Output:**
```json
"signal": [
  {"name": "clk", ...},
  {"name": "wr_valid", ...},  // NOT "valid"
  {"name": "wr_ready", ...},  // NOT "ready"
  {"name": "rd_valid", ...},  // Distinct from wr_valid
  {"name": "count", ...}
]
```

**Grouping (Optional):** Use '|' in signals_to_show for visual organization:
```python
signals_to_show=['clk', 'rst_n', '|', 'wr_valid', 'wr_ready', '|', 'count']
# Separators help organize: Clock/Reset | Write Interface | Internals
```

### 7. **Reset Signal - Include for Clocked Blocks**

**Rule:** For synchronous designs, include reset signal.

**Implementation:**
```python
wave_solver.add_signal_binding('rst_n', 'aresetn')  # Active-low reset
# or
wave_solver.add_signal_binding('rst', 'reset')      # Active-high reset

signals_to_show=['clk', 'rst_n', ...]  # After clock, before data
```

### 8. **Trim/Context Margins - Configurable**

**Rule:** Provide configurable context cycles, with sensible defaults.

**Options:**
- **Minimal (1,1):** Tight waveforms for simple patterns
- **Moderate (3,3):** Balanced view with some context
- **Default (None,None):** Auto-calculate (~25% of window)

**Implementation:**
```python
# Allow user to configure
context_before = {'minimal': 1, 'moderate': 3, 'default': None}[mode]
context_after = {'minimal': 1, 'moderate': 3, 'default': None}[mode]

constraint = TemporalConstraint(
    ...
    context_cycles_before=context_before,
    context_cycles_after=context_after,
)
```

### 9. **Signal Grouping - MANDATORY for ALL Waveforms**

**Rule:** ALL signals MUST be grouped logically by function/bus using WaveDrom labeled groups.

**Rationale:**
- Groups make waveforms easier to read and understand
- Logical grouping shows relationship between signals
- Consistent grouping aids comparison across different scenarios

**Group Order (Standard):**
1. **Clock/Reset** - Timing reference (ALWAYS FIRST)
2. **Control Signals** - Transaction control (psel, penable, valid, ready, etc.)
3. **Address** - Address information
4. **Data** - Data payload (separate write/read if applicable)
5. **Qualifiers/Status** - Additional control (strb, prot, error flags, etc.)
6. **Internal State** - Debug/observability (count, state, pointers, etc.)

**Implementation:**
```python
# Use nested arrays for WaveDrom labeled groups
common_signals = [
    ['Clock/Reset', 'clk', 'rst_n'],
    '|',  # Visual separator
    ['APB Control', 'psel', 'penable', 'pwrite', 'pready'],
    '|',
    ['APB Address', 'paddr'],
    '|',
    ['APB Data', 'pwdata', 'prdata'],
    '|',
    ['APB Qualifiers', 'pstrb', 'pprot', 'pslverr']
]

constraint = TemporalConstraint(
    name="scenario",
    events=[...],
    signals_to_show=common_signals  # Use same grouping for ALL scenarios
)
```

**WaveJSON Output:**
```json
"signal": [
  ["Clock/Reset",
    {"name": "clk", "wave": "p...."},
    {"name": "rst_n", "wave": "1...."}
  ],
  {},
  ["APB Control",
    {"name": "psel", "wave": "01..."},
    {"name": "penable", "wave": "0.1.."}
  ],
  ...
]
```

**Key Requirements:**
- ✅ ALL waveforms in a test MUST use the SAME grouped signal list
- ✅ Clock/Reset group ALWAYS included FIRST
- ✅ All signals MUST be in a labeled group (no ungrouped signals)
- ✅ Use `'|'` separators between groups for visual clarity
- ✅ Define signal grouping ONCE, reuse for all constraints in test

### 10. **Quality Over Quantity - Focus on Meaningful Scenarios**

**Rule:** Generate 3-4 high-quality waveforms that clearly illustrate key behaviors, rather than 12+ waveforms where most don't make sense.

**Rationale:**
- Too many waveforms overwhelm the user
- Each waveform should tell a clear story about the design
- Poor quality waveforms (wrong constraints, nonsensical patterns) are worse than no waveforms

**Selection Criteria for Scenarios:**
1. **Coverage:** Does it show a unique aspect of the design?
2. **Clarity:** Will a designer immediately understand what's being shown?
3. **Relevance:** Does it demonstrate normal operation OR an important edge case?
4. **Completeness:** Does it show the full transaction (not just fragments)?

**Good Scenario Examples:**
- ✅ APB Write with wait states (shows backpressure handling)
- ✅ APB Read with immediate response (shows zero-wait operation)
- ✅ Back-to-back transactions (shows back-pressure release and transaction pipelining)
- ✅ FIFO full→empty sequence (shows complete buffer cycle)

**Bad Scenario Examples:**
- ❌ Partial transactions (missing setup or completion)
- ❌ Nonsensical signal transitions (constraints don't match reality)
- ❌ Redundant scenarios (showing the same thing multiple ways)
- ❌ Scenarios that never occur in normal operation

**Implementation Checklist:**
```python
# Before adding a new scenario, ask:
# 1. Does this show something the other scenarios don't?
# 2. Will the constraint actually match real signal behavior?
# 3. Can I explain in one sentence what this waveform demonstrates?
# 4. Would I want to see this in design documentation?

# If any answer is "no" or "unsure", reconsider the scenario
```

**Recommended Scenario Count:**
- Simple modules (FIFO, skid buffer): **3-4 scenarios**
- Complex modules (AXI, APB): **4-6 scenarios**
- Maximum for any module: **8 scenarios** (only if truly necessary)

---

## Common Patterns

### Pattern 1: GAXI/FIFO Waveforms

```python
# Clock and reset
wave_solver.add_signal_binding('clk', 'axi_aclk')
wave_solver.add_signal_binding('rst_n', 'axi_aresetn')

# Write interface
wave_solver.add_signal_binding('wr_valid', 'wr_valid')
wave_solver.add_signal_binding('wr_ready', 'wr_ready')
wave_solver.add_signal_binding('wr_data', 'wr_data')

# Read interface (for combined view)
wave_solver.add_signal_binding('rd_valid', 'rd_valid')
wave_solver.add_signal_binding('rd_ready', 'rd_ready')
wave_solver.add_signal_binding('rd_data', 'rd_data')

# Internal state
wave_solver.add_signal_binding('count', 'fifo_count')

# Scenarios
signals_to_show=['clk', 'rst_n', 'wr_valid', 'wr_ready', 'wr_data', 'count']  # Write focus
signals_to_show=['clk', 'wr_valid', 'wr_data', 'rd_valid', 'rd_data', 'count']  # Coupling
```

### Pattern 2: APB Waveforms

```python
# Clock always first
wave_solver.add_signal_binding('clk', 'pclk')
wave_solver.add_signal_binding('rst_n', 'presetn')

# APB signals
wave_solver.add_signal_binding('psel', 'psel')
wave_solver.add_signal_binding('penable', 'penable')
wave_solver.add_signal_binding('pready', 'pready')
wave_solver.add_signal_binding('pwrite', 'pwrite')
wave_solver.add_signal_binding('paddr', 'paddr')
wave_solver.add_signal_binding('pwdata', 'pwdata')
wave_solver.add_signal_binding('prdata', 'prdata')

signals_to_show=['clk', 'psel', 'penable', 'pready', 'pwrite', 'paddr', 'pwdata']
```

### Pattern 3: Backpressure/Stall

```python
# Show TRUE backpressure: valid high while ready low
TemporalConstraint(
    name="backpressure",
    events=[
        TemporalEvent("blocked", SignalTransition("ready", 1, 0)),
        TemporalEvent("waiting", SignalTransition("valid", 1, 1)),
    ],
    temporal_relation=TemporalRelation.CONCURRENT,  # Simultaneous
    signals_to_show=['clk', 'valid', 'ready', 'data', 'count']
)
```

---

## Integration with All Tests

**Goal:** Eventually add wavedrom to ALL tests in the repository.

**Approach:**
1. Start with critical tests (GAXI, APB, AXI4)
2. Use test_gaxi_wavedrom_example.py as template
3. Follow these requirements for consistency
4. Add wavedrom to existing tests incrementally

**Checklist for Adding WaveDrom to a Test:**
- [ ] Clock signal bound and shown first
- [ ] 2-3 initial setup cycles before events
- [ ] Reset signal included (for sync designs)
- [ ] Internal signals shown to explain behavior
- [ ] Arrows show meaningful relationships (not normal operation)
- [ ] Appropriate arrow types used
- [ ] No duplicate signal names
- [ ] Configurable context margins
- [ ] Test documented with scenario descriptions

---

## Anti-Patterns to Avoid

### ❌ Anti-Pattern 1: Starting at Time 0
```python
# BAD
await wave_solver.start_sampling()
dut.valid.value = 1  # Immediate event
```

```python
# GOOD
await wave_solver.start_sampling()
dut.valid.value = 0
await RisingEdge(dut.clk)  # Setup cycles
await RisingEdge(dut.clk)
dut.valid.value = 1  # Now event
```

### ❌ Anti-Pattern 2: Missing Clock
```python
# BAD
signals_to_show=['valid', 'ready', 'data']  # No clock!
```

```python
# GOOD
signals_to_show=['clk', 'valid', 'ready', 'data']  # Clock first
```

### ❌ Anti-Pattern 3: Meaningless Arrows
```python
# BAD: Normal handshake labeled as problem
TemporalEvent("ready_first", SignalTransition("ready", 0, 1)),
TemporalEvent("then_valid", SignalTransition("valid", 0, 1)),
# Arrow: "ready→valid" suggests problem, but this is NORMAL!
```

```python
# GOOD: Show actual problem
TemporalEvent("stall", SignalTransition("ready", 1, 0)),
TemporalEvent("blocked", SignalTransition("valid", 1, 1)),
# Arrow: "stall~>blocked" shows backpressure
```

### ❌ Anti-Pattern 4: Duplicate Names
```python
# BAD
wave_solver.add_signal_binding('valid', 'wr_valid')
wave_solver.add_signal_binding('valid', 'rd_valid')  # Duplicate!
```

```python
# GOOD
wave_solver.add_signal_binding('wr_valid', 'wr_valid')
wave_solver.add_signal_binding('rd_valid', 'rd_valid')
```

---

## Maintenance

**When Adding New Features:**
1. Update this requirements document
2. Update test_gaxi_wavedrom_example.py as reference
3. Ensure backward compatibility with existing tests
4. Add new arrow types or patterns to Common Patterns section

**Version History:**
- v1.2 (2025-10-07): Mandatory grouping and quality requirements
  - **BREAKING:** ALL waveforms MUST use signal grouping (labeled groups)
  - Clock/Reset MUST be in first group (ALWAYS included)
  - Quality over quantity: 3-4 meaningful scenarios better than 12 nonsensical ones
  - Scenario selection criteria and checklist added
  - Maximum recommended scenario counts by module complexity
- v1.1 (2025-10-05): Signal naming and grouping improvements
  - Preserve interface prefixes (wr_, rd_) in display names
  - Added grouping support with '|' separators
  - Fixed duplicate signal name issues
- v1.0 (2025-10-05): Initial requirements based on user feedback
  - Clock always required
  - Initial setup cycles mandatory
  - Arrows must be meaningful
  - Backpressure correctly identified
  - Anti-patterns documented

**Maintained By:** RTL Design Sherpa Project
**Last Review:** 2025-10-07
