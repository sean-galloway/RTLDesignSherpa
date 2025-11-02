# Common RTL Library - Documentation Style Guide

**Version:** 1.0
**Last Updated:** 2025-10-15
**Purpose:** Standardize module header documentation across all 86 modules

---

## Documentation Template

Every module MUST include a comprehensive header comment block immediately before the `module` declaration.

### Standard Header Template

```systemverilog
//==============================================================================
// Module: <module_name>
//==============================================================================
// Description:
//   <Concise 1-3 sentence description of module functionality>
//   <Additional details if needed>
//
// Features:
//   - <Key feature 1>
//   - <Key feature 2>
//   - <Key feature 3>
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   <PARAM_NAME>:
//     Description: <What this parameter controls>
//     Type: <int/logic/etc>
//     Range: <Valid range, e.g., 1 to 64>
//     Default: <Default value>
//     Units: <If applicable, e.g., MHz, ms, cycles>
//     Constraints: <Any dependencies or requirements>
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   Inputs:
//     i_clk:        Clock input (rising edge active)
//     i_rst_n:      Asynchronous active-low reset
//     <port_name>:  <Brief description, width if not obvious>
//
//   Outputs:
//     o_<name>:     <Description, timing if critical>
//
//   Inouts:
//     io_<name>:    <Description>
//
//------------------------------------------------------------------------------
// Timing:
//------------------------------------------------------------------------------
//   Clock-to-Q:     <N> cycle(s)
//   Combinational:  <If applicable>
//   Pipeline Depth: <N> stage(s)
//   Latency:        <N> cycle(s) from input valid to output valid
//
//------------------------------------------------------------------------------
// Behavior:
//------------------------------------------------------------------------------
//   <Detailed description of operation>
//   <State transitions if FSM>
//   <Edge cases and special conditions>
//
//   [OPTIONAL: Wavedrom timing diagram for complex timing]
//
//------------------------------------------------------------------------------
// Usage Example:
//------------------------------------------------------------------------------
//   <module_name> #(
//       .PARAM1(value1),
//       .PARAM2(value2)
//   ) u_instance_name (
//       .i_clk      (clock_signal),
//       .i_rst_n    (reset_n),
//       .i_input    (input_signal),
//       .o_output   (output_signal)
//   );
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - <Important usage note 1>
//   - <Constraint or limitation 2>
//   - <Design trade-off 3>
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - <related_module_1.sv> - <Brief relationship description>
//   - <related_module_2.sv> - <Brief relationship description>
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_<module_name>.py
//   Run: pytest val/common/test_<module_name>.py -v
//   Coverage: <percentage>
//
//------------------------------------------------------------------------------
// References:
//------------------------------------------------------------------------------
//   - <Book/Paper/Standard if applicable>
//   - <Algorithm name and source>
//
//------------------------------------------------------------------------------
// Version History:
//------------------------------------------------------------------------------
//   2025-XX-XX: Initial implementation
//   2025-XX-XX: <Description of changes>
//
//==============================================================================

module <module_name> #(
    ...
```

---

## Section Guidelines

### 1. Module Name and Banner

```systemverilog
//==============================================================================
// Module: counter_bin
//==============================================================================
```

**Rules:**
- Use full-width separator (78 characters of `=`)
- Module name must match actual module declaration
- Consistent formatting across all modules

### 2. Description

```systemverilog
// Description:
//   Binary up counter with configurable maximum value. Counts from 0 to
//   MAX_VALUE-1, then overflows and wraps back to 0. Useful for iteration
//   control, event counting, and modulo arithmetic.
//
// Features:
//   - Configurable bit width (1-64 bits)
//   - Parameterizable maximum count value
//   - Overflow flag for detecting wraparound
//   - Enable control for gating count operation
```

**Rules:**
- First sentence: High-level "what it does"
- Second sentence: Key behavioral detail
- Third sentence: Common use cases
- Features: 3-5 bullet points highlighting capabilities
- Avoid redundant information

### 3. Parameters

```systemverilog
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   WIDTH:
//     Description: Bit width of counter
//     Type: int
//     Range: 1 to 64
//     Default: 8
//     Constraints: Must be sufficient to represent MAX_VALUE
//
//   MAX_VALUE:
//     Description: Maximum count value before overflow
//     Type: int
//     Range: 1 to (2^WIDTH - 1)
//     Default: (2**WIDTH) - 1
//     Constraints: Must fit within WIDTH bits
```

**Rules:**
- Document ALL parameters
- Include: Type, Range, Default, Constraints
- Explain parameter interdependencies
- Use consistent formatting
- If no parameters, use "N/A" section

### 4. Ports

```systemverilog
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   Inputs:
//     i_clk:        Clock input (rising edge active)
//     i_rst_n:      Asynchronous active-low reset
//     i_enable:     Count enable (active-high)
//
//   Outputs:
//     o_count[WIDTH-1:0]:  Current count value
//     o_overflow:          Overflow flag (1 = count wrapped)
```

**Rules:**
- Group by direction (Inputs, Outputs, Inouts)
- Always document clock and reset first
- Include width for buses (even if parameterized)
- Specify active level (high/low)
- Describe timing relationship if non-trivial

### 5. Timing

```systemverilog
//------------------------------------------------------------------------------
// Timing:
//------------------------------------------------------------------------------
//   Latency:        1 cycle (registered output)
//   Clock-to-Q:     Single flip-flop delay
//   Combinational:  N/A (fully registered)
```

**Rules:**
- Specify latency (input valid → output valid)
- Note if combinational or registered
- Include pipeline depth if applicable
- Critical timing paths if relevant

### 6. Behavior

```systemverilog
//------------------------------------------------------------------------------
// Behavior:
//------------------------------------------------------------------------------
//   On each rising clock edge (if i_enable=1):
//   1. Increment o_count by 1
//   2. If o_count == MAX_VALUE:
//      - Assert o_overflow (1 cycle pulse)
//      - Wrap o_count to 0 on next cycle
//   3. If i_enable=0, hold current count
//
//   Reset behavior (i_rst_n=0):
//   - o_count = 0
//   - o_overflow = 0
```

**Rules:**
- Step-by-step operational description
- Cover normal operation
- Cover reset behavior
- Cover edge cases (enable, overflow, etc.)
- Use numbered lists for clarity

### 7. Wavedrom Timing Diagram (OPTIONAL)

**When to Include:**
- Complex timing relationships
- Multi-cycle operations
- State machine transitions
- Protocol handshakes
- Difficult-to-visualize behavior

**Example:**
```systemverilog
//   Timing Diagram (WIDTH=4, MAX_VALUE=5):
//
//   {signal: [
//     {name: 'i_clk',      wave: 'p........'},
//     {name: 'i_rst_n',    wave: '01.......'},
//     {name: 'i_enable',   wave: '0.1......'},
//     {name: 'o_count',    wave: 'x.2345x2.', data: ['0','1','2','3','4','0','1']},
//     {name: 'o_overflow', wave: '0.....10.'}
//   ]}
```

**Rules:**
- Keep diagrams concise (<10 clock cycles)
- Show key transitions and edge cases
- Include parameter values used in diagram
- Add explanatory data labels

### 8. Usage Example

```systemverilog
//------------------------------------------------------------------------------
// Usage Example:
//------------------------------------------------------------------------------
//   counter_bin #(
//       .WIDTH(8),
//       .MAX_VALUE(100)
//   ) u_event_counter (
//       .i_clk      (clk),
//       .i_rst_n    (rst_n),
//       .i_enable   (event_valid),
//       .o_count    (event_count),
//       .o_overflow (max_events_reached)
//   );
```

**Rules:**
- Show realistic instantiation
- Include parameter overrides
- Use meaningful signal names
- Align port connections vertically

### 9. Notes

```systemverilog
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - Counter wraps to 0 after reaching MAX_VALUE (modulo behavior)
//   - o_overflow is a 1-cycle pulse, not a sticky flag
//   - i_enable gates counting but does NOT reset the counter
//   - For exact modulo-N, set MAX_VALUE = N
//   - Synthesis: Infers efficient binary counter logic
```

**Rules:**
- Important usage guidelines
- Common pitfalls and gotchas
- Design trade-offs
- Synthesis implications
- Performance considerations

### 10. Related Modules

```systemverilog
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - counter_load_clear.sv - Counter with load and clear control
//   - counter_freq_invariant.sv - Time-based counter (ms/us)
//   - counter_bingray.sv - Gray code counter for CDC
```

**Rules:**
- List 2-5 closely related modules
- Brief description of relationship
- Help users find alternatives

### 11. Test Reference

```systemverilog
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_counter_bin.py
//   Run: pytest val/common/test_counter_bin.py -v
//   Coverage: 95%
```

**Rules:**
- Always provide test file location
- Include command to run test
- Report functional coverage if known

### 12. References (OPTIONAL)

```systemverilog
//------------------------------------------------------------------------------
// References:
//------------------------------------------------------------------------------
//   - "Digital Design and Computer Architecture" by Harris & Harris
//   - "Advanced FPGA Design" by Steve Kilts, Chapter 5
```

**Rules:**
- Include for complex algorithms
- Cite books, papers, standards
- Provide chapter/section if applicable
- Only include if truly relevant

### 13. Version History (OPTIONAL)

```systemverilog
//------------------------------------------------------------------------------
// Version History:
//------------------------------------------------------------------------------
//   2025-09-01: Initial implementation
//   2025-09-15: Added overflow flag
//   2025-10-01: Fixed off-by-one in MAX_VALUE comparison
```

**Rules:**
- Date in YYYY-MM-DD format
- Concise change description
- Useful for tracking evolution
- Optional for most modules

---

## Module Categories and Documentation Priority

### Priority 1: High-Value, Frequently Used Modules (Add Wavedrom)

**Counters:**
- counter_bin.sv ✅ **Add Wavedrom**
- counter_load_clear.sv ✅ **Add Wavedrom**
- counter_freq_invariant.sv ✅ **Add Wavedrom**

**Arbiters:**
- arbiter_round_robin.sv ✅ **Add Wavedrom**
- arbiter_round_robin_weighted.sv ✅ **Add Wavedrom**
- arbiter_priority_encoder.sv ✅ **Add Wavedrom**

**Data Integrity:**
- dataint_crc.sv ✅ **Add Wavedrom**
- dataint_ecc_hamming_encode_secded.sv
- dataint_ecc_hamming_decode_secded.sv

**Synchronizers:**
- glitch_free_n_dff_arn.sv ✅ **Add Wavedrom**
- reset_sync.sv ✅ **Add Wavedrom**

**Clock Utilities:**
- clock_divider.sv ✅ **Add Wavedrom**
- clock_gate_ctrl.sv

**FIFOs:**
- fifo_sync.sv ✅ **Add Wavedrom**
- fifo_async.sv ✅ **Add Wavedrom**

### Priority 2: Important but Simple (No Wavedrom Needed)

**Math:**
- count_leading_zeros.sv
- bin2gray.sv, gray2bin.sv
- All adders/subtractors (simple combinational)

**Encoders/Decoders:**
- encoder.sv, decoder.sv
- priority_encoder.sv

**Shifters:**
- shifter_barrel.sv
- shifter_lfsr*.sv

### Priority 3: Supporting/Internal Modules (Minimal Docs)

**Math Primitives:**
- math_adder_half.sv, math_adder_full.sv
- math_subtractor_half.sv, math_subtractor_full.sv
- math_multiplier_basic_cell.sv

**Brent-Kung/Wallace Tree Components:**
- All math_adder_brent_kung_*.sv
- All math_multiplier_wallace_tree_*.sv

---

## Wavedrom Best Practices

### When to Include Wavedrom

✅ **Include for:**
- Multi-cycle operations (counters, FSMs)
- Handshake protocols (valid/ready)
- Complex timing (arbitration, CDC)
- Non-obvious behavior (pulse vs level, delays)

❌ **Skip for:**
- Pure combinational logic (adders, encoders)
- Single-cycle operations
- Self-explanatory modules

### Wavedrom Format

```systemverilog
//   Timing Diagram (<describe scenario>):
//
//   {signal: [
//     {name: 'clk',        wave: 'p........'},
//     {name: 'rst_n',      wave: '01.......'},
//     {name: 'input',      wave: 'x.2.3.4..', data: ['A','B','C']},
//     {name: 'output',     wave: 'x...2.3.4', data: ['A','B','C']},
//     {},
//     {name: 'note',       wave: 'x.2...4..', data: ['Start', 'Done']}
//   ]}
```

**Tips:**
- Keep to 8-10 clock cycles
- Use `data:` for values
- Use `{}` for separator lines
- Add descriptive `name:` for annotations
- Test in online Wavedrom editor

---

## Documentation Checklist

Before considering a module "complete":

- [ ] Module name banner with separators
- [ ] Concise description (1-3 sentences)
- [ ] Feature list (3-5 bullets)
- [ ] ALL parameters documented (type, range, default, constraints)
- [ ] ALL ports documented (grouped by direction)
- [ ] Timing information (latency, clock-to-Q, combinational)
- [ ] Behavior description (step-by-step operation)
- [ ] **Wavedrom diagram (if Priority 1 module)**
- [ ] Usage example with realistic instantiation
- [ ] Notes section (gotchas, constraints, trade-offs)
- [ ] Related modules listed (2-5 modules)
- [ ] Test file reference (location + command)
- [ ] References (if algorithm-based)
- [ ] Spell-checked and grammar-checked

---

## Automation Tools

### Documentation Audit

```bash
# Run audit script
python bin/audit_module_documentation.py

# View reports
cat reports/documentation/module_documentation_audit.md
```

### Template Generator (Future Work)

Create `bin/generate_module_docs.py` to:
- Parse existing modules
- Extract parameters/ports automatically
- Generate template header
- Preserve custom content

---

## Examples

See exemplar documentation in:
- `rtl/common/counter_bin.sv` (after update)
- `rtl/common/arbiter_round_robin.sv` (after update)
- `rtl/common/dataint_crc.sv` (after update)

---

## Version History

- 2025-10-15: Initial style guide creation
- Format standardized across all 86 modules
- Wavedrom integration for Priority 1 modules

---

**Document Owner:** RTL Design Sherpa Project
**Maintained By:** Claude Code
**Next Review:** 2026-01-15
