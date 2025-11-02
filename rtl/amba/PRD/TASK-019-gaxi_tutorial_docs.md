# Task: TASK-019 - Create GAXI Integration Tutorial Documentation

## Priority
**P2 - Medium**

## Status
**🔴 Not Started**

## Description

Create comprehensive tutorial documentation for the GAXI multi-field integration examples in `rtl/amba/testcode/`. These examples demonstrate practical usage patterns for GAXI buffers with structured data (addr/ctrl/data fields).

## Background

**GAXI Testcode Modules:** `rtl/amba/testcode/` contains integration examples:
- `gaxi_skid_buffer_multi.sv` - Multi-field skid buffer wrapper
- `gaxi_skid_buffer_multi_sigmap.sv` - With signal mapping
- `gaxi_fifo_sync_multi.sv` - Multi-field sync FIFO
- `gaxi_fifo_async_multi.sv` - Multi-field async FIFO
- `gaxi_skid_buffer_async_multi.sv` - Multi-field async skid buffer

**Tests:** `val/integ_amba/` contains corresponding tests:
- `test_gaxi_buffer_multi.py`
- `test_gaxi_buffer_multi_sigmap.py`
- `test_gaxi_buffer_field.py`

**Purpose:** These examples show how to use GAXI buffers for real-world data structures (not just raw data bits).

## Prerequisites

- [x] GAXI modules functional
- [x] Integration tests passing
- [x] GAXI documentation complete (`docs/markdown/RTLAmba/gaxi/`)

## Deliverables

### 1. Tutorial: Multi-Field GAXI Buffers

**File:** `docs/markdown/TestTutorial/gaxi_multi_field_integration.md`

**Content Structure:**

```markdown
# GAXI Multi-Field Integration Tutorial

## Overview

Learn how to use GAXI buffers with structured data containing multiple fields
(address, control, data) instead of simple raw bits.

## Use Cases

**Why use multi-field wrappers?**
- Packet-based interfaces (addr + ctrl + payload)
- AXI-like interfaces (address phase + data phase)
- Network packets (header + data)
- Command interfaces (opcode + operands)

## Example 1: Skid Buffer with Multi-Field Data

**Scenario:** Buffer commands with addr, ctrl, and two data fields

### RTL Module

**File:** `rtl/amba/testcode/gaxi_skid_buffer_multi.sv`

[Show module code with annotations]

**Key Points:**
- Concatenates fields: {addr, ctrl, data1, data0}
- Single underlying gaxi_skid_buffer
- Type-safe field access on input/output

### Integration

[Show how to instantiate and connect]

### Test Example

**File:** `val/integ_amba/test_gaxi_buffer_multi.py`

[Show Python testbench code]

## Example 2: Signal Mapping Variant

**File:** `rtl/amba/testcode/gaxi_skid_buffer_multi_sigmap.sv`

[Explain signal mapping approach]

## Example 3: Async Multi-Field FIFO

**File:** `rtl/amba/testcode/gaxi_fifo_async_multi.sv`

**Scenario:** Cross clock domains with structured data

[Show CDC example with multi-field data]

## Design Patterns

### Pattern 1: Field Concatenation
### Pattern 2: Signal Mapping
### Pattern 3: Parameterized Field Widths

## Testing Strategies

[Explain test approaches from val/integ_amba/]

## Common Pitfalls

1. Field ordering (MSB vs LSB)
2. Unused count outputs
3. ...

## Related Modules

- [gaxi_skid_buffer](../RTLAmba/gaxi/gaxi_skid_buffer.md)
- [gaxi_fifo_sync](../RTLAmba/gaxi/gaxi_fifo_sync.md)
- [gaxi_fifo_async](../RTLAmba/gaxi/gaxi_fifo_async.md)
```

### 2. Tutorial: GAXI Field Configuration

**File:** `docs/markdown/TestTutorial/gaxi_field_configuration.md`

**Content Structure:**

```markdown
# GAXI Field Configuration Tutorial

## Overview

Learn how to use FieldConfig and FieldDefinition for protocol-agnostic
signal description and WaveDrom generation.

## Background

The GAXI testbench framework includes field configuration for:
- Automatic signal formatting (hex, decimal, binary)
- WaveDrom waveform generation
- Protocol-aware signal grouping

## Example: Field Definition

**From:** `bin/CocoTBFramework/tbclasses/wavedrom_user/gaxi.py`

[Show get_gaxi_field_config() implementation and explanation]

## Using Field Configuration

### In Tests
### In WaveDrom Generation
### Custom Field Definitions

## Field Types

### Address Fields (Hex Display)
### Data Fields (Hex Display)
### Control Fields (Binary Display)
### Count Fields (Decimal Display)

## Advanced Usage

### Multi-bit Fields
### Nested Structures
### Custom Formatters
```

### 3. Tutorial Index Update

**File:** `docs/markdown/TestTutorial/index.md` (update existing)

Add entries:
```markdown
## GAXI Integration Tutorials

- [Multi-Field GAXI Buffers](gaxi_multi_field_integration.md) - Using GAXI with structured data
- [GAXI Field Configuration](gaxi_field_configuration.md) - Protocol-agnostic signal formatting
- [WaveDrom GAXI Example](wavedrom_gaxi_example.md) - Existing WaveDrom tutorial
```

### 4. Advanced Examples Update

**File:** `docs/markdown/TestTutorial/advanced_examples.md` (update existing)

Add section:
```markdown
## GAXI Multi-Field Integration

The `rtl/amba/testcode/` directory contains advanced GAXI integration examples
showing how to use GAXI buffers with structured data.

### Available Examples

| Module | Purpose | Test |
|--------|---------|------|
| `gaxi_skid_buffer_multi.sv` | Multi-field skid buffer | `test_gaxi_buffer_multi.py` |
| `gaxi_skid_buffer_multi_sigmap.sv` | With signal mapping | `test_gaxi_buffer_multi_sigmap.py` |
| `gaxi_fifo_sync_multi.sv` | Sync FIFO with fields | `test_gaxi_buffer_multi.py` |
| `gaxi_fifo_async_multi.sv` | Async FIFO with fields | `test_gaxi_buffer_multi.py` |
| `gaxi_skid_buffer_async_multi.sv` | Async skid buffer with fields | `test_gaxi_buffer_multi.py` |

See [Multi-Field GAXI Buffers](gaxi_multi_field_integration.md) for detailed tutorial.
```

## Testing

**Verify Examples Still Work:**
```bash
cd val/integ_amba
pytest test_gaxi_buffer_multi.py -v
pytest test_gaxi_buffer_multi_sigmap.py -v
pytest test_gaxi_buffer_field.py -v
```

**Check Documentation Links:**
- [ ] All internal links work
- [ ] Code examples are accurate
- [ ] References to source files are correct

## Success Criteria

- [ ] `gaxi_multi_field_integration.md` created with comprehensive examples
- [ ] `gaxi_field_configuration.md` created explaining field system
- [ ] Tutorial index updated
- [ ] Advanced examples updated
- [ ] All 5 testcode modules documented
- [ ] Clear code examples with annotations
- [ ] Design patterns explained
- [ ] Common pitfalls documented
- [ ] Links to related documentation

## Design Decisions

1. **Focus on Integration:** Show real-world usage, not just API docs
   - Practical examples from testcode/
   - Explain why and when to use each pattern

2. **No WaveDroms Needed:** Focus on code and concepts
   - WaveDrom already covered in separate tutorial
   - Keep this focused on integration patterns

3. **Link to Existing Docs:** Reference, don't duplicate
   - Link to GAXI module docs for detailed specs
   - Link to test files for full code

4. **Progressive Complexity:**
   - Start simple (basic multi-field)
   - Progress to advanced (async with fields, signal mapping)

## Content Guidelines

**Code Examples:**
- Use actual code from `rtl/amba/testcode/`
- Add inline comments explaining key lines
- Show before/after for clarity

**Explanations:**
- Explain the "why" not just the "how"
- Use cases for each pattern
- Trade-offs and design decisions

**Testing:**
- Reference test files but don't duplicate all test code
- Show key testbench setup patterns
- Explain test methodology

## References

**RTL Modules:**
- `rtl/amba/testcode/gaxi_*_multi*.sv` (5 files)

**Tests:**
- `val/integ_amba/test_gaxi_buffer_multi.py`
- `val/integ_amba/test_gaxi_buffer_multi_sigmap.py`
- `val/integ_amba/test_gaxi_buffer_field.py`

**Framework:**
- `bin/CocoTBFramework/tbclasses/wavedrom_user/gaxi.py`

**Existing Docs:**
- `docs/markdown/RTLAmba/gaxi/` (GAXI module docs)
- `docs/markdown/TestTutorial/wavedrom_gaxi_example.md` (existing)

## Related Tasks

**Prerequisites:**
- GAXI module documentation complete (✅)
- GAXI WaveDrom integration complete (✅)

**Related:**
- TASK-017: APB WaveDrom
- TASK-018: AXI4 WaveDrom
- TASK-020: Identify tests needing waves

**Future:**
- Additional integration examples (as needed)
- Video tutorials (stretch goal)

---

**Task Owner:** TBD
**Created:** 2025-10-06
**Target Completion:** TBD
**Estimated Effort:** 4-6 hours
**Note:** No WaveDrom generation needed, focus on documentation
