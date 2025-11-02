# CAM Testing Module Documentation

## Overview

The `CamTB` class provides comprehensive testing for Content Addressable Memory (CAM) implementations. It validates tag storage, retrieval, state management, and capacity handling with systematic test patterns that ensure proper CAM functionality across all operating conditions.

## Purpose and Use Cases

### When to Use CamTB
- Testing CAM implementations with tag-based addressing
- Verifying proper full/empty state detection
- Validating tag marking and invalidation operations
- Ensuring correct capacity management
- Testing associative lookup functionality

### CAM Fundamentals
Content Addressable Memory allows data retrieval based on content rather than address:
- **Tags**: Data values stored in the CAM
- **Valid/Invalid**: State management for each entry
- **Full/Empty**: Capacity status indicators
- **Associative Search**: Content-based lookup operations

## Configuration

### Environment Variables
- `PARAM_N`: Tag width in bits (determines tag value range)
- `PARAM_DEPTH`: Number of entries the CAM can store
- `SEED`: Random number generator seed for reproducible tests
- `DUT`: Device under test identifier

### Expected DUT Interface

```verilog
module cam #(
    parameter N = 8,        // Tag width
    parameter DEPTH = 16    // Number of entries
) (
    input                i_clk,              // Clock
    input                i_rst_n,            // Active low reset
    
    // Tag operations
    input  [N-1:0]       i_tag_in_valid,    // Tag to mark valid
    input                i_mark_valid,       // Mark tag valid strobe
    input  [N-1:0]       i_tag_in_invalid,  // Tag to mark invalid  
    input                i_mark_invalid,     // Mark tag invalid strobe
    
    // Tag status query
    input  [N-1:0]       i_tag_in_status,   // Tag to check status
    output               ow_tag_status,      // Tag status (1=valid, 0=invalid)
    
    // CAM status
    output               ow_tags_empty,      // CAM is empty
    output               ow_tags_full        // CAM is full
);
```

## Test Methodologies

### 1. Main Loop Testing (`main_loop`)
**Purpose**: Comprehensive CAM lifecycle testing

**Test Sequence**:
1. **Fill Phase**: Add unique tags until CAM is full
2. **Validation Phase**: Verify all tags are properly stored
3. **Partial Removal**: Remove one tag, verify state changes
4. **Restoration**: Add tag back, verify full state
5. **Complete Cleanup**: Remove all tags, verify empty state

**Algorithm**:
```python
# Generate DEPTH unique random tags
tag_list = generate_unique_tags(DEPTH)

# Fill CAM and track successful additions
for tag in tag_list:
    await mark_one_valid(tag)
    verify_tag_added(tag)

# Test state transitions
verify_not_empty()
verify_full_if_all_added()

# Test removal and restoration
tag = remove_random_tag()
verify_state_changes()
restore_tag()

# Complete cleanup
remove_all_tags()
verify_empty_state()
```

### 2. Tag Operations

#### Mark Valid Operation (`mark_one_valid`)
**Purpose**: Add a tag to the CAM
```python
async def mark_one_valid(self, tag_value):
    self.dut.i_tag_in_valid.value = tag_value
    self.dut.i_mark_valid.value = 1
    await self.wait_clocks('i_clk', 1)
    self.dut.i_tag_in_valid.value = 0
    self.dut.i_mark_valid.value = 0
```

#### Mark Invalid Operation (`mark_one_invalid`)  
**Purpose**: Remove a tag from the CAM
```python
async def mark_one_invalid(self, tag_value):
    self.dut.i_tag_in_invalid.value = tag_value
    self.dut.i_mark_invalid.value = 1
    await self.wait_clocks('i_clk', 1)
    self.dut.i_tag_in_invalid.value = 0
    self.dut.i_mark_invalid.value = 0
```

#### Tag Status Check (`check_tag`)
**Purpose**: Verify tag presence in CAM
```python
async def check_tag(self, tag_value, expected_status):
    self.dut.i_tag_in_status.value = tag_value
    await self.wait_clocks('i_clk', 1)
    actual_status = self.dut.ow_tag_status.value
    assert actual_status == expected_status
```

### 3. State Verification

#### Empty State Checks
```python
def check_empty(self):
    assert self.dut.ow_tags_empty == 1, "CAM should be empty"
    
def check_not_empty(self):
    assert self.dut.ow_tags_empty == 0, "CAM should not be empty"
```

#### Full State Checks
```python
def check_full(self):
    assert self.dut.ow_tags_full == 1, "CAM should be full"
    
def check_not_full(self):
    assert self.dut.ow_tags_full == 0, "CAM should not be full"
```

### 4. Cleanup Operations (`cleanup_cam`)
**Purpose**: Reset CAM to known empty state

**Algorithm**:
1. **Discovery Phase**: Check all possible tag values to find valid entries
2. **Removal Phase**: Mark all discovered valid tags as invalid
3. **Verification Phase**: Confirm CAM is empty

```python
async def cleanup_cam(self):
    # Find all valid entries
    valid_tags = []
    for tag in range(2**self.N):
        if await self.is_tag_valid(tag):
            valid_tags.append(tag)
    
    # Remove all valid entries
    for tag in valid_tags:
        await self.mark_one_invalid(tag)
    
    # Verify empty state
    self.check_empty()
```

## Implementation Examples

### Basic CAM Test
```python
import cocotb
from CocoTBFramework.tbclasses.common.cam_testing import CamTB

@cocotb.test()
async def test_cam_basic(dut):
    """Basic CAM functionality test"""
    tb = CamTB(dut)
    
    # Start with reset
    tb.assert_reset()
    await tb.start_clock('i_clk', 10, 'ns')
    await tb.wait_clocks('i_clk', 5)
    tb.deassert_reset()
    await tb.wait_clocks('i_clk', 5)
    
    # Run main test
    await tb.main_loop()
```

### Advanced CAM Testing
```python
@cocotb.test()
async def test_cam_comprehensive(dut):
    """Comprehensive CAM testing"""
    tb = CamTB(dut)
    
    tb.print_settings()
    
    # Initialize
    tb.assert_reset()
    await tb.start_clock('i_clk', 10, 'ns')
    await tb.wait_clocks('i_clk', 10)
    tb.deassert_reset()
    await tb.wait_clocks('i_clk', 10)
    
    # Test empty state initially
    tb.check_empty()
    tb.check_not_full()
    
    # Test individual operations
    tag = 0x55
    await tb.mark_one_valid(tag)
    await tb.check_tag(tag, 1)  # Should be found
    tb.check_not_empty()
    
    await tb.mark_one_invalid(tag)
    await tb.check_tag(tag, 0)  # Should not be found
    
    # Run full test suite
    await tb.main_loop()
    
    # Final cleanup
    await tb.cleanup_cam()
```

### Custom Test Patterns
```python
@cocotb.test()
async def test_cam_patterns(dut):
    """Test specific tag patterns"""
    tb = CamTB(dut)
    
    # Initialize CAM
    await tb.reset_sequence()
    
    # Test specific patterns
    patterns = [0x00, 0xFF, 0xAA, 0x55, 0x0F, 0xF0]
    
    for pattern in patterns:
        # Add pattern
        await tb.mark_one_valid(pattern)
        await tb.check_tag(pattern, 1)
        
        # Remove pattern  
        await tb.mark_one_invalid(pattern)
        await tb.check_tag(pattern, 0)
    
    tb.check_empty()
```

## CAM-Specific Considerations

### 1. Capacity Management
- **Full Detection**: CAM correctly indicates when maximum capacity is reached
- **Empty Detection**: CAM correctly indicates when no valid entries exist
- **Transition States**: Proper state changes during add/remove operations

### 2. Tag Uniqueness
- **Duplicate Handling**: How CAM handles attempts to add existing tags
- **Collision Resolution**: Behavior when tag space exceeds physical capacity
- **Priority Schemes**: FIFO, LRU, or other replacement policies

### 3. Performance Characteristics
- **Lookup Speed**: Single-cycle associative search
- **Update Latency**: Clock cycles required for mark valid/invalid operations
- **Reset Behavior**: Time required to clear all entries

## Error Analysis

### Common Failure Patterns
1. **State Inconsistency**: Full/empty flags don't match actual content
2. **Tag Persistence**: Tags disappear unexpectedly or persist after invalidation
3. **Capacity Errors**: CAM accepts more tags than DEPTH parameter
4. **Lookup Failures**: Valid tags not found or invalid tags found

### Debug Information
```
SAFETY VIOLATION: CAM should be empty, but is not @ 12345ns
  Expected: ow_tags_empty = 1
  Actual:   ow_tags_empty = 0
  Debug: Check for incomplete tag removal or reset issues
```

### Troubleshooting Steps
1. **Verify Reset**: Ensure proper reset sequence clears all entries
2. **Check Timing**: Confirm clock edges align with data changes
3. **Interface Validation**: Verify signal names match DUT implementation
4. **Capacity Limits**: Ensure DEPTH parameter matches DUT configuration

## Configuration Examples

### Environment Setup
```bash
# 8-bit tags, 16 entry CAM
export PARAM_N=8
export PARAM_DEPTH=16
export SEED=42

# 16-bit tags, 64 entry CAM  
export PARAM_N=16
export PARAM_DEPTH=64
export SEED=12345
```

### Safety Configuration
```python
# For large CAMs, increase timeout limits
safety_limits = {
    'max_test_duration_minutes': 45,
    'progress_timeout_minutes': 10
}
tb = CamTB(dut, safety_limits)
```

This module provides comprehensive validation of CAM functionality, ensuring proper tag storage, retrieval, and state management across all operating conditions and capacity ranges.