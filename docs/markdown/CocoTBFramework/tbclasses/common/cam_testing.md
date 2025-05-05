# CAM Testing

## Overview

The `cam_testing` module provides a testbench for verifying Content Addressable Memory (CAM) implementations. It supports testing of CAM operations including tag insertion, lookup, and removal. The module handles parameter configuration, test vector generation, and comprehensive verification of CAM functionality.

## Class Definition

```python
class CamTB(TBBase):
    """Testbench for Content Addressable Memory implementations.
    
    This class provides functionality for testing CAM operations
    including tag insertion, lookup, and removal.
    """

    def __init__(self, dut):
        """Initialize the testbench with design under test.

        Args:
            dut: The cocotb design under test object
        """
        TBBase.__init__(self, dut)
        # Gather the settings from the Parameters to verify them
        self.N = self.convert_to_int(os.environ.get('PARAM_N', '0'))
        self.DEPTH = self.convert_to_int(os.environ.get('PARAM_DEPTH', '0'))
        self.max_val = (2**self.N)-1
```

## Key Features

- Testing of CAM tag insertion and removal
- Status checking (empty, full, not empty, not full)
- Tag validation and uniqueness testing
- Random tag generation for varied test scenarios
- Full-state verification (filling and emptying the CAM)
- CAM cleanup utilities for test isolation

## Primary Methods

### main_loop

Main testing loop that exercises all CAM functionality with random tags.

```python
async def main_loop(self):
    """Main Test
    
    This method tests the CAM with a sequence of random tags,
    filling the CAM, removing one tag, then refilling and emptying.
    """
    self.log.info("Main Test")
    # Generate DEPTH unique tags
    tag_list = []
    while len(tag_list) < self.DEPTH:
        tag = random.randint(0x00, self.max_val)
        if tag not in tag_list:
            tag_list.append(tag)

    self.log.info(f'{tag_list=}')

    # Track which tags are actually added successfully
    valid_tags = []

    # Add tags to the CAM
    for tag in tag_list:
        await self.mark_one_valid(tag)
        # Verify tag was added successfully
        self.dut.i_tag_in_status.value = tag
        await self.wait_clocks('i_clk', 1)
        if self.dut.ow_tag_status == 1:
            valid_tags.append(tag)

    # Continue with tests...
```

### mark_one_valid

Marks a tag as valid (inserts it into the CAM).

```python
async def mark_one_valid(self, tag_value):
    """Mark a tag as valid (insert into CAM).
    
    Args:
        tag_value: The tag value to insert
    """
    # Implementation...
```

### mark_one_invalid

Marks a tag as invalid (removes it from the CAM).

```python
async def mark_one_invalid(self, tag_value):
    """Mark a tag as invalid (remove from CAM).
    
    Args:
        tag_value: The tag value to remove
    """
    # Implementation...
```

### check_tag

Checks if a tag is present in the CAM.

```python
async def check_tag(self, tag_value, check):
    """Check if a tag is present in the CAM.
    
    Args:
        tag_value: The tag value to check
        check: Expected result (1=present, 0=not present)
    """
    # Implementation...
```

### check_empty / check_not_empty

Verifies the empty status flag.

```python
def check_empty(self):
    """Check if CAM is empty."""
    # Implementation...

def check_not_empty(self):
    """Check if CAM is not empty."""
    # Implementation...
```

### check_full / check_not_full

Verifies the full status flag.

```python
def check_full(self):
    """Check if CAM is full."""
    # Implementation...

def check_not_full(self):
    """Check if CAM is not full."""
    # Implementation...
```

### cleanup_cam

Utility to clear all entries from the CAM.

```python
async def cleanup_cam(self):
    """Clear all entries from the CAM"""
    # Implementation...
```

## Test Methodology

The CAM testing methodology includes several approaches:

1. **Tag Insertion**: Add tags and verify they are present
2. **Tag Removal**: Remove tags and verify they are no longer present  
3. **Status Checking**: Verify empty/full flags are correctly managed
4. **Fullness Testing**: Fill the CAM to capacity and verify behavior
5. **Cleanup Testing**: Remove all tags and verify empty state

During testing, the module:
1. Generates unique random tags to fill the CAM
2. Verifies each tag is properly inserted
3. Tests the CAM in full state for correct behavior
4. Removes tags and verifies proper removal
5. Cleans up by emptying the CAM completely

## Implementation Approach

The implementation provides detailed verification of CAM operations:

```python
# Process one tag
random.shuffle(valid_tags)
tag = valid_tags.pop()
await self.mark_one_invalid(tag)
self.check_not_empty()
self.check_not_full()

# Add tag back
await self.mark_one_valid(tag)
valid_tags.append(tag)

# Check if CAM is full if we expect it to be
if len(valid_tags) == self.DEPTH:
    self.check_full()

# Remove all tags we know are valid
for tag in valid_tags:
    await self.mark_one_invalid(tag)
    # Verify tag is removed
    self.dut.i_tag_in_status.value = tag
    await self.wait_clocks('i_clk', 1)
    assert self.dut.ow_tag_status == 0, f"Tag 0x{tag:x} was not properly removed"

self.clear_interface()
await self.wait_clocks('i_clk', 1)
self.check_empty()
self.check_not_full()
```

## Example Usage

Basic usage of the CAM testbench:

```python
from CocoTBFramework.tbclasses.common.cam_testing import CamTB

@cocotb.test()
async def test_cam(dut):
    # Create testbench
    tb = CamTB(dut)
    
    # Print settings
    tb.print_settings()
    
    # Run main test loop
    await tb.main_loop()
```

Running isolated tests:

```python
@cocotb.test()
async def test_cam_operations(dut):
    # Create testbench
    tb = CamTB(dut)
    
    # Test individual operations
    await tb.cleanup_cam()  # Start clean
    
    # Add a tag
    tag = 0x42
    await tb.mark_one_valid(tag)
    await tb.check_tag(tag, 1)  # Should be present
    
    # Remove the tag
    await tb.mark_one_invalid(tag)
    await tb.check_tag(tag, 0)  # Should be gone
```

## Implementation Notes

- DUT signals use standard names: i_tag_in_valid, i_mark_valid, etc.
- PARAM_N environment variable controls tag width
- PARAM_DEPTH environment variable controls CAM depth
- Random tag generation ensures uniqueness to avoid duplicate entries
- Tags are verified after insertion/removal to confirm correct operation
- Cleanup method safely removes all entries for test isolation
- Status flags are checked at each stage to verify state management

## See Also

- [FIFO Testing](fifo_sync_testing.md) - Similar approach for FIFO verification
- [Memory Model](../../components/memory_model.md) - Memory modeling component

## Navigation

[↑ Common Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
