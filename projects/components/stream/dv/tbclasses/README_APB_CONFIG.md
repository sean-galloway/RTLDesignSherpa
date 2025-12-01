# StreamCoreTB APB Configuration Interface

## Overview

StreamCoreTB has been extended to support APB configuration for `stream_top` testing. The testbench now supports **two modes**:

1. **stream_core mode**: Direct signal configuration (existing functionality)
2. **stream_top mode**: APB configuration via PeakRDL-generated registers (new functionality)

## Architecture

```
StreamCoreTB
├── Direct Signal Mode (stream_core)
│   ├── kick_off_channel() - Uses direct signals (apb_addr, apb_valid)
│   ├── Direct config signals (cfg_*)
│   └── No APB master needed
│
└── APB Configuration Mode (stream_top)
    ├── init_apb_master() - Initialize APB BFM
    ├── APB register access (0x100-0x3FF)
    ├── Still uses kick_off_channel() for 0x000-0x03F
    └── APB master handles all config writes
```

## Address Space

| Range | Purpose | Interface |
|-------|---------|-----------|
| 0x000-0x03F | Channel kick-off | Existing `kick_off_channel()` |
| 0x100-0x3FF | Configuration registers | New APB methods |

## Usage Pattern for stream_top

### Step 1: Initialize Testbench with APB Master

```python
from projects.components.stream.dv.tbclasses.stream_core_tb import StreamCoreTB

# Create testbench
tb = StreamCoreTB(
    dut,
    num_channels=8,
    addr_width=64,
    data_width=512,
    axi_id_width=8,
    fifo_depth=4096
)

# Setup clocks and reset
await tb.setup_clocks_and_reset()

# Initialize APB master (stream_top only!)
await tb.init_apb_master()
```

### Step 2: Configure via APB Registers

```python
# Read version register
version = await tb.read_version()
print(f"STREAM version: 0x{version:08X}")

# Enable STREAM globally
await tb.enable_global()

# Enable specific channels
await tb.enable_channel_mask(0xFF)  # All 8 channels

# Read global status
status = await tb.read_global_status()
print(f"Global status: 0x{status:08X}")
```

### Step 3: Use Existing Descriptor/Transfer Methods

```python
# Existing methods work the same in both modes
tb.write_descriptor(
    addr=0x10000,
    src_addr=0x80000000,
    dst_addr=0x90000000,
    length=64,  # beats
    next_ptr=0,
    last=True,
    channel_id=0
)

# Kick off channel (uses 0x000-0x03F range)
await tb.kick_off_channel(0, 0x10000)

# Wait for completion
await tb.wait_for_channel_idle(0, timeout_us=10000)

# Verify data transfer
result = tb.verify_transfer(
    src_addr=0x80000000,
    dst_addr=0x90000000,
    num_beats=64
)
```

## Available APB Configuration Methods

### Basic Register Access

```python
# Write to APB register
await tb.write_apb_register(addr, data)

# Read from APB register
data = await tb.read_apb_register(addr)
```

### Global Control

```python
# Enable/disable globally
await tb.enable_global()
await tb.disable_global()

# Read global status
status = await tb.read_global_status()

# Read version
version = await tb.read_version()
```

### Channel Control

```python
# Enable channels (8-bit mask)
await tb.enable_channel_mask(0xFF)  # All channels
await tb.enable_channel_mask(0x0F)  # Channels 0-3 only

# Reset channels
await tb.reset_channels(0xFF)  # Reset all

# Read channel idle status
idle_status = await tb.read_channel_idle_status()
if (idle_status & (1 << 0)):
    print("Channel 0 is idle")

# Read per-channel state
state = await tb.read_channel_state(0)
print(f"Channel 0 state: 0x{state:08X}")
```

## Register Map Reference

Use `StreamRegisterMap` for human-readable register names:

```python
from projects.components.stream.dv.tbclasses.stream_core_tb import StreamRegisterMap

# Global registers
StreamRegisterMap.GLOBAL_CTRL       # 0x100
StreamRegisterMap.GLOBAL_STATUS     # 0x104
StreamRegisterMap.VERSION           # 0x108

# Per-channel control
StreamRegisterMap.CHANNEL_ENABLE    # 0x120
StreamRegisterMap.CHANNEL_RESET     # 0x124

# Per-channel status
StreamRegisterMap.DESC_ENGINE_IDLE  # 0x140
StreamRegisterMap.SCHEDULER_IDLE    # 0x144
StreamRegisterMap.CHANNEL_IDLE      # 0x148

# Helper methods
addr = StreamRegisterMap.get_ch_ctrl_low_addr(0)   # Channel 0 kick-off low
addr = StreamRegisterMap.get_ch_state_addr(3)      # Channel 3 state
name = StreamRegisterMap.get_register_name(0x100)  # "GLOBAL_CTRL"
```

## Backward Compatibility

**Existing stream_core tests are NOT affected:**

- `apb_master` attribute is `None` by default
- `init_apb_master()` detects if DUT has APB interface
- APB methods raise error if APB master not initialized
- Existing tests use direct signal configuration - no changes needed

```python
# stream_core test (no APB, still works)
tb = StreamCoreTB(dut, ...)
await tb.setup_clocks_and_reset()
# NO init_apb_master() call
tb.write_descriptor(...)
await tb.kick_off_channel(0, 0x10000)  # Direct signals
```

## Complete Example Test

```python
import cocotb
from cocotb_test.simulator import run
from projects.components.stream.dv.tbclasses.stream_core_tb import StreamCoreTB, StreamRegisterMap

@cocotb.test()
async def cocotb_test_apb_config(dut):
    """Test APB configuration interface for stream_top"""

    # Initialize testbench
    tb = StreamCoreTB(dut, num_channels=8, data_width=512)
    await tb.setup_clocks_and_reset()
    await tb.init_apb_master()

    # Read version
    version = await tb.read_version()
    tb.log.info(f"STREAM version: 0x{version:08X}")

    # Configure and enable
    await tb.enable_global()
    await tb.enable_channel_mask(0xFF)

    # Setup descriptor
    tb.write_descriptor(
        addr=0x10000,
        src_addr=0x80000000,
        dst_addr=0x90000000,
        length=64,
        last=True
    )

    # Write source data pattern
    for beat in range(64):
        data = tb.create_test_pattern(beat, 'increment')
        tb.write_source_data(0x80000000 + beat*64, data, 64)

    # Kick off transfer
    await tb.kick_off_channel(0, 0x10000)

    # Wait for completion
    await tb.wait_for_channel_idle(0, timeout_us=10000)

    # Verify transfer
    assert tb.verify_transfer(0x80000000, 0x90000000, 64)

    # Check final status
    idle_status = await tb.read_channel_idle_status()
    assert (idle_status & 1) == 1, "Channel 0 should be idle"

@pytest.mark.parametrize("params", generate_test_params())
def test_stream_top_apb(request, params):
    """Pytest wrapper for stream_top APB configuration test"""
    # ... setup verilog sources, parameters, etc.
    run(
        verilog_sources=verilog_sources,
        toplevel="stream_top_ch8",
        module=module,
        testcase="cocotb_test_apb_config",
        # ... other parameters
    )
```

## Implementation Details

### APB Master Initialization

The `init_apb_master()` method:
1. Checks if DUT has `s_apb_paddr` signal (stream_top vs stream_core detection)
2. Creates APBMaster BFM with:
   - 12-bit addressing (4KB space)
   - 32-bit data width
   - Fixed randomization (deterministic)
   - APB4 protocol
3. Resets APB bus
4. Logs initialization status

### Register Access Logging

All APB register accesses are logged with human-readable names:

```
APB WRITE: GLOBAL_CTRL (0x100) = 0x00000001
APB READ:  GLOBAL_STATUS (0x104) = 0x00000080
APB WRITE: CHANNEL_ENABLE (0x120) = 0x000000FF
```

### Error Handling

```python
# If APB master not initialized
try:
    await tb.write_apb_register(0x100, 0x1)
except RuntimeError as e:
    print(f"Error: {e}")  # "APB master not initialized. Call init_apb_master() first."
```

## PeakRDL Register Definitions

The configuration registers are defined in:
```
projects/components/stream/rtl/macro/stream_regs.rdl
```

Generated RTL:
```
projects/components/stream/regs/generated/rtl/stream_regs.sv
projects/components/stream/regs/generated/rtl/stream_regs_pkg.sv
```

## Next Steps

When creating stream_top tests:
1. Import StreamCoreTB and StreamRegisterMap
2. Call `init_apb_master()` after `setup_clocks_and_reset()`
3. Use APB methods for configuration (0x100+)
4. Use existing methods for descriptors and transfers
5. Follow HPET pattern for test structure

## See Also

- `projects/components/retro_legacy_blocks/dv/tbclasses/hpet/hpet_tb.py` - Reference implementation
- `projects/components/stream/rtl/macro/stream_regs.rdl` - Register definitions
- `projects/components/stream/dv/tbclasses/stream_core_tb.py` - Implementation
