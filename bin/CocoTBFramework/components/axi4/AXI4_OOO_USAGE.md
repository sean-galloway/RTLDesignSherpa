# AXI4 Out-of-Order (OOO) Response Support - Usage Guide

**Implementation Date:** 2025-10-28
**Feature:** Configurable out-of-order response capability for AXI4 slave BFMs
**Files Modified:**
- `axi4_interfaces.py` - Added OOO support to `AXI4SlaveWrite` and `AXI4SlaveRead`
- `axi4_factories.py` - Updated factory function documentation

---

## Overview

The AXI4 slave components now support **out-of-order (OOO) responses** to enable realistic testing of bridge crossbars and other OOO-capable infrastructure.

**Key Features:**
- ✅ Backward compatible (OOO disabled by default)
- ✅ Two modes: Random and Deterministic
- ✅ Configurable delay ranges
- ✅ Specify exact response order for testing (deterministic mode)
- ✅ Minimally invasive implementation

---

## Quick Start

### Example 1: Deterministic OOO for Testing (Specify Exact Order)

```python
from CocoTBFramework.components.axi4.axi4_factories import create_axi4_slave_wr

# Create slave with deterministic OOO - specify exact response order
slave_ddr = create_axi4_slave_wr(
    dut=dut,
    prefix='ddr_s_axi_',
    clock=dut.aclk,
    enable_ooo=True,
    ooo_config={
        'mode': 'deterministic',
        'pattern': [2, 0, 3, 1, 4],  # Responses return in THIS order
    },
    log=tb.log
)
```

**Result:** If you send 5 writes with IDs 0, 1, 2, 3, 4, the B responses will arrive in order: **2, 0, 3, 1, 4** ← Exactly as specified!

### Example 2: Random OOO (Realistic DDR Behavior)

```python
from CocoTBFramework.components.axi4.axi4_factories import create_axi4_slave_rd

# Create slave with random OOO delays
slave_ddr = create_axi4_slave_rd(
    dut=dut,
    prefix='ddr_s_axi_',
    clock=dut.aclk,
    enable_ooo=True,
    ooo_config={
        'mode': 'random',
        'reorder_probability': 0.4,    # 40% chance to significantly delay
        'min_delay_cycles': 5,
        'max_delay_cycles': 200,       # DDR latency range
    },
    log=tb.log
)
```

**Result:** Responses return in unpredictable order with realistic delays, modeling DDR controller behavior.

### Example 3: In-Order (Default - Backward Compatible)

```python
# No changes needed - existing code works as before
slave_sram = create_axi4_slave_wr(
    dut=dut,
    prefix='sram_s_axi_',
    clock=dut.aclk,
    # enable_ooo defaults to False
    log=tb.log
)
```

**Result:** Responses arrive in-order (FIFO), same as before OOO feature was added.

---

## Configuration Parameters

### `enable_ooo` (bool, default: False)

**Purpose:** Enable out-of-order response mode

```python
enable_ooo=True   # Enable OOO
enable_ooo=False  # Disable OOO (default, backward compatible)
```

### `ooo_config` (dict)

**Purpose:** Configure OOO behavior

#### Mode: 'deterministic' (Specify Exact Order)

```python
ooo_config={
    'mode': 'deterministic',
    'pattern': [3, 1, 4, 0, 2],  # Complete txn IDs in this exact order
}
```

**How it works:**
- Transaction ID 3 completes first (delay = 0 cycles)
- Transaction ID 1 completes second (delay = 20 cycles after ID 3)
- Transaction ID 4 completes third (delay = 20 cycles after ID 1)
- ... and so on

**Use case:** Reproducible testing, corner case validation, regression tests

#### Mode: 'random' (Realistic Modeling)

```python
ooo_config={
    'mode': 'random',
    'reorder_probability': 0.3,    # 30% chance to add extra delay
    'min_delay_cycles': 1,         # Minimum delay before response
    'max_delay_cycles': 50,        # Maximum delay before response
}
```

**How it works:**
- Each transaction gets random delay in range `[min_delay_cycles, max_delay_cycles]`
- With `reorder_probability` chance, add extra 20-50 cycles to force reordering
- Results in realistic OOO behavior

**Use case:** Stress testing, DDR modeling, performance analysis

---

## Complete Examples

### Test Bridge OOO Routing (Deterministic)

```python
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import Timer
from CocoTBFramework.components.axi4.axi4_factories import (
    create_axi4_master_wr, create_axi4_slave_wr
)

@cocotb.test()
async def test_bridge_ooo_deterministic(dut):
    """Test bridge CAM routes OOO responses to correct master."""

    # Start clock
    cocotb.start_soon(Clock(dut.aclk, 10, units='ns').start())

    # Reset
    dut.aresetn.value = 0
    await Timer(100, units='ns')
    dut.aresetn.value = 1
    await Timer(50, units='ns')

    # Create master
    master_wr = create_axi4_master_wr(
        dut=dut,
        prefix='cpu_m_axi_',
        clock=dut.aclk,
        id_width=4,
        log=tb.log
    )

    # Create OOO slave with deterministic pattern
    slave_ddr = create_axi4_slave_wr(
        dut=dut,
        prefix='ddr_s_axi_',
        clock=dut.aclk,
        enable_ooo=True,
        ooo_config={
            'mode': 'deterministic',
            'pattern': [2, 0, 3, 1, 4],  # Exact order
        },
        log=tb.log
    )

    # Send 5 writes with different IDs
    for txn_id in range(5):
        addr = 0x80000000 + (txn_id * 0x100)
        data = 0xDEAD0000 + txn_id
        await master_wr['interface'].write_transaction(
            address=addr,
            data=[data],
            transaction_id=txn_id,
            timeout_cycles=1000
        )

    # Verify all transactions completed
    # Bridge CAM correctly routed each response despite OOO arrival
    assert all_transactions_complete()
```

### Multi-Master OOO Test

```python
@cocotb.test()
async def test_multi_master_ooo(dut):
    """Test bridge handles OOO from multiple masters."""

    # Setup (clocks, reset)
    # ...

    # Create 2 masters
    master0 = create_axi4_master_wr(...)  # Master 0
    master1 = create_axi4_master_wr(...)  # Master 1

    # Create OOO slave
    slave_ddr = create_axi4_slave_wr(
        enable_ooo=True,
        ooo_config={
            'mode': 'random',
            'reorder_probability': 0.7,  # High OOO rate
        }
    )

    # Master 0 sends IDs: 0, 2, 4
    # Master 1 sends IDs: 1, 3, 5
    # Slave responds out-of-order
    # Bridge CAM ensures each response routed to correct master

    # Run test...
```

---

## How It Works

### Deterministic Mode (`pattern=[...]`)

1. **Startup:**
   - You specify pattern: `[2, 0, 3, 1]`
   - Pattern index starts at 0

2. **Transaction Completion:**
   - Transaction ID 0 completes → Check pattern → ID 0 is at position 1
     - Position 1 > current position 0 → Delay = (1-0) * 20 = 20 cycles
   - Transaction ID 2 completes → Check pattern → ID 2 is at position 0
     - Position 0 == current position 0 → Delay = 1 cycle (immediate)
   - Pattern index advances with each completion

3. **Result:**
   - Responses arrive in exact pattern order: 2, 0, 3, 1

### Random Mode

1. **Each transaction:**
   - Base delay = random(`min_delay_cycles`, `max_delay_cycles`)
   - Roll dice (0.0-1.0) < `reorder_probability`?
     - YES → Add extra 20-50 cycles
     - NO → Use base delay

2. **Result:**
   - Unpredictable OOO arrival
   - Some transactions significantly delayed (forcing reordering)

---

## Backward Compatibility

**100% backward compatible!**

All existing testbench code works unchanged:

```python
# OLD CODE (still works):
slave = create_axi4_slave_wr(
    dut=dut,
    prefix='sram_s_axi_',
    clock=dut.aclk,
    log=tb.log
)
# Behavior: In-order responses (FIFO), same as before
```

**Migration:** Opt-in via `enable_ooo=True` parameter

---

## Testing Recommendations

### Use Deterministic for Corner Cases

```python
# Test specific scenario: Last transaction completes first
ooo_config={
    'mode': 'deterministic',
    'pattern': [4, 3, 2, 1, 0],  # Reverse order
}
```

### Use Random for Stress Testing

```python
# Stress test with high OOO rate
ooo_config={
    'mode': 'random',
    'reorder_probability': 0.8,  # 80% delayed
    'max_delay_cycles': 500,     # Long delays
}
```

### Verify OOO Infrastructure

```python
# Test bridge CAM allocates/deallocates correctly
# 1. Send transactions with varied IDs
# 2. Use deterministic pattern to control arrival order
# 3. Verify CAM routes each response to correct master
# 4. Check no CAM leaks (all entries deallocated)
```

---

## Troubleshooting

### Issue: Responses still in-order despite enable_ooo=True

**Check:**
1. Is `enable_ooo=True` actually set?
2. In random mode, is `reorder_probability` too low? (Try 0.5+)
3. Are delays too small? (Increase `max_delay_cycles`)

**Debug:**
```python
# Add logging to see delays
ooo_config={'mode': 'random', ...}
slave = create_axi4_slave_wr(..., enable_ooo=True, ooo_config=ooo_config, log=log)

# Check log output:
# "AXI4SlaveWrite: OOO mode ENABLED (reorder_prob=0.3, delay=[1, 50])"
# "AXI4SlaveWrite: Scheduling OOO completion for txn 2 after 73 cycles"
```

### Issue: Deterministic pattern not working

**Check:**
1. Are transaction IDs in pattern? (`pattern=[2,0,1]` only works if sending IDs 0,1,2)
2. Pattern exhausted? (Pattern doesn't loop - extra transactions use `min_delay_cycles`)

**Fix:**
```python
# Ensure pattern covers all transaction IDs you're sending
num_transactions = 10
ooo_config={
    'pattern': list(range(num_transactions))  # [0,1,2,3,4,5,6,7,8,9]
}
random.shuffle(ooo_config['pattern'])  # Randomize once, then deterministic
```

---

## Implementation Details

### Files Modified

**`axi4_interfaces.py`:**
- Added `enable_ooo`, `ooo_config`, `ooo_pattern_index` to both `AXI4SlaveWrite` and `AXI4SlaveRead`
- Added helper methods:
  - `_find_matching_transaction_ooo()` - Match W packets to AW in OOO mode
  - `_calculate_ooo_delay()` - Determine delay for transaction
  - `_complete_write_transaction_delayed()` - Delayed write completion
  - `_generate_read_response_delayed()` - Delayed read completion
- Modified `_w_callback()` to support OOO matching
- Modified `_ar_callback()` to support OOO scheduling

**`axi4_factories.py`:**
- Updated docstrings for `create_axi4_slave_wr()` and `create_axi4_slave_rd()`
- Documented OOO parameters

### Code Additions

**Total lines added:** ~200 (split between write and read paths)
**Backward compatibility:** 100% (default `enable_ooo=False`)
**Invasiveness:** Minimal - only modified transaction completion logic

---

## See Also

- `/mnt/data/github/rtldesignsherpa/AXI4_SLAVE_OOO_REQUIREMENTS.md` - Complete requirements document
- `projects/components/bridge/CLAUDE.md` - Bridge testing guidance
- `projects/components/bridge/rtl/bridge_cam.sv` - CAM implementation for OOO routing

---

**Implementation:** Claude (AI Assistant)
**Review Status:** Ready for testing
**Next Steps:** Create validation tests in `projects/components/bridge/dv/tests/test_bridge_ooo_validation.py`
