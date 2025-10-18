# WaveDrom Automatic Signal Binding Guide

**Version:** 2.0 (SignalResolver Integration)
**Last Updated:** 2025-10-04
**Status:** ✅ Production Ready

---

## Overview

The WaveDrom infrastructure has been modernized to use **automatic signal discovery** via the proven SignalResolver methodology. This eliminates manual signal binding and provides robust error reporting with troubleshooting guidance.

### Key Benefits

✅ **Automatic Discovery**: Tries multiple naming patterns to find signals
✅ **Manual Override**: Full control when needed via `signal_map` parameter
✅ **Rich Visualization**: Beautiful tables showing signal mappings
✅ **Error Guidance**: Comprehensive troubleshooting messages
✅ **Protocol Support**: GAXI, APB, AXIS (more coming)

---

## Quick Start

### GAXI WaveDrom (Simplest Case)

```python
from CocoTBFramework.tbclasses.wavedrom_user.gaxi import GAXIWaveDromTemplate

@cocotb.test()
async def my_test(dut):
    # ONE LINE setup - automatic signal discovery!
    gaxi_wave = GAXIWaveDromTemplate(
        dut=dut,
        signal_prefix="wr_",       # Finds: wr_valid, wr_ready, wr_data
        data_width=32
    )

    await gaxi_wave.start_sampling()

    # Run your test...
    # ...

    results = await gaxi_wave.stop_sampling()
    gaxi_wave.get_status()
```

### APB WaveDrom

```python
from CocoTBFramework.tbclasses.wavedrom_user.apb import APBWaveDromTemplate

@cocotb.test()
async def my_apb_test(dut):
    # ONE LINE setup - automatic APB signal discovery!
    apb_wave = APBWaveDromTemplate(
        dut=dut,
        signal_prefix="apb_",      # Finds: apb_psel, apb_penable, etc.
        data_width=32,
        addr_width=32
    )

    await apb_wave.start_sampling()

    # Run APB transactions...
    # ...

    results = await apb_wave.stop_sampling()
```

---

## How Automatic Discovery Works

### Pattern Matching

SignalResolver tries **multiple naming patterns** for each signal:

#### GAXI Example (prefix='wr_'):
- `valid` signal: tries `wr_valid`, `wr_gaxi_valid`, `wr_m2s_valid`, etc.
- `ready` signal: tries `wr_ready`, `wr_gaxi_ready`, `wr_s2m_ready`, etc.
- `data` signal: tries `wr_data`, `wr_pkt`, `wr_packet`, etc.

#### APB Example (prefix='apb_'):
- `psel` signal: tries `apb_psel`, `apb_PSEL`, `s_apb_psel`, etc.
- `penable` signal: tries `apb_penable`, `apb_PENABLE`, etc.
- `paddr` signal: tries `apb_paddr`, `apb_PADDR`, `apb_addr`, etc.

### Rich Table Display

When signals are discovered, you see a beautiful table:

```
Signal Mapping for GAXI WaveDrom (gaxi_wavedrom) - Automatic discovery
┏━━━━━━━━━━━━━━━━┳━━━━━━━━━━━━━━━━┳━━━━━━━━━━━━━━━┳━━━━━━━━━━━━━━━━━━━━┓
┃ Logical Signal ┃ Matched Signal ┃ Cocotb Signal ┃ Status             ┃
┡━━━━━━━━━━━━━━━━╇━━━━━━━━━━━━━━━━╇━━━━━━━━━━━━━━━╇━━━━━━━━━━━━━━━━━━━━┩
│ valid          │ wr_valid       │ valid         │ ✓ Found            │
│ ready          │ wr_ready       │ ready         │ ✓ Found            │
│ data_sig       │ wr_data        │ data          │ ✓ Found (Optional) │
└────────────────┴────────────────┴───────────────┴────────────────────┘
```

---

## Template Classes

### GAXIWaveDromTemplate

```python
class GAXIWaveDromTemplate:
    def __init__(self,
                 dut,
                 signal_prefix: str = "gaxi_",
                 data_width: int = 32,
                 addr_width: int = 0,
                 ctrl_width: int = 0,
                 num_data_fields: int = 1,
                 preset: str = "comprehensive",
                 bus_name: str = '',
                 pkt_prefix: str = '',
                 signal_map: Optional[Dict[str, str]] = None,
                 clock_signal = None)
```

**Parameters:**
- `signal_prefix`: Signal name prefix (e.g., `'wr_'`, `'cmd_'`, `'s_'`)
- `data_width`: Data field width
- `preset`: Constraint preset:
  - `'comprehensive'`: All handshake patterns (default)
  - `'basic_handshake'`: Simple valid/ready
  - `'performance'`: Throughput analysis
  - `'debug'`: Debug patterns
- `signal_map`: Manual override (see below)
- `clock_signal`: Auto-detected if None (tries `axi_aclk`, `i_clk`, `clk`)

### APBWaveDromTemplate

```python
class APBWaveDromTemplate:
    def __init__(self,
                 dut,
                 signal_prefix: str = "apb_",
                 data_width: int = 32,
                 addr_width: int = 32,
                 preset: str = "comprehensive",
                 bus_name: str = '',
                 signal_map: Optional[Dict[str, str]] = None,
                 clock_signal = None)
```

**Parameters:**
- `signal_prefix`: Signal name prefix (e.g., `'apb_'`, `'s_apb_'`, `''`)
- `preset`: Constraint preset:
  - `'comprehensive'`: Full APB protocol analysis (default)
  - `'basic_rw'`: Read/write transactions only
  - `'timing'`: Timing and wait state analysis
  - `'debug'`: Debug patterns
  - `'error'`: Error-focused
- `signal_map`: Manual override
- `clock_signal`: Auto-detected (tries `pclk`, `apb_pclk`, `i_clk`, `clk`)

---

## Manual Signal Override

### When You Need It

Use `signal_map` when:
- Non-standard signal naming
- Unusual prefixes
- Legacy designs
- Quick override without renaming

### GAXI Manual Override

```python
gaxi_wave = GAXIWaveDromTemplate(
    dut,
    signal_prefix="",  # Empty - using manual map
    data_width=32,
    signal_map={
        'valid': 'weird_valid_name',
        'ready': 'custom_ready_sig',
        'data': 'pkt_data_field'
    }
)
```

### APB Manual Override

```python
apb_wave = APBWaveDromTemplate(
    dut,
    signal_prefix="",
    data_width=32,
    addr_width=32,
    signal_map={
        'psel': 'chip_select',
        'penable': 'enable_sig',
        'pwrite': 'wr_en',
        'pready': 'slave_ready',
        'paddr': 'address_bus',
        'pwdata': 'write_data',
        'prdata': 'read_data'
    }
)
```

---

## Multi-Field Protocols

### Multiple Data Fields (GAXI)

For protocols with packet fields:

```python
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition

# Create field configuration
field_config = FieldConfig([
    FieldDefinition('addr', 32, 0),
    FieldDefinition('data', 64, 32),
    FieldDefinition('ctrl', 8, 96)
])

gaxi_wave = GAXIWaveDromTemplate(
    dut,
    signal_prefix="wr_",
    data_width=0,  # Not used when field_config provided
    field_config=field_config  # Signal discovery will find: wr_addr, wr_data, wr_ctrl
)
```

---

## Error Handling

### Comprehensive Error Messages

If signal not found, you get helpful troubleshooting:

```
🚨 CRITICAL: No valid signal found for GAXI WaveDrom!

Component: GAXI WaveDrom
Protocol: gaxi_wavedrom
Mode: single-signal (multi_sig=False)
Bus name: '' (empty means no bus prefix)

This component REQUIRES a valid signal for proper operation.

💡 TROUBLESHOOTING:
1. Check signal naming - expected patterns:
   - valid (current prefix + 'valid')
   - wr_valid (for write-side)
   - m2s_valid (master-to-slave)

2. Available valid-like signals found on DUT:
   DATA_VALID, cmd_valid, wr_v

3. Use manual signal_map to specify correct signal:
   signal_map={'valid': 'cmd_valid'}

4. Check signal_prefix parameter - currently: 'wr_'
   If your signals have a different prefix, update signal_prefix
```

---

## Architecture Overview

### Component Stack

```
┌─────────────────────────────────────┐
│   GAXIWaveDromTemplate / APB...     │  ← User-facing templates
├─────────────────────────────────────┤
│   TemporalConstraintSolver          │  ← Constraint solver
│   - auto_bind_signals()             │
├─────────────────────────────────────┤
│   WavedromSignalBinder              │  ← Wavedrom-specific layer
├─────────────────────────────────────┤
│   SignalResolver                    │  ← Pattern matching engine
│   - PROTOCOL_SIGNAL_CONFIGS         │
└─────────────────────────────────────┘
```

### Signal Flow

1. **Template Init**: User creates `GAXIWaveDromTemplate(dut, signal_prefix='wr_')`
2. **Auto-Bind**: Template calls `wave_solver.auto_bind_signals('gaxi', signal_prefix='wr_')`
3. **Wavedrom Binder**: Creates `WavedromSignalBinder` with protocol='gaxi_wavedrom'
4. **Signal Resolver**: Uses `PROTOCOL_SIGNAL_CONFIGS['gaxi_wavedrom']` patterns
5. **Pattern Match**: Tries all combinations: `wr_valid`, `wr_gaxi_valid`, etc.
6. **Binding**: Found signals bound to solver via `add_signal_binding()`
7. **Display**: Rich table shows all mappings

---

## Configuration Files

### Adding New Protocols

To add a new protocol to automatic discovery:

**1. Add patterns to `signal_mapping_helper.py`:**

```python
PROTOCOL_SIGNAL_CONFIGS = {
    # ... existing configs ...

    'myprotocol_wavedrom': {
        'signal_map': {
            'req': ['{prefix}{bus_name}req', '{prefix}{bus_name}request'],
            'ack': ['{prefix}{bus_name}ack', '{prefix}{bus_name}acknowledge'],
        },
        'optional_signal_map': {
            'multi_sig_false': ['{prefix}{bus_name}data'],
            'multi_sig_true': ['{prefix}{bus_name}{field_name}']
        }
    }
}
```

**2. Add protocol type handling in `signal_mapping_helper.py`:**

```python
# In _resolve_optional_signals() method:
elif self.protocol_type in ['myprotocol_master', 'myprotocol_slave', 'myprotocol_wavedrom']:
    signal_obj = self._find_signal_match('data_sig', patterns, required=False)
    self.resolved_signals['data_sig'] = signal_obj
```

**3. Create template class** (similar to `GAXIWaveDromTemplate`)

---

## Testing

### Test Your Wavedrom Setup

```python
@cocotb.test()
async def test_wavedrom(dut):
    # Setup wavedrom
    wave = GAXIWaveDromTemplate(dut, signal_prefix="wr_", data_width=32)

    await wave.start_sampling()

    # Generate transactions
    for i in range(5):
        dut.wr_valid.value = 1
        dut.wr_data.value = 0xA000 + i
        await RisingEdge(dut.clk)
        dut.wr_valid.value = 0
        await RisingEdge(dut.clk)

    # Get results
    results = await wave.stop_sampling()

    # Verify
    assert len(results['solutions']) > 0, "Should find patterns"
    assert 'wr_handshake' in results['satisfied_constraints']

    wave.get_status()  # Print summary
```

### View Generated WaveJSON

WaveJSON files are auto-generated:
- `wr_handshake_001.json`
- `wr_back2back_001.json`
- `wr_stall_001.json`
- etc.

View at: https://wavedrom.com/editor.html

---

## Advanced Usage

### Custom Constraints with Auto-Binding

```python
# Create solver with auto-binding
wave_solver = TemporalConstraintSolver(dut=dut, log=dut._log)
wave_solver.add_clock_group('default', dut.clk)

# Auto-bind signals
num_signals = wave_solver.auto_bind_signals(
    protocol_type='gaxi',
    signal_prefix='wr_',
    signal_map={'valid': 'custom_valid'}  # Partial override
)

# Add custom constraints
custom_constraint = TemporalConstraint(
    name="my_pattern",
    events=[...],
    ...
)
wave_solver.add_constraint(custom_constraint)

# Run
await wave_solver.start_sampling()
# ...
await wave_solver.stop_sampling()
```

### Debugging Signal Resolution

Enable super-debug mode:

```python
wave_solver.auto_bind_signals(
    protocol_type='gaxi',
    signal_prefix='wr_',
    super_debug=True  # Verbose signal resolution logging
)
```

---

## Migration Guide

### From Manual Binding

**Old approach:**
```python
# Manual binding (deprecated)
wave_solver.add_signal_binding('wr_valid', wr_valid_handle)
wave_solver.add_signal_binding('wr_ready', wr_ready_handle)
wave_solver.add_signal_binding('wr_data', wr_data_handle)
```

**New approach:**
```python
# Automatic binding (recommended)
wave_solver.auto_bind_signals('gaxi', signal_prefix='wr_')
```

### From Old Template

**Old:**
```python
# Old GAXIWaveDrom class with manual setup
wave = GAXIWaveDrom(dut, ...)
# ... complex setup code ...
```

**New:**
```python
# New GAXIWaveDromTemplate - one line!
wave = GAXIWaveDromTemplate(dut, signal_prefix='wr_', data_width=32)
```

---

## Troubleshooting

### Signal Not Found

**Problem:** "No valid signal found"

**Solutions:**
1. Check signal name with `print(dir(dut))` or DUT hierarchy
2. Verify `signal_prefix` is correct
3. Use `signal_map` for manual override:
   ```python
   signal_map={'valid': 'actual_signal_name'}
   ```

### Clock Not Auto-Detected

**Problem:** "Could not auto-detect clock signal"

**Solution:** Provide clock explicitly:
```python
wave = GAXIWaveDromTemplate(
    dut,
    signal_prefix='wr_',
    clock_signal=dut.my_custom_clk  # Explicit clock
)
```

### No Patterns Found

**Problem:** Wavedrom runs but finds no patterns

**Solutions:**
1. Check constraints match your traffic (use `preset='debug'`)
2. Verify signals toggling: `wave.get_status()`
3. Check window sizes - may need larger: `max_cycles=50`

---

## Best Practices

### ✅ DO

- Use automatic discovery with `signal_prefix`
- Let clock auto-detect when possible
- Use appropriate preset for your use case
- Check status with `wave.get_status()` after sampling

### ❌ DON'T

- Don't use manual `signal_map` unless necessary
- Don't hardcode signal handles
- Don't skip error messages - they have solutions!

---

## See Also

- **SignalResolver Documentation**: `bin/CocoTBFramework/components/shared/signal_mapping_helper.py`
- **Constraint Solver**: `bin/CocoTBFramework/components/wavedrom/constraint_solver.py`
- **GAXI Constraints**: `bin/CocoTBFramework/tbclasses/wavedrom_user/gaxi.py`
- **APB Constraints**: `bin/CocoTBFramework/tbclasses/wavedrom_user/apb.py`

---

**Version History:**
- v2.0 (2025-10-04): SignalResolver integration, auto-binding
- v1.0 (2025-09-15): Initial manual binding version

**Maintained By:** RTL Design Sherpa Project
