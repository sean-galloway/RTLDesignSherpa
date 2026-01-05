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

# GAXI WaveDrom Tutorial - Complete Example

**Learn WaveDrom generation with a real 6-scenario testbench**

---

## Overview

This tutorial walks through `test_gaxi_wavedrom_example.py`, a comprehensive example demonstrating WaveDrom timing diagram generation for a GAXI skid buffer / FIFO. The test uses **segmented capture** to isolate 6 different behavioral scenarios, generating clean, publication-quality waveforms for each.

**Test File:** `val/amba/test_gaxi_wavedrom_example.py`
**RTL Module:** `rtl/amba/gaxi/gaxi_skid_buffer.sv`
**Generated Assets:** `docs/markdown/assets/WAVES/`

---

## Test Architecture

### Device Under Test (DUT)

```systemverilog
module gaxi_skid_buffer #(
    parameter DATA_WIDTH = 32,
    parameter DEPTH = 4
) (
    input  logic                  axi_aclk,
    input  logic                  axi_aresetn,
    // Write interface
    input  logic                  wr_valid,
    output logic                  wr_ready,
    input  logic [DATA_WIDTH-1:0] wr_data,
    // Read interface
    output logic                  rd_valid,
    input  logic                  rd_ready,
    output logic [DATA_WIDTH-1:0] rd_data,
    // Internal state
    output logic [2:0]            count
);
```

**Behavior:**
- **Skid buffer** when nearly empty: Zero-latency bypass (wr_data → rd_data immediately)
- **FIFO** when filling: Buffers data, asserts backpressure (wr_ready=0) when full

### 6 Scenarios Captured

1. **Zero-latency bypass** - Write to empty buffer shows immediate rd_valid
2. **Burst write until full** - Demonstrates backpressure behavior
3. **Simultaneous read/write** - Pass-through operation (count stays constant)
4. **Burst read until empty** - Shows rd_valid deassert when drained
5. **Fill then drain** - Complete fill phase followed by drain phase
6. **Alternating read/write** - Continuous flow with interleaved operations

---

## Setup Phase

### Step 1: Create Field Configuration

```python
from CocoTBFramework.components.wavedrom.utility import create_protocol_specific_field_config

# Use 8-bit data for readability in waveforms
field_config = create_protocol_specific_field_config(
    protocol_type='gaxi',
    data_width=8,  # Small width = readable waveforms
    addr_width=0,
    ctrl_width=0
)
```

**Why 8-bit?** Easier to read hex values in timing diagrams (0x42 vs 0x00000042)

### Step 2: Create Constraint Solver

```python
from CocoTBFramework.components.wavedrom.constraint_solver import TemporalConstraintSolver
from CocoTBFramework.components.wavedrom.wavejson_gen import WaveJSONGenerator

wave_generator = WaveJSONGenerator()
wave_solver = TemporalConstraintSolver(
    dut=dut,
    log=dut._log,
    wavejson_generator=wave_generator,
    default_field_config=field_config
)

# Add clock group
wave_solver.add_clock_group('default', dut.axi_aclk)
```

### Step 3: Auto-Bind Signals

```python
# Auto-bind Write interface
wave_solver.auto_bind_signals('gaxi', signal_prefix='wr_', field_config=field_config)

# Auto-bind Read interface
wave_solver.auto_bind_signals('gaxi', signal_prefix='rd_', field_config=field_config)

# Manual bind internal signals (not part of GAXI protocol)
count_field = FieldDefinition('count', 4, format='dec', description='FIFO count')
wave_solver.add_signal_binding('count', 'count', count_field)
wave_solver.add_signal_binding('wr_xfer', 'w_wr_xfer')  # Internal transfer signals
wave_solver.add_signal_binding('rd_xfer', 'w_rd_xfer')
```

**Note:** Auto-binding discovers `wr_valid`, `wr_ready`, `wr_data`, `rd_valid`, `rd_ready`, `rd_data` automatically!

### Step 4: Define Constraints with Arrows

Each scenario has a temporal constraint with arrow annotations:

```python
from CocoTBFramework.components.wavedrom.constraint_solver import (
    TemporalConstraint, TemporalEvent, TemporalRelation
)

# Example: Zero-latency bypass
zero_latency_bypass = TemporalConstraint(
    name='zero_latency_bypass',
    events=[
        TemporalEvent('activity', create_static_pattern('wr_xfer', 1))
    ],
    temporal_relation=TemporalRelation.SEQUENCE,
    max_window_size=12,
    required=True,
    clock_group='default',
    signals_to_show=['clk', 'rst_n', 'wr_valid', 'wr_ready', 'wr_data',
                     'rd_valid', 'rd_ready', 'rd_data',
                     'count', 'wr_xfer', 'rd_xfer'],
    labeled_groups=[
        ['Write', 'wr_valid', 'wr_ready', 'wr_data'],
        ['Read', 'rd_valid', 'rd_ready', 'rd_data'],
        ['Internal', 'count', 'wr_xfer', 'rd_xfer']
    ],
    edges=[
        ('wr_data', 'rd_data', '->', 'data'),   # Show data flow
        ('wr_xfer', 'count', '->', 'wr+'),      # Write increments count
        ('rd_xfer', 'count', '->', 'rd-'),      # Read decrements count
    ]
)

wave_solver.add_constraint(zero_latency_bypass)
```

**Key Features:**
- **`labeled_groups`**: Organizes signals into visual groups
- **`edges`**: Arrows showing signal relationships
  - Format: `(from_signal, to_signal, arrow_type, label)`
  - Arrow types: `->` (solid), `~>` (curved), `-~>` (dashed curved)

---

## Scenario 1: Zero-Latency Bypass

### Test Sequence

```python
# Scenario 1: Write to empty buffer
await wave_solver.start_sampling()

# Write transaction
dut.wr_valid.value = 1
dut.wr_data.value = 0x60
await RisingEdge(dut.axi_aclk)

# Deassert
dut.wr_valid.value = 0
await RisingEdge(dut.axi_aclk)

# Read transaction
dut.rd_ready.value = 1
await RisingEdge(dut.axi_aclk)
dut.rd_ready.value = 0

await wave_solver.stop_sampling()
await wave_solver.solve_and_generate()
wave_solver.clear_windows()
```

### Generated Waveform

![Zero-Latency Bypass](../assets/WAVES/test_gaxi_skid_buffer_w32_d4_default_wd_zero_latency_bypass_001.png)

**Key Observations:**
- ✅ **`rd_valid` asserts immediately** when wr_valid goes high (bypass path)
- ✅ **Data arrow** shows wr_data → rd_data relationship
- ✅ **Count changes** with wr_xfer/rd_xfer arrows showing causality
- ✅ **Labeled groups** separate Write, Read, and Internal signals

---

## Scenario 2: Burst Write Until Full

### Test Sequence

```python
# Scenario 2: Fill the FIFO
await wave_solver.start_sampling()

# Burst write
for i in range(5):
    dut.wr_valid.value = 1
    dut.wr_data.value = 0x30 + i
    await RisingEdge(dut.axi_aclk)

dut.wr_valid.value = 0

await wave_solver.stop_sampling()
await wave_solver.solve_and_generate()
wave_solver.clear_windows()
```

### Generated Waveform

![Burst Write Full](../assets/WAVES/test_gaxi_skid_buffer_w32_d4_default_wd_burst_write_full_001.png)

**Key Observations:**
- ✅ **wr_ready deasserts** when FIFO is full (backpressure)
- ✅ **count increments** with each write
- ✅ **Single arrow** (wr_xfer → count) shows fill behavior

---

## Scenario 3: Simultaneous Read/Write

### Test Sequence

```python
# Scenario 3: Pass-through operation
await wave_solver.start_sampling()

# Simultaneous read and write
for i in range(3):
    dut.wr_valid.value = 1
    dut.rd_ready.value = 1
    dut.wr_data.value = 0x62 + i
    await RisingEdge(dut.axi_aclk)

    dut.wr_valid.value = 0
    dut.rd_ready.value = 0
    await RisingEdge(dut.axi_aclk)

await wave_solver.stop_sampling()
await wave_solver.solve_and_generate()
wave_solver.clear_windows()
```

### Generated Waveform

![Simultaneous Read/Write](../assets/WAVES/test_gaxi_skid_buffer_w32_d4_default_wd_simultaneous_rdwr_001.png)

**Key Observations:**
- ✅ **count stays constant** (same rate in/out)
- ✅ **Data flows through** with minimal latency
- ✅ **Three arrows** show wr→count, rd→count, and data flow

---

## Scenario 4: Burst Read Until Empty

### Test Sequence

```python
# Scenario 4: Drain the FIFO
await wave_solver.start_sampling()

# Burst read
dut.rd_ready.value = 1
for _ in range(5):
    await RisingEdge(dut.axi_aclk)

dut.rd_ready.value = 0

await wave_solver.stop_sampling()
await wave_solver.solve_and_generate()
wave_solver.clear_windows()
```

### Generated Waveform

![Burst Read Empty](../assets/WAVES/test_gaxi_skid_buffer_w32_d4_default_wd_burst_read_empty_001.png)

**Key Observations:**
- ✅ **rd_valid deasserts** when FIFO is empty
- ✅ **count decrements** with each read
- ✅ **Drain arrow** (rd_xfer → count) shows empty behavior

---

## Scenario 5: Fill Then Drain

### Test Sequence

```python
# Scenario 5: Fill completely, then drain
await wave_solver.start_sampling()

# Fill phase
dut.rd_ready.value = 0
for i in range(4):
    dut.wr_valid.value = 1
    dut.wr_data.value = 0x70 + i
    await RisingEdge(dut.axi_aclk)
dut.wr_valid.value = 0
await RisingEdge(dut.axi_aclk)

# Drain phase
dut.rd_ready.value = 1
for _ in range(4):
    await RisingEdge(dut.axi_aclk)
dut.rd_ready.value = 0

await wave_solver.stop_sampling()
await wave_solver.solve_and_generate()
wave_solver.clear_windows()
```

### Generated Waveform

![Fill Then Drain](../assets/WAVES/test_gaxi_skid_buffer_w32_d4_default_wd_fill_then_drain_001.png)

**Key Observations:**
- ✅ **Two distinct phases** visible in waveform
- ✅ **count rises to max** (fill), then **falls to zero** (drain)
- ✅ **Buffered arrow** (wr_data → rd_data) shows data stored then retrieved

---

## Scenario 6: Alternating Read/Write

### Test Sequence

```python
# Scenario 6: Continuous interleaved operations
await wave_solver.start_sampling()

for i in range(4):
    # Write
    dut.wr_valid.value = 1
    dut.rd_ready.value = 0
    dut.wr_data.value = 0x80 + i
    await RisingEdge(dut.axi_aclk)

    # Read
    dut.wr_valid.value = 0
    dut.rd_ready.value = 1
    await RisingEdge(dut.axi_aclk)

dut.rd_ready.value = 0

await wave_solver.stop_sampling()
await wave_solver.solve_and_generate()
wave_solver.clear_windows()
```

### Generated Waveform

![Alternating Read/Write](../assets/WAVES/test_gaxi_skid_buffer_w32_d4_default_wd_alternating_rdwr_001.png)

**Key Observations:**
- ✅ **Regular pattern** of alternating write/read
- ✅ **count oscillates** between levels
- ✅ **Flow arrow** (curved ~>) shows continuous data movement

---

## Key Techniques

### Segmented Capture

**Why:** Prevents spurious matches across different test scenarios

```python
# Each scenario is isolated
await wave_solver.start_sampling()
# ... run scenario ...
await wave_solver.stop_sampling()
await wave_solver.solve_and_generate()  # Generate NOW
wave_solver.clear_windows()              # Clear for next scenario
```

**Benefits:**
- ✅ No cross-contamination between scenarios
- ✅ Deterministic pattern matching
- ✅ Faster CP-SAT solving (smaller windows)

### Labeled Groups

**Syntax:**
```python
labeled_groups=[
    ['Group Name', 'signal1', 'signal2', ...],
    ['Another Group', 'signal3', 'signal4', ...],
]
```

**Output in WaveJSON:**
```json
"signal": [
  ["Write",
    {"name": "wr_valid", "wave": "..."},
    {"name": "wr_ready", "wave": "..."}
  ],
  ["Read",
    {"name": "rd_valid", "wave": "..."},
    {"name": "rd_ready", "wave": "..."}
  ]
]
```

### Edge Annotations (Arrows)

**Syntax:**
```python
edges=[
    ('from_signal', 'to_signal', 'arrow_type', 'label'),
]
```

**Arrow Types:**
- `->`: Solid arrow
- `~>`: Curved arrow
- `-~>`: Dashed curved arrow
- `->>`: Double arrow
- `<->`: Bidirectional

**Example:**
```python
edges=[
    ('wr_data', 'rd_data', '->', 'data'),      # Data flow
    ('wr_xfer', 'count', '->', 'wr+'),         # Write increases count
    ('rd_xfer', 'count', '->', 'rd-'),         # Read decreases count
]
```

### Field-Based Formatting

```python
# Decimal format for count (shows "2", "3", not binary)
count_field = FieldDefinition('count', 4, format='dec', description='FIFO count')

# Hex format for data (shows "0x42", not "0x00000042")
data_field = FieldDefinition('data', 8, format='hex', description='Data')
```

---

## Running the Test

### Basic Run

```bash
pytest val/amba/test_gaxi_wavedrom_example.py -v -s
```

### Generate PNG/SVG from WaveJSON

```bash
cd val/amba
bash wd_cmd.sh
```

**Output:**
- `PNG/` directory with all PNG waveforms
- `SVG/` directory with all SVG waveforms

### Copy to Documentation

```bash
cp val/amba/PNG/*.png docs/markdown/assets/WAVES/
cp val/amba/SVG/*.svg docs/markdown/assets/WAVES/
```

---

## Test Configuration

### Parametric Testing

```python
def generate_params():
    """Control test matrix with enable_wavedrom flag"""
    return [
        (32, 4, 'default', True),   # WITH waveforms
        (32, 4, 'default', False),  # NO waveforms (faster)
    ]

@pytest.mark.parametrize("data_width,depth,trim_mode,enable_wavedrom", generate_params())
def test_gaxi_wavedrom_example(data_width, depth, trim_mode, enable_wavedrom):
    # Test setup...
    extra_env = {
        'ENABLE_WAVEDROM': str(int(enable_wavedrom)),
        'TRIM_MODE': trim_mode,
    }
```

**Why:** Run 100+ functional tests fast, generate waveforms for only 1 config

### Trim Modes

| Mode | Before Context | After Context | Use Case |
|------|---------------|---------------|----------|
| `minimal` | 2 cycles | 1 cycle | Compact diagrams |
| `default` | 5 cycles | None (auto) | Balanced |
| `moderate` | 10 cycles | 5 cycles | More context |

**Set via environment:**
```python
'TRIM_MODE': 'moderate'
```

---

## Summary

This tutorial demonstrated:

✅ **Segmented capture** for isolated scenarios
✅ **Auto-binding** for automatic signal discovery
✅ **Labeled groups** for organized waveforms
✅ **Arrow annotations** for showing relationships
✅ **Field formatting** for readable data values
✅ **6 comprehensive scenarios** covering skid buffer/FIFO behavior

**Next Steps:**
- Adapt this pattern for your protocol
- Add custom scenarios
- Create protocol-specific presets
- Generate documentation with embedded waveforms

---

## Related Documentation

- [WaveDrom Quick Start](../CocoTBFramework/components/wavedrom/wavedrom_quick_start.md)
- [Protocol Presets Reference](../CocoTBFramework/components/wavedrom/wavedrom_protocol_presets.md)
- [Auto-Binding Guide](../CocoTBFramework/components/wavedrom/wavedrom_auto_binding.md)
- [Segmented Capture Details](../CocoTBFramework/components/wavedrom/wavedrom_segmented_capture.md)
