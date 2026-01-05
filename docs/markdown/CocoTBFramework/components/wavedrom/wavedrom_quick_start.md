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

# WaveDrom Quick Start Guide

**Get timing diagrams in 5 minutes**

---

## Prerequisites

```bash
# Install wavedrom-cli for PNG/SVG generation
npm install -g wavedrom-cli

# Verify installation
wavedrom-cli --version
```

---

## Method 1: Template Class (Easiest)

### GAXI Protocol

```python
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge
from CocoTBFramework.tbclasses.wavedrom_user.gaxi import GAXIWaveDromTemplate

@cocotb.test()
async def gaxi_test(dut):
    # Start clock
    clock = Clock(dut.axi_aclk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    dut.axi_aresetn.value = 0
    await RisingEdge(dut.axi_aclk)
    dut.axi_aresetn.value = 1
    await RisingEdge(dut.axi_aclk)

    # === ONE LINE SETUP ===
    gaxi_wave = GAXIWaveDromTemplate(
        dut=dut,
        signal_prefix="wr_",      # Finds: wr_valid, wr_ready, wr_data
        data_width=32,
        preset="comprehensive"    # handshake, back2back, stall, idle
    )

    # Start capturing
    await gaxi_wave.start_sampling()

    # Run your test
    dut.wr_valid.value = 1
    dut.wr_data.value = 0xDEAD
    await RisingEdge(dut.axi_aclk)
    dut.wr_valid.value = 0
    await RisingEdge(dut.axi_aclk)

    # Stop and generate waveforms
    results = await gaxi_wave.stop_sampling()
    gaxi_wave.get_status()
```

**Output:** WaveJSON files in `sim_build/` directory

### APB Protocol

```python
from CocoTBFramework.tbclasses.wavedrom_user.apb import APBWaveDromTemplate

@cocotb.test()
async def apb_test(dut):
    # Clock and reset...

    apb_wave = APBWaveDromTemplate(
        dut=dut,
        signal_prefix="apb_",     # Finds: apb_psel, apb_penable, etc.
        data_width=32,
        addr_width=32,
        preset="comprehensive"     # write, read, phases, errors
    )

    await apb_wave.start_sampling()
    # Run APB transactions...
    results = await apb_wave.stop_sampling()
```

---

## Method 2: Manual Setup (More Control)

### Step 1: Create Field Config

```python
from CocoTBFramework.tbclasses.wavedrom_user.gaxi import get_gaxi_field_config

# Define data fields
field_config = get_gaxi_field_config(
    data_width=32,
    addr_width=16,  # Optional
    ctrl_width=4    # Optional
)
```

### Step 2: Create WaveJSON Generator

```python
from CocoTBFramework.tbclasses.wavedrom_user.gaxi import create_gaxi_wavejson_generator

wave_generator = create_gaxi_wavejson_generator(
    field_config=field_config,
    signal_prefix="cmd_",
    group_name="Command Interface"
)
```

### Step 3: Create Constraint Solver

```python
from CocoTBFramework.components.wavedrom.constraint_solver import TemporalConstraintSolver

wave_solver = TemporalConstraintSolver(
    dut=dut,
    log=dut._log,
    wavejson_generator=wave_generator,
    default_field_config=field_config
)

# Add clock
wave_solver.add_clock_group('default', dut.axi_aclk)
```

### Step 4: Auto-Bind Signals

```python
# Automatic signal discovery
wave_solver.auto_bind_signals(
    protocol_type='gaxi',
    signal_prefix='cmd_',
    field_config=field_config
)
```

### Step 5: Setup Constraints

```python
from CocoTBFramework.tbclasses.wavedrom_user.gaxi import setup_gaxi_constraints_with_boundaries

setup_gaxi_constraints_with_boundaries(
    wave_solver=wave_solver,
    preset_name="comprehensive",
    signal_prefix="cmd_",
    field_config=field_config
)
```

### Step 6: Capture and Generate

```python
await wave_solver.start_sampling()

# Run test...

await wave_solver.stop_sampling()
wave_solver.debug_status()
```

---

## Generate PNG/SVG from WaveJSON

### Script Method (Batch Processing)

Create `wd_cmd.sh`:

```bash
#!/bin/bash
rm -rf ./PNG ./SVG
mkdir -p ./PNG ./SVG

find ./ -name "*.json" | while read file; do
    test_name=$(echo "$file" | sed 's|^\./local_sim_build/\([^/]*\)/.*|\1|')
    base_name=$(basename "${file%.json}")
    wavedrom-cli -i "$file" \\
                 -s "./SVG/${test_name}_${base_name}.svg" \\
                 -p "./PNG/${test_name}_${base_name}.png"
done
```

Run:
```bash
cd val/amba  # Or your test directory
bash wd_cmd.sh
```

### Manual Method (Single File)

```bash
wavedrom-cli -i waveform.json -p waveform.png -s waveform.svg
```

---

## Segmented Capture Pattern

For clean, isolated scenario waveforms:

```python
# Scenario 1
await wave_solver.start_sampling()
# ... run scenario 1 ...
await wave_solver.stop_sampling()
await wave_solver.solve_and_generate()
wave_solver.clear_windows()

# Scenario 2
await wave_solver.start_sampling()
# ... run scenario 2 ...
await wave_solver.stop_sampling()
await wave_solver.solve_and_generate()
wave_solver.clear_windows()
```

**Benefits:**
- No spurious matches across scenarios
- Cleaner, more deterministic waveforms
- Faster CP-SAT solving (smaller windows)

---

## Common Presets

### GAXI Presets

| Preset | Constraints | Use Case |
|--------|-------------|----------|
| `basic_handshake` | handshake | Verify valid/ready works |
| `comprehensive` | handshake, back2back, stall, idle | Full behavior analysis |
| `performance` | handshake, back2back, stall (extended) | Throughput optimization |
| `debug` | All with extended windows | Debugging stuck interfaces |

### APB Presets

| Preset | Constraints | Use Case |
|--------|-------------|----------|
| `basic_rw` | write, read | Basic functionality |
| `comprehensive` | write, read, phases, completion, errors | Full protocol analysis |
| `debug` | Activity detection on all signals | Troubleshooting |
| `timing` | Complete transactions with wait states | Timing analysis |
| `error` | Error responses and edge cases | Error handling verification |

---

## Troubleshooting

### No waveforms generated?

1. Check constraint solver status:
   ```python
   wave_solver.debug_status()
   ```

2. Verify signals were bound:
   ```python
   # Should see table with "✓ Found" status
   ```

3. Check if patterns were detected:
   ```python
   results = await wave_solver.stop_sampling()
   print(f"Solutions: {len(results['solutions'])}")
   ```

### Signals not found?

Use manual signal map:

```python
gaxi_wave = GAXIWaveDromTemplate(
    dut=dut,
    signal_prefix="",
    signal_map={
        'valid': 'my_custom_valid',
        'ready': 'weird_ready_signal',
        'data': 'pkt_data'
    }
)
```

### Wrong data captured?

Adjust window sizes:

```python
setup_gaxi_constraints_with_boundaries(
    wave_solver=wave_solver,
    max_cycles=50,  # Increase if pattern is longer
    context_cycles_before=10,  # More setup cycles
    context_cycles_after=10    # More teardown cycles
)
```

---

## Next Steps

- **Full Tutorial**: [GAXI WaveDrom Example](../../TestTutorial/wavedrom_gaxi_example.md)
- **Protocol Presets**: [All Supported Protocols](wavedrom_protocol_presets.md)
- **Auto-Binding Details**: [Auto-Binding Guide](wavedrom_auto_binding.md)
- **Advanced Techniques**: [Segmented Capture](wavedrom_segmented_capture.md)
