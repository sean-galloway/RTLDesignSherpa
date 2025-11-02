# GTKWave Save Files for RTL Common Library

**Last Updated:** 2025-10-15
**Coverage:** 86/86 modules (100%)

---

## Overview

This directory contains GTKWave save files (`.gtkw`) for all 86 modules in the RTL Common Library. These files provide pre-configured waveform views with organized signal groupings for efficient debugging.

**Purpose:**
- Quick waveform analysis without manual signal selection
- Standardized signal organization across all modules
- Improved debugging efficiency

---

## Quick Start

### Method 1: Generate Waveforms and Load Save File

```bash
# 1. Run test with VCD/FST dump
pytest val/common/test_counter_bin.py -v --vcd=waves.vcd

# 2. Open with GTKWave and load save file
gtkwave waves.vcd val/common/GTKW/counter_bin.gtkw
```

### Method 2: Load Save File After Generating Waveforms

```bash
# If you already have a VCD/FST file
gtkwave path/to/sim_build/dump.fst

# In GTKWave GUI:
# File → Read Save File → val/common/GTKW/{module}.gtkw
```

---

## Signal Organization

All `.gtkw` files follow a consistent hierarchical structure:

### 1. **Parameters** (if applicable)
Module configuration parameters (e.g., `WIDTH`, `DEPTH`, `MAX`)

### 2. **Clock and Reset**
- Clock signals (`clk`, `aclk`, etc.)
- Reset signals (`rst_n`, `aresetn`, etc.)

### 3. **Inputs**
All input ports (excluding clk/rst)

### 4. **Outputs**
All output ports

### 5. **Inouts** (if applicable)
Bidirectional ports

### 6. **Internal Registers**
Registers with `r_` prefix (state, counters, buffers)

### 7. **Internal Wires**
Combinational signals with `w_` prefix (intermediate results, flags)

---

## Usage Examples

### Example 1: Counter Debugging

```bash
# Run counter test with waveform generation
pytest val/common/test_counter_bin.py -v --vcd=counter_debug.vcd

# Load with save file
gtkwave counter_debug.vcd val/common/GTKW/counter_bin.gtkw
```

**Waveform View Shows:**
```
counter_bin
├── Parameters
│   ├── WIDTH = 8
│   └── MAX = 100
├── Clock and Reset
│   ├── clk
│   └── rst_n
├── Inputs
│   └── enable
├── Outputs
│   ├── counter_bin_curr [7:0]
│   └── counter_bin_next [7:0]
└── Internal Wires
    └── w_max_val [6:0]
```

**Timing Diagram (Counter Operation):**
```wavedrom
{
  "signal": [
    {"name": "clk", "wave": "p.........", "period": 1},
    {"name": "rst_n", "wave": "01........", "data": [""]},
    {"name": "enable", "wave": "0.1.......", "data": [""]},
    {"name": "counter_bin_curr", "wave": "=.========", "data": ["0","0","1","2","3","4","5","6","7","8"]},
    {"name": "counter_bin_next", "wave": "=.========", "data": ["0","1","2","3","4","5","6","7","8","9"]},
    {"name": "w_max_val", "wave": "========..", "data": ["99","99","99","99","99","99","99","99"]}
  ],
  "config": {"hscale": 2}
}
```

### Example 2: Arbiter Debugging

```bash
# Run arbiter test
pytest val/common/test_arbiter_round_robin.py -v --vcd=arbiter_debug.vcd

# Load save file
gtkwave arbiter_debug.vcd val/common/GTKW/arbiter_round_robin.gtkw
```

**Waveform View Shows:**
```
arbiter_round_robin
├── Parameters
│   ├── N = 4
│   └── REG_OUTPUT = 1
├── Clock and Reset
│   ├── clk
│   └── rst_n
├── Inputs
│   ├── request [3:0]
│   ├── grant_ack [3:0]
│   └── block_arb
├── Outputs
│   ├── grant [3:0]
│   ├── grant_valid
│   └── grant_id [1:0]
├── Internal Registers
│   ├── r_last_valid
│   ├── r_last_grant_id [1:0]
│   ├── r_pending_ack
│   └── r_pending_client [1:0]
└── Internal Wires
    ├── w_winner_valid
    ├── w_ack_received
    ├── w_any_requests
    ├── w_can_grant
    └── ...
```

**Timing Diagram (Round-Robin Arbitration):**
```wavedrom
{
  "signal": [
    {"name": "clk", "wave": "p............", "period": 1},
    {"name": "rst_n", "wave": "01...........", "data": [""]},
    {"name": "request[3:0]", "wave": "x.3.4.3.5....", "data": ["0001","0011","0001","0101"]},
    {"name": "grant[3:0]", "wave": "x..2.4.8.2...", "data": ["0001","0010","1000","0001"]},
    {"name": "grant_valid", "wave": "0..1.1.1.1..0", "data": [""]},
    {"name": "grant_id[1:0]", "wave": "x..=.=.=.=..x", "data": ["0","1","3","0"]},
    {"name": "r_last_grant_id", "wave": "x..=.=.=.=...", "data": ["0","1","3","0"]},
    {},
    {"name": "notes", "wave": "x..2.4.6.8...", "data": ["Req0","Req1","Req3","Req0 (wrap)"]}
  ],
  "config": {"hscale": 2}
}
```

### Example 3: FIFO Debugging

```bash
pytest val/common/test_fifo_buffer.py -v --vcd=fifo_debug.vcd
gtkwave fifo_debug.vcd val/common/GTKW/fifo_sync.gtkw
```

**Timing Diagram (FIFO Write/Read):**
```wavedrom
{
  "signal": [
    {"name": "clk", "wave": "p...........", "period": 1},
    {"name": "rst_n", "wave": "01..........", "data": [""]},
    {"name": "i_write", "wave": "0.1111.0....", "data": [""]},
    {"name": "i_wr_data", "wave": "x.3456.x....", "data": ["A","B","C","D"]},
    {"name": "o_wr_full", "wave": "0.......1.0.", "data": [""]},
    {"name": "i_read", "wave": "0......1111.", "data": [""]},
    {"name": "o_rd_data", "wave": "x......3456.", "data": ["A","B","C","D"]},
    {"name": "o_rd_empty", "wave": "1.0.......1.", "data": [""]},
    {"name": "r_wr_ptr_bin", "wave": "=.========..", "data": ["0","0","1","2","3","0","0","0","0","0"]},
    {"name": "r_rd_ptr_bin", "wave": "=......=====", "data": ["0","0","0","1","2","3","0"]}
  ],
  "config": {"hscale": 2}
}
```

### Example 4: CRC Debugging

```bash
pytest val/common/test_dataint_crc.py -v --vcd=crc_debug.vcd
gtkwave crc_debug.vcd val/common/GTKW/dataint_crc.gtkw
```

**Timing Diagram (CRC Calculation):**
```wavedrom
{
  "signal": [
    {"name": "clk", "wave": "p........", "period": 1},
    {"name": "rst_n", "wave": "01.......", "data": [""]},
    {"name": "i_data[7:0]", "wave": "x.345678.", "data": ["0x12","0x34","0x56","0x78","0xAB","0xCD"]},
    {"name": "i_valid", "wave": "0.1111110", "data": [""]},
    {"name": "o_crc[31:0]", "wave": "x.=======", "data": ["Init","CRC1","CRC2","CRC3","CRC4","CRC5","Final"]},
    {"name": "o_valid", "wave": "0.......1", "data": [""]},
    {},
    {"name": "notes", "wave": "x.2.4...6", "data": ["Start","Processing","Done"]}
  ],
  "config": {"hscale": 2}
}
```

---

## Module Categories and Example Use Cases

### Counters (9 modules)

| Module | Save File | Use Case |
|--------|-----------|----------|
| `counter_bin` | `counter_bin.gtkw` | Event counting, iteration |
| `counter_load_clear` | `counter_load_clear.gtkw` | Loadable counter with clear |
| `counter_freq_invariant` | `counter_freq_invariant.gtkw` | Time-based counting (ms/us) |
| `counter_bingray` | `counter_bingray.gtkw` | Gray code counter for CDC |
| `counter_ring` | `counter_ring.gtkw` | Ring counter (circular) |
| `counter_johnson` | `counter_johnson.gtkw` | Johnson counter (2N states) |

**Debugging Tip:** Focus on `counter_bin_curr` vs `counter_bin_next` to verify combinational logic before register.

### Arbiters (4 modules)

| Module | Save File | Use Case |
|--------|-----------|----------|
| `arbiter_round_robin` | `arbiter_round_robin.gtkw` | Fair multi-master arbitration |
| `arbiter_round_robin_simple` | `arbiter_round_robin_simple.gtkw` | Simplified arbiter |
| `arbiter_round_robin_weighted` | `arbiter_round_robin_weighted.gtkw` | QoS arbitration |
| `arbiter_priority_encoder` | `arbiter_priority_encoder.gtkw` | Fixed priority |

**Debugging Tip:** Check `r_last_grant_id` to verify round-robin progression. Verify `grant_ack` handshake timing.

### Data Integrity (7 modules)

| Module | Save File | Use Case |
|--------|-----------|----------|
| `dataint_crc` | `dataint_crc.gtkw` | CRC calculation (300+ standards) |
| `dataint_ecc_hamming_encode_secded` | `dataint_ecc_hamming_encode_secded.gtkw` | ECC encoding |
| `dataint_ecc_hamming_decode_secded` | `dataint_ecc_hamming_decode_secded.gtkw` | ECC decoding with SECDED |
| `dataint_parity` | `dataint_parity.gtkw` | Even/odd parity |
| `dataint_checksum` | `dataint_checksum.gtkw` | Checksum calculation |

**Debugging Tip:** For CRC, verify polynomial initialization and final XOR. For ECC, check syndrome calculation and error injection.

### Clock Utilities (4 modules)

| Module | Save File | Use Case |
|--------|-----------|----------|
| `clock_divider` | `clock_divider.gtkw` | Clock frequency division |
| `clock_gate_ctrl` | `clock_gate_ctrl.gtkw` | Clock gating for power |
| `clock_pulse` | `clock_pulse.gtkw` | Pulse generation |
| `icg` | `icg.gtkw` | Integrated clock gate |

**Debugging Tip:** Verify clock edges align properly. Check enable signal timing for clock gates.

### Synchronizers (4 modules)

| Module | Save File | Use Case |
|--------|-----------|----------|
| `glitch_free_n_dff_arn` | `glitch_free_n_dff_arn.gtkw` | N-stage CDC synchronizer |
| `reset_sync` | `reset_sync.gtkw` | Reset synchronization |
| `debounce` | `debounce.gtkw` | Button debouncing |

**Debugging Tip:** For CDC, verify data propagation delay matches FLOP_COUNT. Check for metastability resolution time.

---

## Advanced Usage

### Customizing Save Files

You can customize any `.gtkw` file to add your own signal views:

1. Load the save file in GTKWave
2. Add/remove/reorder signals as desired
3. Save: `File → Write Save File`

### Generating VCD vs FST

**VCD (Value Change Dump):**
```bash
pytest val/common/test_module.py --vcd=waves.vcd
```

**FST (Faster, compressed):**
```bash
pytest val/common/test_module.py --fst=waves.fst
```

GTKWave supports both formats. FST is recommended for large simulations.

### Batch Waveform Generation

Generate waveforms for multiple tests:

```bash
for test in val/common/test_counter*.py; do
    module=$(basename $test .py | sed 's/test_//')
    pytest $test --vcd=${module}.vcd
    gtkwave ${module}.vcd val/common/GTKW/${module}.gtkw &
done
```

---

## Regenerating Save Files

If you modify module interfaces or want to regenerate all `.gtkw` files:

```bash
# Regenerate all (overwrites existing files)
python bin/generate_gtkw_files.py --force

# Generate for specific RTL directory
python bin/generate_gtkw_files.py --rtl-dir rtl/custom --output val/custom/GTKW
```

**Script Features:**
- Automatically parses SystemVerilog modules
- Extracts parameters, ports, and internal signals
- Creates standardized signal organization
- Handles modules with/without parameters
- Supports 86/86 modules (100% coverage)

---

## Troubleshooting

### Problem: Save File Doesn't Load

**Solution:** Ensure VCD/FST path in save file matches your waveform file. Edit line 5 of `.gtkw`:
```
[dumpfile] "/absolute/path/to/your/waves.vcd"
```

Or use GTKWave's `File → Read Waveform` first, then `File → Read Save File`.

### Problem: Signals Not Showing

**Solution:**
1. Verify module name matches save file (case-sensitive)
2. Check if module instance name differs from module type
3. Regenerate save file: `python bin/generate_gtkw_files.py --force`

### Problem: Too Many Signals

**Solution:** Hide internal signals by collapsing groups in GTKWave:
- Click `-` next to "Internal Registers" or "Internal Wires"
- Or edit `.gtkw` file and remove unwanted signal lines

---

## Coverage Summary

**Total Modules:** 86
**Save Files Generated:** 86
**Coverage:** 100%

| Category | Modules | .gtkw Files | Coverage |
|----------|---------|-------------|----------|
| Counters | 9 | 9 | 100% |
| Arbiters | 4 | 4 | 100% |
| Data Integrity | 7 | 7 | 100% |
| FIFOs | 4 | 4 | 100% |
| Math | 36 | 36 | 100% |
| Encoders | 4 | 4 | 100% |
| Clock Utils | 4 | 4 | 100% |
| Synchronizers | 4 | 4 | 100% |
| Other | 18 | 18 | 100% |

---

## Related Documentation

- **rtl/common/PRD.md** - Module specifications
- **rtl/common/CLAUDE.md** - AI assistance guide
- **val/common/test_*.py** - Test files
- **bin/generate_gtkw_files.py** - Save file generator

---

## Contributing

To add save files for new modules:

1. Add module to `rtl/common/`
2. Add test to `val/common/`
3. Run: `python bin/generate_gtkw_files.py`
4. Verify save file: `gtkwave test_waves.vcd val/common/GTKW/module.gtkw`
5. Commit both module and `.gtkw` file

---

**Last Updated:** 2025-10-15
**Maintainer:** RTL Design Sherpa Project
**Version:** 1.0
