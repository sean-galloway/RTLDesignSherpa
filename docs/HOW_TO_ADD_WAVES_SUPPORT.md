# How to Add WAVES Support to CocoTB Tests

**Quick Reference:** Add VCD waveform generation support to any CocoTB test file

---

## The Pattern (Copy-Paste Template)

Add this code block to your test function, before the `simulator.run()` call:

```python
import os  # Add to imports if not present

# VCD waveform generation support via WAVES environment variable
# Set WAVES=1 to enable VCD tracing for debugging
compile_args = []
if int(os.environ.get('WAVES', '0')) == 1:
    compile_args.extend([
        "--trace",                  # VCD tracing
        "--trace-depth", "99",      # Full depth
        "--trace-max-array", "1024" # Array tracing
    ])
```

Then add `compile_args=compile_args` to your `simulator.run()` call.

---

## Complete Example

### Before (No WAVES Support)

```python
import pytest
from cocotb_test.simulator import run

def test_axi4_master_basic(request):
    """Basic AXI4 master test."""

    module = "axi4_master_rd"
    toplevel = module
    verilog_sources = [f"../../rtl/amba/axi4/{module}.sv"]
    sim_build = f"sim_build/test_{module}_basic"

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        toplevel=toplevel,
        module=module,
        sim_build=sim_build,
        waves=False,  # Hardcoded - no VCD support!
    )
```

### After (With WAVES Support)

```python
import os  # ← Add this import
import pytest
from cocotb_test.simulator import run

def test_axi4_master_basic(request):
    """Basic AXI4 master test."""

    module = "axi4_master_rd"
    toplevel = module
    verilog_sources = [f"../../rtl/amba/axi4/{module}.sv"]
    sim_build = f"sim_build/test_{module}_basic"

    # VCD waveform generation support via WAVES environment variable
    # Set WAVES=1 to enable VCD tracing for debugging
    compile_args = []
    if int(os.environ.get('WAVES', '0')) == 1:
        compile_args.extend([
            "--trace",                  # VCD tracing
            "--trace-depth", "99",      # Full depth
            "--trace-max-array", "1024" # Array tracing
        ])

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        toplevel=toplevel,
        module=module,
        sim_build=sim_build,
        compile_args=compile_args,  # ← Add this parameter
        waves=False,  # Keep False - we use compile_args instead
    )
```

---

## Usage

```bash
# Run test WITHOUT waveforms (default, faster)
pytest test_axi4_master.py -v

# Run test WITH waveforms (for debugging)
WAVES=1 pytest test_axi4_master.py -v

# View the waveforms
gtkwave sim_build/test_axi4_master_basic/dump.vcd
```

---

## Checklist

When adding WAVES support to a test file:

- [ ] Add `import os` to imports (if not already present)
- [ ] Add the `compile_args` block before `simulator.run()`
- [ ] Add `compile_args=compile_args` parameter to `simulator.run()`
- [ ] Keep `waves=False` (we use compile_args for better control)
- [ ] Test it: `WAVES=1 pytest test_file.py -v`
- [ ] Verify VCD created: `ls sim_build/*/dump.vcd`

---

## Why This Pattern?

1. **VCD over FST**: VCD format is more reliable than FST
2. **Conditional**: No performance impact when WAVES=0 (default)
3. **Full Depth**: `--trace-depth 99` captures all signal levels
4. **Array Support**: `--trace-max-array 1024` for memory tracing
5. **Consistent**: Same pattern across all 189 test files

---

## Troubleshooting

**Q: VCD file not created?**
- Check that `WAVES=1` was set
- Verify `compile_args` was added to `simulator.run()`
- Test must complete successfully (VCD written at end)

**Q: VCD file too large?**
- Use shorter test duration
- Reduce `--trace-depth` to smaller value (e.g., "5")
- Reduce `--trace-max-array` to smaller value (e.g., "256")

**Q: Signals missing in waveform?**
- Increase `--trace-depth` to "99"
- Check module hierarchy in waveform viewer

---

## See Also

- `/TESTING.md` - Complete testing guide
- `/CLAUDE.md` - Repository guide for Claude Code
- `bin/add_waves_support.py` - Automated script (if needed)

---

**Last Updated:** 2025-10-26
