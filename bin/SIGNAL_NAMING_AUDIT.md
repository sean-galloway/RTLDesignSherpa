# Signal Naming Conflict Audit Tool

**Script:** `bin/audit_signal_naming_conflicts.py`
**Purpose:** Proactively detect signal naming conflicts in SystemVerilog RTL before writing testbench code
**Version:** 1.0
**Last Updated:** 2025-10-16

---

## Problem Statement

When using AXI factory functions with pattern matching (e.g., `create_axi4_slave_rd(dut, clock, prefix="desc_")`), the factory searches for signals using combinations of prefix + channel patterns.

**The Issue:**
If your RTL has **both** internal signals and external AXI port signals that match the same pattern, the factory will find **multiple different signal objects** and fail during initialization.

**Example Conflict:**
```systemverilog
// Internal signals (simple valid/ready handshake)
logic desc_valid;
logic desc_ready;

// External AXI signals (AR channel)
output logic desc_ar_valid;
input  logic desc_ar_ready;
input  logic desc_r_valid;
output logic desc_r_ready;

// CONFLICT: Both match prefix "desc_" + pattern "*valid"
// Factory will find BOTH desc_valid AND desc_ar_valid!
```

**Impact:**
- Factory initialization fails with "multiple signals found" error
- Testbench development blocked
- RTL signal names must be changed

**Solution:**
This audit script **detects conflicts at RTL definition time**, allowing you to fix naming issues before writing testbench code.

---

## Quick Start

### Installation

The script is ready to use - no installation needed. Just make it executable:

```bash
chmod +x bin/audit_signal_naming_conflicts.py
```

### Basic Usage

```bash
# Scan a single file
./bin/audit_signal_naming_conflicts.py rtl/rapids/rapids_macro/scheduler_group.sv

# Scan entire directory
./bin/audit_signal_naming_conflicts.py rtl/rapids/

# Generate markdown report
./bin/audit_signal_naming_conflicts.py rtl/rapids/ --markdown rtl/rapids/signal_conflicts.md

# Verbose output with code context
./bin/audit_signal_naming_conflicts.py rtl/rapids/ -v
```

---

## Command-Line Options

```
usage: audit_signal_naming_conflicts.py [-h] [-v] [--markdown OUTPUT] path

Audit SystemVerilog files for signal naming conflicts

positional arguments:
  path                  SystemVerilog file or directory to audit

optional arguments:
  -h, --help            show this help message and exit
  -v, --verbose         Enable verbose output
  --markdown OUTPUT     Generate markdown report to specified file
```

---

## Output Format

### Console Output

```
⚠️  Found 2 potential signal naming conflicts:

================================================================================

Conflict #1: Prefix 'desc' [HIGH]
--------------------------------------------------------------------------------

Internal Signals (4):
  - desc_valid                     [scheduler_group.sv:175]
  - desc_ready                     [scheduler_group.sv:176]
  - desc_mon_valid                 [scheduler_group.sv:198]
  - desc_mon_ready                 [scheduler_group.sv:199]

External Signals (4):
  + desc_ar_valid                  [scheduler_group.sv:81] (output)
  + desc_ar_ready                  [scheduler_group.sv:82] (input)
  + desc_r_valid                   [scheduler_group.sv:95] (input)
  + desc_r_ready                   [scheduler_group.sv:96] (output)

📋 Impact:
   When using AXI factory with prefix='desc_', the factory will find
   BOTH internal and external signals, causing initialization to fail.

💡 Solutions:
   1. Rename internal signals: desc_valid → desc_valid_to_sched
   2. Use explicit signal_map parameter in factory call
   3. Test at higher integration level where internal signals are hidden
```

### Markdown Report

The `--markdown` option generates a structured report suitable for documentation:

- Conflict summary with severity levels
- Complete signal listings with line numbers
- SystemVerilog code context for each signal
- Impact analysis
- Recommended solutions

**Example:** See `rtl/rapids/signal_conflicts_report.md` for a complete example.

---

## How It Works

### Detection Algorithm

1. **Signal Collection**
   - Scans .sv and .v files for signal declarations
   - Identifies input/output/inout ports (external signals)
   - Identifies wire/logic/reg declarations (internal signals)
   - Records file path, line number, and code context

2. **Prefix Grouping**
   - Groups signals by common prefixes: desc, prog, data, cmd, resp, m_axi, s_axi, axi

3. **Pattern Matching**
   - Checks if internal signals match AXI channel patterns (ar_valid, r_ready, etc.)
   - Checks if external signals match the same patterns
   - Detects when both internal and external signals match

4. **Conflict Detection**
   - A conflict exists when:
     - Same prefix (e.g., "desc")
     - Internal signal matches simple pattern (e.g., "valid")
     - External signal matches AXI pattern (e.g., "ar_valid")
   - Both would be found by factory pattern matching!

5. **Severity Calculation**
   - **HIGH:** Multiple AXI channels affected OR many signals involved
   - **MEDIUM:** At least one internal and one external signal
   - **LOW:** Minor conflict

### Patterns Detected

**AXI4 Channel Patterns:**
- AR channel: `ar_valid`, `ar_ready`
- R channel: `r_valid`, `r_ready`
- AW channel: `aw_valid`, `aw_ready`
- W channel: `w_valid`, `w_ready`
- B channel: `b_valid`, `b_ready`

**Simple Internal Patterns:**
- `_valid`, `_ready`
- `valid`, `ready`

**Common Prefixes Checked:**
- `desc`, `prog`, `data`, `cmd`, `resp`
- `m_axi`, `s_axi`, `axi`

---

## Recommended Solutions

When conflicts are detected, you have three options:

### Option 1: Rename Internal Signals (Recommended)

**Change internal signal names to avoid pattern matching:**

```systemverilog
// Before (CONFLICT)
logic desc_valid;
logic desc_ready;

// After (NO CONFLICT)
logic desc_to_sched_valid;
logic desc_to_sched_ready;
```

**Pros:**
- Clean solution
- No testbench workarounds needed
- Works with factory pattern matching

**Cons:**
- Requires RTL changes
- May affect existing code

### Option 2: Use Explicit signal_map Parameter

**Bypass pattern matching by providing explicit signal mapping:**

```python
# In testbench
signal_map = {
    'ar_valid': 'desc_ar_valid',
    'ar_ready': 'desc_ar_ready',
    'r_valid': 'desc_r_valid',
    'r_ready': 'desc_r_ready',
    # ... all other signals explicitly mapped
}

desc_axi = create_axi4_slave_rd(
    dut, clock,
    signal_map=signal_map  # Bypass pattern matching
)
```

**Pros:**
- No RTL changes
- Explicit control over signal mapping

**Cons:**
- Verbose testbench code
- Must maintain signal map
- Bypasses factory convenience

### Option 3: Test at Higher Integration Level

**Test at a level where internal signals are hidden:**

```
scheduler_group.sv (has conflicts)
    └── Internal signals NOT visible at top level

miop_top.sv (no conflicts)
    └── Only external AXI ports visible
```

**Pros:**
- No RTL or testbench changes
- Tests more realistic integration

**Cons:**
- Can't test individual block in isolation
- Harder to debug failures

---

## Integration with Development Workflow

### Pre-Commit Checks

Add to your CI/CD pipeline:

```bash
# In .git/hooks/pre-commit or CI script
./bin/audit_signal_naming_conflicts.py rtl/rapids/ || exit 1
```

The script returns exit code 1 if conflicts are found.

### New Module Checklist

Before writing testbench code:

1. ✅ Define RTL module with signals
2. ✅ **Run audit script on new module**
3. ✅ Fix any conflicts (rename internal signals)
4. ✅ Write testbench using factory pattern matching

### Documentation Generation

Generate reports for design reviews:

```bash
# Scan all RTL subsystems
./bin/audit_signal_naming_conflicts.py rtl/rapids/ --markdown docs/miop_signal_conflicts.md
./bin/audit_signal_naming_conflicts.py rtl/amba/ --markdown docs/amba_signal_conflicts.md
./bin/audit_signal_naming_conflicts.py rtl/common/ --markdown docs/common_signal_conflicts.md
```

---

## Examples

### Example 1: Scan Single File

```bash
$ ./bin/audit_signal_naming_conflicts.py rtl/rapids/rapids_macro/scheduler_group.sv

Scanned scheduler_group.sv: 115 signals

⚠️  Found 2 potential signal naming conflicts:
...
```

### Example 2: Scan Directory with Verbose Output

```bash
$ ./bin/audit_signal_naming_conflicts.py rtl/rapids/ -v

Scanning 18 SystemVerilog files in rtl/rapids...
  scheduler.sv: 45 signals
  descriptor_engine.sv: 38 signals
  program_engine.sv: 32 signals
  scheduler_group.sv: 115 signals
  ...

⚠️  Found 2 potential signal naming conflicts:

Conflict #1: Prefix 'desc' [HIGH]
...
Internal Signals (4):
  - desc_valid                     [scheduler_group.sv:175]
    logic                        desc_valid;
  ...
```

### Example 3: Generate Markdown Report

```bash
$ ./bin/audit_signal_naming_conflicts.py rtl/rapids/ --markdown rtl/rapids/signal_conflicts_report.md

Scanning 18 SystemVerilog files in rtl/rapids...

⚠️  Found 2 potential signal naming conflicts:
...

📄 Markdown report written to: rtl/rapids/signal_conflicts_report.md
```

### Example 4: No Conflicts Found

```bash
$ ./bin/audit_signal_naming_conflicts.py rtl/common/counter_bin.sv

Scanned counter_bin.sv: 8 signals

✅ No signal naming conflicts detected!
```

---

## Limitations

### Current Limitations

1. **Pattern Coverage:** Only checks common AXI4 patterns (AR, R, AW, W, B channels)
2. **Prefix List:** Limited to predefined common prefixes
3. **Single File Analysis:** Doesn't analyze cross-module signal usage
4. **SystemVerilog Only:** Supports .sv and .v files, not VHDL

### Future Enhancements

Potential improvements for future versions:

- [ ] Support AXI4-Lite (AXIL) patterns
- [ ] Support AXI-Stream (AXIS) patterns
- [ ] Configurable prefix list (command-line option)
- [ ] Cross-module signal analysis
- [ ] Integration with verilator for more accurate parsing
- [ ] JSON output format for tooling integration
- [ ] Configuration file for custom patterns

---

## Troubleshooting

### Script Reports False Positives

**Issue:** Script reports conflicts that aren't actually problematic.

**Solution:** Review the specific signals and patterns. If the conflict is acceptable (e.g., you're not using factory pattern matching), you can:
- Ignore the warning
- Add exceptions to the script (edit `COMMON_PREFIXES` or pattern lists)

### Script Misses Actual Conflicts

**Issue:** Testbench fails but audit script didn't detect conflict.

**Possible Causes:**
1. Pattern not in script's detection list
2. Prefix not in `COMMON_PREFIXES`
3. Unusual signal naming convention

**Solution:**
- Update script's pattern lists
- File bug report with example RTL

### Permission Denied

**Issue:** `Permission denied` when running script.

**Solution:**
```bash
chmod +x bin/audit_signal_naming_conflicts.py
```

---

## Related Documentation

- **Signal Helper Implementation:** `bin/CocoTBFramework/components/shared/signal_mapping_helper.py`
- **AXI Factory Functions:** `bin/CocoTBFramework/components/axi4/axi4_factories.py`
- **Known Issues:** `rtl/rapids/known_issues/scheduler_group_signal_naming_conflicts.md`
- **Example Report:** `rtl/rapids/signal_conflicts_report.md`

---

## Support and Contributions

### Reporting Issues

If you encounter bugs or have feature requests:

1. Check existing known issues
2. Create detailed bug report with:
   - Example RTL that triggers issue
   - Expected vs actual behavior
   - Script output

### Contributing

Improvements welcome:

- Additional pattern support (AXIL, AXIS, APB)
- Better severity calculation algorithms
- Enhanced reporting formats
- Performance optimizations

---

**Version:** 1.0
**Author:** Claude Code / RTL Design Sherpa Project
**Last Updated:** 2025-10-16
**License:** Same as RTL Design Sherpa repository
