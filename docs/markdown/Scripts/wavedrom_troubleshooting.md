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

# WaveDrom Troubleshooting Guide

**Last Updated:** 2026-01-05
**Purpose:** Comprehensive troubleshooting guide for WaveDrom usage in RTL Design Sherpa

---

## Table of Contents

1. [Overview](#overview)
2. [Installation Issues](#installation-issues)
3. [JSON Syntax Errors](#json-syntax-errors)
4. [Rendering Issues](#rendering-issues)
5. [Integration with Documentation](#integration-with-documentation)
6. [VCD to WaveDrom Conversion](#vcd-to-wavedrom-conversion)
7. [Best Practices](#best-practices)
8. [Common Error Messages](#common-error-messages)
9. [Quick Reference](#quick-reference)

---

## Overview

### What is WaveDrom?

WaveDrom is a digital timing diagram rendering engine that uses JSON to describe and render waveforms. In the RTL Design Sherpa project, WaveDrom is used to:

- Document protocol timing diagrams
- Visualize signal behavior in specifications
- Convert VCD simulation output to readable timing diagrams
- Generate visual documentation for hardware designs

### Where WaveDrom is Used

**Project Locations:**
```
projects/components/bridge/docs/bridge_has/assets/wavedrom/
projects/components/stream/docs/stream_spec/assets/wavedrom/
projects/components/retro_legacy_blocks/docs/pit_8254_mas/assets/wavedrom/
```

**Common Use Cases:**
- Protocol timing specifications (APB, AXI4)
- Reset timing diagrams
- Data flow visualizations
- Multi-channel timing relationships

### WaveDrom Tools in This Project

1. **wavedrom-cli** - Command-line tool for rendering JSON to SVG/PNG
2. **VCD2WaveDrom2** - Python framework for converting VCD simulation output to WaveDrom JSON
3. **md_to_docx.py** - Converts markdown with embedded WaveDrom to DOCX/PDF

---

## Installation Issues

### Issue 1: wavedrom-cli Not Found

**Symptom:**
```bash
$ wavedrom-cli input.json
bash: wavedrom-cli: command not found
```

**Solution:**

Install wavedrom-cli via npm (requires Node.js):

```bash
# Install Node.js if not already installed (Ubuntu/Debian)
sudo apt-get update
sudo apt-get install nodejs npm

# Install wavedrom-cli globally
sudo npm install -g wavedrom-cli

# Verify installation
which wavedrom-cli
wavedrom-cli --version
```

**Alternative Installation (npm user install):**
```bash
# Install to user directory (no sudo required)
npm install -g wavedrom-cli

# Add to PATH if needed
export PATH="$HOME/.npm-global/bin:$PATH"
echo 'export PATH="$HOME/.npm-global/bin:$PATH"' >> ~/.bashrc
```

### Issue 2: python-wavedrom Not Installed

**Symptom:**
```python
>>> import wavedrom
ModuleNotFoundError: No module named 'wavedrom'
```

**Solution:**

Install wavedrom Python package via pip:

```bash
# Install for current user
pip3 install wavedrom --user

# OR install system-wide (requires sudo)
sudo pip3 install wavedrom

# Verify installation
python3 -c "import wavedrom; print(wavedrom.__version__)"
```

**Note:** The RTL Design Sherpa project primarily uses wavedrom-cli for rendering, not the Python package. The Python package is only needed for specific workflows.

### Issue 3: PATH Configuration Problems

**Symptom:**
```bash
$ wavedrom-cli
bash: wavedrom-cli: command not found

# But installation succeeded
$ npm list -g wavedrom-cli
/usr/local/lib
└── wavedrom-cli@2.7.0
```

**Solution:**

Add npm global bin directory to PATH:

```bash
# Find npm global bin path
npm bin -g
# Example output: /usr/local/lib/node_modules/.bin

# Add to PATH temporarily
export PATH="$(npm bin -g):$PATH"

# Add to PATH permanently
echo 'export PATH="$(npm bin -g):$PATH"' >> ~/.bashrc
source ~/.bashrc

# Verify
which wavedrom-cli
```

### Issue 4: Node.js Version Too Old

**Symptom:**
```bash
$ sudo npm install -g wavedrom-cli
npm ERR! engine Unsupported engine
npm ERR! Required: {"node":">=10.0.0"}
npm ERR! Actual:   {"node":"v8.10.0","npm":"3.5.2"}
```

**Solution:**

Upgrade Node.js to a supported version:

```bash
# Ubuntu/Debian - Install Node.js 18.x LTS
curl -fsSL https://deb.nodesource.com/setup_18.x | sudo -E bash -
sudo apt-get install -y nodejs

# Verify version
node --version  # Should be >= 10.0.0
npm --version

# Retry wavedrom-cli installation
sudo npm install -g wavedrom-cli
```

---

## JSON Syntax Errors

### Issue 1: Invalid JSON Structure

**Symptom:**
```bash
$ wavedrom-cli input.json
SyntaxError: Unexpected token } in JSON at position 245
```

**Common Causes:**

1. **Trailing commas** (not allowed in JSON)
2. **Missing quotes** around keys or values
3. **Unmatched braces** or brackets
4. **Comments** (JSON doesn't support comments)

**Example - Wrong:**
```json
{
  "signal": [
    {"name": "clk", "wave": "p..."},
    {"name": "data", "wave": "x345x"},  ← Trailing comma!
  ]
}
```

**Example - Correct:**
```json
{
  "signal": [
    {"name": "clk", "wave": "p..."},
    {"name": "data", "wave": "x345x"}
  ]
}
```

**Validation Tip:**

Use a JSON validator before rendering:

```bash
# Python built-in JSON validator
python3 -m json.tool input.json

# If valid, outputs formatted JSON
# If invalid, shows error message with line number

# Online validators
# https://jsonlint.com/
```

### Issue 2: Signal Name Formatting Errors

**Symptom:**

Diagram renders but signal names appear incorrectly or cause rendering glitches.

**Common Errors:**

1. **Special characters without escaping**
2. **Signal names with spaces** (need quotes)
3. **Reserved characters** in names

**Example - Problematic:**
```json
{
  "signal": [
    {"name": "i_clk & clock", "wave": "p..."},      ← & needs escaping
    {"name": "data[7:0]", "wave": "x345x"},        ← Brackets OK
    {"name": "rst_n", "wave": "01.."}              ← Underscore OK
  ]
}
```

**Best Practice:**

Use alphanumeric characters, underscores, and brackets. Avoid special characters:

```json
{
  "signal": [
    {"name": "i_clk", "wave": "p..."},
    {"name": "data[7:0]", "wave": "x345x"},
    {"name": "rst_n", "wave": "01.."}
  ]
}
```

### Issue 3: Wave String Format Errors

**Symptom:**

Diagram renders with incorrect or missing transitions.

**Valid Wave Characters:**

| Character | Meaning |
|-----------|---------|
| `0` | Low level |
| `1` | High level |
| `x` | Unknown/Don't care |
| `z` | High impedance |
| `.` | Continue previous value |
| `p` | Positive edge clock |
| `n` | Negative edge clock |
| `2-9`, `a-f` | Data values (bus) |
| `=` | Continue previous data |

**Example - Correct Wave Strings:**
```json
{
  "signal": [
    {"name": "clk", "wave": "p......."},           // Clock
    {"name": "rst_n", "wave": "0..1...."},         // Reset
    {"name": "valid", "wave": "0.1..0.."},         // Control signal
    {"name": "data", "wave": "x.345..x."}          // Data bus
  ]
}
```

**Common Mistakes:**
```json
// WRONG: Invalid characters
{"name": "clk", "wave": "p p p p"}    // Spaces not allowed
{"name": "data", "wave": "123456789"} // Only 2-9 valid (use =)
{"name": "valid", "wave": "hi..lo"}   // Use 1 and 0, not hi/lo

// CORRECT:
{"name": "clk", "wave": "pppp"}
{"name": "data", "wave": "2345678="}
{"name": "valid", "wave": "1...0"}
```

### Issue 4: Missing Required Fields

**Symptom:**
```
TypeError: Cannot read property 'wave' of undefined
```

**Cause:**

Missing required "signal" array or "wave" field in signal objects.

**Minimum Valid Structure:**
```json
{
  "signal": [
    {"name": "signal_name", "wave": "0.1."}
  ]
}
```

**Optional Fields:**
```json
{
  "signal": [
    {"name": "clk", "wave": "p.........", "period": 1},
    {"name": "data", "wave": "x.345..x..", "data": ["A", "B", "C"]},
    {}  // Empty object creates separator line
  ],
  "head": {"text": "Diagram Title"},
  "foot": {"text": "Footer text"},
  "edge": ["a<->b Transfer Time"]
}
```

---

## Rendering Issues

### Issue 1: Empty or Blank Diagram

**Symptom:**

wavedrom-cli executes without error but generates empty/blank SVG or PNG.

**Common Causes:**

1. **All signals have same value** (no transitions)
2. **Wave strings too short** (diagram has no width)
3. **Incorrect scaling parameters**

**Debug Steps:**

```bash
# Step 1: Check JSON syntax
python3 -m json.tool input.json

# Step 2: Try rendering to SVG (easier to debug)
wavedrom-cli -i input.json -s output.svg

# Step 3: Open SVG in browser/text editor to inspect
cat output.svg

# Step 4: Verify signal transitions exist
grep "wave" input.json
```

**Example - No Transitions (renders empty):**
```json
{
  "signal": [
    {"name": "clk", "wave": "1"},  // Too short!
    {"name": "data", "wave": "x"}  // No transitions
  ]
}
```

**Example - Proper Diagram:**
```json
{
  "signal": [
    {"name": "clk", "wave": "p......."},  // 8 cycles
    {"name": "data", "wave": "x.345.x.."}  // Clear transitions
  ]
}
```

### Issue 2: Missing Signals

**Symptom:**

Some signals don't appear in rendered diagram, but JSON is valid.

**Cause 1: Signal filtered by node/edge configuration**

Check if signal has node markers that might be filtering it.

**Cause 2: Wave string too short**

If wave strings have different lengths, shorter ones may not render fully.

**Solution:**

Make all wave strings the same length using `.` (continue):

```json
{
  "signal": [
    {"name": "clk", "wave": "p........"},   // 9 characters
    {"name": "valid", "wave": "01....0.."},  // 9 characters
    {"name": "data", "wave": "x.345..x.."}   // 9 characters
  ]
}
```

### Issue 3: Timing Misalignment

**Symptom:**

Signals appear misaligned or transitions don't line up correctly.

**Cause:**

Wave strings have different lengths or incorrect period settings.

**Solution:**

1. **Ensure all wave strings same length:**

```json
{
  "signal": [
    {"name": "clk", "wave": "p......."},    // 8 chars
    {"name": "valid", "wave": "0..1..0."},   // 8 chars
    {"name": "data", "wave": "x..345.x."}    // 8 chars
  ]
}
```

2. **Use period parameter for clock signals:**

```json
{
  "signal": [
    {"name": "clk", "wave": "p.........", "period": 1},     // Base period
    {"name": "clk_div2", "wave": "p.........", "period": 2}, // Half frequency
    {"name": "data", "wave": "x.345..x..."}
  ]
}
```

### Issue 4: Scale and Width Problems

**Symptom:**

Diagram too small/large or doesn't fit in document.

**Solution 1: Adjust hscale (horizontal scale):**

```json
{
  "signal": [
    {"name": "clk", "wave": "p......."}
  ],
  "config": {"hscale": 2}  // 2x horizontal scale (wider)
}
```

**Solution 2: Use SVG output for better scaling:**

```bash
# SVG scales better than PNG
wavedrom-cli -i input.json -s output.svg

# Or render PNG at specific width
wavedrom-cli -i input.json --width 1200 -o output.png
```

**Solution 3: Adjust skin (rendering style):**

```json
{
  "signal": [
    {"name": "clk", "wave": "p......."}
  ],
  "config": {
    "hscale": 1,
    "skin": "narrow"  // Options: narrow, default
  }
}
```

---

## Integration with Documentation

### Issue 1: Markdown Embedded WaveDrom Not Rendering

**Symptom:**

WaveDrom code blocks in markdown don't render in generated documentation.

**Typical Markdown Pattern:**
````markdown
```wavedrom
{
  "signal": [
    {"name": "clk", "wave": "p......."}
  ]
}
```
````

**Cause:**

Documentation toolchain doesn't support WaveDrom rendering.

**Solution for RTL Design Sherpa:**

Use external JSON files and reference them:

**Step 1: Create WaveDrom JSON file:**
```bash
# projects/components/stream/docs/stream_spec/assets/wavedrom/apb_read_access.json
{
  "signal": [
    {"name": "pclk", "wave": "p......."},
    {"name": "psel", "wave": "01....0."},
    {"name": "penable", "wave": "0.1..0.."},
    {"name": "pready", "wave": "0...10.."}
  ],
  "head": {"text": "APB Read Access"}
}
```

**Step 2: Render to SVG/PNG:**
```bash
cd projects/components/stream/docs/stream_spec/assets/wavedrom/
wavedrom-cli -i apb_read_access.json -s apb_read_access.svg
```

**Step 3: Reference in markdown:**
```markdown
## APB Read Timing

![APB Read Access](assets/wavedrom/apb_read_access.svg)
```

### Issue 2: md_to_docx.py WaveDrom Integration

**Symptom:**

WaveDrom diagrams don't appear in generated DOCX/PDF files.

**Current Status:**

As of 2026-01-05, md_to_docx.py does NOT directly support inline WaveDrom code blocks.

**Workaround:**

Pre-render WaveDrom JSON to SVG/PNG and reference as images:

```bash
# Step 1: Render all WaveDrom files
cd docs/stream_spec/assets/wavedrom/
for file in *.json; do
    wavedrom-cli -i "$file" -s "${file%.json}.svg"
done

# Step 2: Reference SVG files in markdown
# See Issue 1 solution above

# Step 3: Run md_to_docx.py
cd /mnt/data/github/rtldesignsherpa
python3 bin/md_to_docx.py docs/stream_spec/index.md output.docx
```

### Issue 3: External JSON File References

**Symptom:**

Documentation build can't find external WaveDrom JSON files.

**Best Practice - Organized File Structure:**

```
projects/components/{component}/docs/{doc_name}/
├── index.md
├── chapter1.md
├── chapter2.md
└── assets/
    └── wavedrom/
        ├── timing1.json
        ├── timing1.svg        ← Rendered output
        ├── timing2.json
        └── timing2.svg
```

**Markdown Reference Pattern:**
```markdown
# In chapter1.md

## Timing Diagram

![Timing 1](assets/wavedrom/timing1.svg)
```

**Generation Script:**
```bash
#!/bin/bash
# projects/components/stream/docs/stream_spec/render_wavedrom.sh

WAVEDROM_DIR="assets/wavedrom"

for json_file in ${WAVEDROM_DIR}/*.json; do
    svg_file="${json_file%.json}.svg"
    echo "Rendering $json_file -> $svg_file"
    wavedrom-cli -i "$json_file" -s "$svg_file"
done
```

### Issue 4: Version Control Considerations

**Question:** Should generated SVG/PNG files be version controlled?

**Recommendation:**

**Commit both JSON and rendered SVG/PNG:**

1. **JSON files** - Source of truth, easy to diff
2. **SVG/PNG files** - Required for documentation build

**Rationale:**
- SVG files are relatively small (text-based)
- Not everyone has wavedrom-cli installed
- CI/CD builds need pre-rendered images
- Git diffs show changes to JSON (human-readable)

**.gitignore pattern (if desired):**
```gitignore
# Optionally ignore rendered files (regenerate in CI)
# **/wavedrom/*.svg
# **/wavedrom/*.png

# But commit JSON source
!**/wavedrom/*.json
```

---

## VCD to WaveDrom Conversion

### Overview

The VCD2WaveDrom2 framework converts Value Change Dump (VCD) simulation output to WaveDrom JSON format.

**Primary Script:** `bin/project_automation/v2w/vcd2wavedrom2.py`

**Documentation:**
- [VCD2WaveDrom2 Class](vcd2wavedrom2.md)
- [V2WConfig Class](v2wconfig.md)
- [V2WConvert Class](v2wconvert.md)

### Issue 1: Basic Usage

**Workflow:**

```bash
# Step 1: Run simulation to generate VCD
cd val/amba/
pytest test_axi_monitor.py --vcd=output.vcd

# Step 2: (Optional) Generate GTKWave save file for signal grouping
gtkwave output.vcd
# File -> Write Save File -> output.gtkw

# Step 3: Convert VCD to WaveDrom JSON
cd ../../bin/project_automation/v2w/
python3 vcd2wavedrom2.py -i ../../../val/amba/output.vcd -o timing.json

# Step 4: Render JSON to SVG
wavedrom-cli -i timing.json -s timing.svg
```

### Issue 2: Signal Selection and Filtering

**Problem:**

VCD file contains hundreds of signals, but only need a few for diagram.

**Solution 1: Use GTKWave save file for signal selection:**

```bash
# Step 1: Open VCD in GTKWave
gtkwave output.vcd

# Step 2: Select signals of interest in GTKWave UI
# Drag signals from SST (Signal Search Tree) to Signals pane

# Step 3: Organize into groups (optional)
# Right-click in Signals pane -> Insert Group

# Step 4: Save configuration
# File -> Write Save File (as .gtkw)

# Step 5: Convert using GTKWave config
python3 vcd2wavedrom2.py -i output.vcd -g output.gtkw -o timing.json
```

**Solution 2: Use signal filtering in configuration:**

Create configuration file (config.json):
```json
{
  "signals": [
    "top.dut.aclk",
    "top.dut.aresetn",
    "top.dut.s_axi4_awvalid",
    "top.dut.s_axi4_awready"
  ],
  "start_time": "0ns",
  "end_time": "1us",
  "sample_rate": "10ns"
}
```

Run with config:
```bash
python3 vcd2wavedrom2.py -i output.vcd -c config.json -o timing.json
```

### Issue 3: Time Window Selection

**Problem:**

VCD file contains entire simulation (10ms), but only need to show specific time window (100ns-200ns).

**Solution:**

Use start_time and end_time parameters:

```bash
python3 vcd2wavedrom2.py \
    -i output.vcd \
    -o timing.json \
    --start-time 100ns \
    --end-time 200ns
```

**Or in configuration file:**
```json
{
  "start_time": "100ns",
  "end_time": "200ns",
  "sample_rate": "1ns"
}
```

### Issue 4: Clock Signal Detection

**Problem:**

Clock signals not rendering properly (appear as data instead of clock waves).

**Cause:**

VCD2WaveDrom2 auto-detects clocks based on toggle rate, but may miss some.

**Solution:**

Manually mark clock signals in configuration:

```json
{
  "signals": [
    {"name": "top.dut.aclk", "is_clock": true, "period": "10ns"},
    {"name": "top.dut.pclk", "is_clock": true, "period": "5ns"},
    {"name": "top.dut.data", "is_clock": false}
  ]
}
```

**WaveDrom Clock Representation:**

Clocks should use `p` (posedge) or `n` (negedge) wave characters:
```json
{
  "signal": [
    {"name": "aclk", "wave": "p.........", "period": 1},
    {"name": "data", "wave": "x.345..x.."}
  ]
}
```

### Issue 5: Signal Name Hierarchical Path Issues

**Problem:**

VCD signal names are hierarchical (top.dut.submodule.signal), making diagrams cluttered.

**Solution 1: Rename signals in generated JSON:**

```python
# Post-process generated JSON
import json

with open('timing.json', 'r') as f:
    data = json.load(f)

# Shorten signal names
for sig in data['signal']:
    if 'name' in sig:
        # top.dut.axi4_awvalid -> awvalid
        sig['name'] = sig['name'].split('.')[-1]

with open('timing_clean.json', 'w') as f:
    json.dump(data, f, indent=2)
```

**Solution 2: Configure signal aliases:**

```json
{
  "signals": [
    {
      "vcd_name": "top.dut.s_axi4_awvalid",
      "wavedrom_name": "awvalid"
    },
    {
      "vcd_name": "top.dut.s_axi4_awready",
      "wavedrom_name": "awready"
    }
  ]
}
```

### Issue 6: Bus Signal Handling

**Problem:**

Multi-bit bus signals (e.g., data[7:0]) show individual bits instead of aggregated bus value.

**Solution:**

VCD2WaveDrom2 should auto-detect buses. If not working:

```bash
# Check VCD file structure
grep "data\[" output.vcd

# Ensure VCD has proper vector declaration
# $var wire 8 ! data [7:0] $end
```

**Manual Bus Configuration:**
```json
{
  "signals": [
    {
      "name": "data",
      "bits": ["data[7]", "data[6]", "data[5]", "data[4]",
               "data[3]", "data[2]", "data[1]", "data[0]"],
      "is_bus": true
    }
  ]
}
```

### Issue 7: Sample Rate and Resolution

**Problem:**

Generated diagram has too few/too many samples, missing transitions.

**Solution:**

Adjust sample_rate parameter:

```bash
# High resolution (slow simulation, detailed diagram)
python3 vcd2wavedrom2.py -i output.vcd -o timing.json --sample-rate 1ns

# Lower resolution (fast simulation, overview diagram)
python3 vcd2wavedrom2.py -i output.vcd -o timing.json --sample-rate 10ns
```

**Rule of Thumb:**
- Sample rate should be ≤ fastest clock period / 2 (Nyquist)
- For 10ns clock period, use ≤ 5ns sample rate

### Issue 8: Common Conversion Problems

**Problem 1: "No signals found in VCD"**

**Cause:** VCD file empty or corrupted

**Solution:**
```bash
# Verify VCD has content
head -20 output.vcd

# Should see:
# $date ... $end
# $version ... $end
# $timescale 1ns $end
# $scope module top $end
# ...

# Re-run simulation with VCD generation
pytest test_module.py --vcd=output.vcd -v
```

**Problem 2: "Timescale parsing failed"**

**Cause:** VCD file missing or malformed $timescale directive

**Solution:**
```bash
# Check timescale in VCD
grep timescale output.vcd

# Should be: $timescale 1ns $end

# If missing, simulator didn't generate properly
# Add to RTL top-level:
`timescale 1ns / 1ps
```

**Problem 3: "Maximum time exceeded"**

**Cause:** VCD file too large or simulation time too long

**Solution:**
```bash
# Limit time window
python3 vcd2wavedrom2.py \
    -i output.vcd \
    -o timing.json \
    --end-time 1us  # Only first microsecond
```

---

## Best Practices

### 1. Signal Naming Conventions

**For Readability:**

Use descriptive but concise names:

```json
// ✅ GOOD:
{"name": "axi4_awvalid", "wave": "01..0"},
{"name": "axi4_awready", "wave": "1...."},
{"name": "rst_n", "wave": "01..."}

// ❌ AVOID:
{"name": "top.dut.u_axi_interconnect.s0_axi4_awvalid", "wave": "01..0"},  // Too long
{"name": "sig1", "wave": "01..0"},  // Not descriptive
{"name": "axi4 aw-valid signal", "wave": "01..0"}  // Spaces problematic
```

**Hierarchy Guidelines:**
- Use underscores for clarity: `axi4_awvalid`
- Include protocol/interface prefix: `apb_psel`, `axi4_rvalid`
- For buses, use brackets: `data[7:0]`

### 2. Keeping Diagrams Readable

**Group Related Signals:**

```json
{
  "signal": [
    {"name": "clk", "wave": "p......."},
    {},  // Separator
    ["Write Address Channel",
      {"name": "awvalid", "wave": "01....0."},
      {"name": "awready", "wave": "1......."},
      {"name": "awaddr", "wave": "x.3...x.", "data": ["0x1000"]}
    ],
    {},  // Separator
    ["Write Data Channel",
      {"name": "wvalid", "wave": "0.1...0."},
      {"name": "wready", "wave": "1......."},
      {"name": "wdata", "wave": "x.4...x.", "data": ["0xDEAD"]}
    ]
  ],
  "head": {"text": "AXI4 Write Transaction"}
}
```

**Limit Diagram Width:**
- Keep wave strings to 10-20 characters for readability
- Use multiple diagrams for long sequences
- Focus on specific protocol phases

**Use Annotations:**

```json
{
  "signal": [
    {"name": "clk", "wave": "p.........", "node": ".a.b....."},
    {"name": "valid", "wave": "01..0.....", "node": "..c......"},
    {"name": "data", "wave": "x.345..x..", "node": "..d......"}
  ],
  "edge": [
    "a<->b Setup Time",
    "c->d Data Valid"
  ]
}
```

### 3. Color Usage

**Standard WaveDrom Colors (Implicit):**

WaveDrom assigns colors automatically based on signal value:
- `0`, `1` - Standard logic levels (blue/green)
- `2-9`, `a-f` - Data values (different colors per value)
- `x` - Unknown (gray)
- `z` - High-Z (gray striped)

**Custom Colors (Advanced):**

Use "data" arrays for colored annotations:

```json
{
  "signal": [
    {"name": "state", "wave": "2.3.4.5", "data": ["IDLE", "ADDR", "DATA", "DONE"]}
  ]
}
```

**Best Practice:**
- Rely on default coloring for consistency
- Use data labels for clarity, not color
- Colors may not render identically across all viewers

### 4. Annotation Tips

**Use Edges for Timing Relationships:**

```json
{
  "signal": [
    {"name": "clk", "wave": "p.........", "node": ".a....b.."},
    {"name": "setup", "wave": "0.1.0.....", "node": "..c......"},
    {"name": "sample", "wave": "0....1.0..", "node": "......d.."}
  ],
  "edge": [
    "a<->c Setup Time: 20ns",
    "b<->d Hold Time: 5ns"
  ]
}
```

**Use Head/Foot for Context:**

```json
{
  "signal": [
    {"name": "aclk", "wave": "p......."},
    {"name": "awvalid", "wave": "01....0."}
  ],
  "head": {
    "text": "AXI4 Write Address Phase",
    "tick": 0
  },
  "foot": {
    "text": "Timing assumes 100MHz clock (10ns period)"
  }
}
```

**Label Data Values:**

```json
{
  "signal": [
    {"name": "addr", "wave": "x.3.4.x", "data": ["0x1000", "0x1004"]},
    {"name": "data", "wave": "x.5.6.x", "data": ["0xDEAD", "0xBEEF"]}
  ]
}
```

### 5. Documentation Integration Patterns

**Pattern 1: Specification Diagrams**

Store in `docs/{doc_name}/assets/wavedrom/`:

```
docs/stream_spec/
├── assets/
│   └── wavedrom/
│       ├── apb_read_access.json
│       ├── apb_read_access.svg
│       ├── apb_write_access.json
│       └── apb_write_access.svg
└── protocol_timing.md
```

**Pattern 2: Simulation-Derived Diagrams**

```
val/amba/
├── sim_results/
│   ├── test_axi_monitor.vcd
│   └── test_axi_monitor.gtkw
├── docs/
│   └── waveforms/
│       ├── axi_monitor_basic.json
│       └── axi_monitor_basic.svg
└── test_axi_monitor.py
```

**Pattern 3: Test Documentation**

```python
# test_axi_monitor.py

@cocotb.test()
async def test_basic_write(dut):
    """
    Test AXI4 write transaction.

    Timing diagram: docs/waveforms/axi_write_basic.svg

    Expected behavior:
    1. AWVALID asserted with address
    2. AWREADY handshake
    3. WVALID asserted with data
    ...
    """
```

### 6. Version Control Best Practices

**Commit Strategy:**

```bash
# Commit both source and rendered
git add docs/stream_spec/assets/wavedrom/timing.json
git add docs/stream_spec/assets/wavedrom/timing.svg
git commit -m "Add APB timing diagram for specification"
```

**Regeneration Script:**

```bash
#!/bin/bash
# docs/stream_spec/render_all_wavedrom.sh

WAVEDROM_DIR="assets/wavedrom"

echo "Rendering WaveDrom diagrams..."
for json_file in ${WAVEDROM_DIR}/*.json; do
    svg_file="${json_file%.json}.svg"
    echo "  $json_file -> $svg_file"
    wavedrom-cli -i "$json_file" -s "$svg_file" || exit 1
done
echo "All WaveDrom diagrams rendered successfully."
```

**Pre-commit Hook (Optional):**

```bash
#!/bin/bash
# .git/hooks/pre-commit

# Auto-render modified WaveDrom JSON files
for json_file in $(git diff --cached --name-only --diff-filter=ACM | grep '\.json$' | grep wavedrom); do
    svg_file="${json_file%.json}.svg"
    echo "Rendering $json_file -> $svg_file"
    wavedrom-cli -i "$json_file" -s "$svg_file"
    git add "$svg_file"
done
```

---

## Common Error Messages

### wavedrom-cli Errors

**Error 1:**
```
Error: Cannot find module 'wavedrom'
```

**Solution:** Reinstall wavedrom-cli:
```bash
sudo npm install -g wavedrom-cli
```

**Error 2:**
```
SyntaxError: Unexpected token } in JSON
```

**Solution:** Validate JSON syntax:
```bash
python3 -m json.tool input.json
# Fix reported errors (trailing commas, missing quotes, etc.)
```

**Error 3:**
```
Error: ENOENT: no such file or directory
```

**Solution:** Check file path:
```bash
ls -la input.json
# Use absolute path if needed
wavedrom-cli -i /full/path/to/input.json -s output.svg
```

### VCD2WaveDrom2 Errors

**Error 1:**
```
ValueError: No timescale found in VCD file
```

**Solution:** Add timescale to RTL:
```systemverilog
`timescale 1ns / 1ps

module top;
    // ...
endmodule
```

**Error 2:**
```
KeyError: 'signal'
```

**Solution:** Check JSON structure has required "signal" array:
```json
{
  "signal": [  // Required!
    {"name": "clk", "wave": "p..."}
  ]
}
```

**Error 3:**
```
RuntimeError: VCD file corrupted or incomplete
```

**Solution:** Re-run simulation ensuring VCD generation completes:
```bash
# Check if simulation completed
tail output.vcd
# Should end with: #<final_time>

# Re-run test
pytest test_module.py --vcd=output.vcd -v
```

### JSON Validation Errors

**Error 1:**
```
JSONDecodeError: Expecting ',' delimiter
```

**Solution:** Missing comma between array/object elements:
```json
// WRONG:
{"name": "clk", "wave": "p..."}
{"name": "data", "wave": "x345"}  // Missing comma above!

// CORRECT:
{"name": "clk", "wave": "p..."},
{"name": "data", "wave": "x345"}
```

**Error 2:**
```
JSONDecodeError: Expecting property name enclosed in double quotes
```

**Solution:** JSON keys must use double quotes:
```json
// WRONG:
{signal: [...]}  // Missing quotes
{'signal': [...]}  // Single quotes

// CORRECT:
{"signal": [...]}  // Double quotes
```

---

## Quick Reference

### Basic WaveDrom Syntax

```json
{
  "signal": [
    {"name": "clk", "wave": "p.........", "period": 1},
    {"name": "rst_n", "wave": "0...1....."},
    {},
    {"name": "valid", "wave": "0.1...0..."},
    {"name": "ready", "wave": "1........."},
    {"name": "data", "wave": "x.345...x.", "data": ["A", "B", "C"]}
  ],
  "head": {"text": "Example Timing Diagram"},
  "foot": {"text": "Footer text"}
}
```

### Wave Characters Quick Reference

| Char | Meaning | Use Case |
|------|---------|----------|
| `p` | Positive edge clock | Clock signals |
| `n` | Negative edge clock | Inverted clocks |
| `0` | Logic 0 | Control signals |
| `1` | Logic 1 | Control signals |
| `x` | Unknown/Don't care | Initial states |
| `z` | High impedance | Tri-state buses |
| `.` | Continue previous | Hold value |
| `2-9` | Data value | Bus data |
| `=` | Continue data | Hold bus value |

### Command Reference

```bash
# Render JSON to SVG
wavedrom-cli -i input.json -s output.svg

# Render JSON to PNG
wavedrom-cli -i input.json -o output.png

# Render with specific width
wavedrom-cli -i input.json --width 1200 -o output.png

# Validate JSON
python3 -m json.tool input.json

# Convert VCD to WaveDrom
python3 bin/project_automation/v2w/vcd2wavedrom2.py \
    -i simulation.vcd \
    -o timing.json \
    --start-time 0ns \
    --end-time 1us
```

### File Organization Template

```
docs/{component}/
├── assets/
│   └── wavedrom/
│       ├── timing1.json      # Source
│       ├── timing1.svg       # Rendered
│       ├── timing2.json
│       └── timing2.svg
├── chapter1.md               # References: ![](assets/wavedrom/timing1.svg)
└── render_wavedrom.sh        # Regeneration script
```

---

## Additional Resources

### Official Documentation

- **WaveDrom Official:** https://wavedrom.com/
- **WaveDrom Tutorial:** https://wavedrom.com/tutorial.html
- **WaveDrom Editor:** https://wavedrom.com/editor.html (online testing)

### RTL Design Sherpa Documentation

- [VCD to WaveDrom 2](vcd2wavedrom2.md) - Main converter class
- [V2W Config](v2wconfig.md) - Configuration handling
- [V2W Convert](v2wconvert.md) - Conversion utilities
- [Scripts Index](index.md) - All script documentation

### GTKWave Resources

- **GTKWave Manual:** http://gtkwave.sourceforge.net/gtkwave.pdf
- **VCD Format Specification:** IEEE 1364-2001 Standard

### JSON Resources

- **JSON Validator:** https://jsonlint.com/
- **JSON Formatter:** https://jsonformatter.org/

---

[Back to Scripts Index](index.md)

---
