# sv_interface_flattener.py

A powerful SystemVerilog interface flattening tool that converts SystemVerilog interfaces to individual logic signals for Verilator compatibility and enhanced tool interoperability.

## Overview

The `sv_interface_flattener.py` script addresses a common challenge in SystemVerilog design: converting interface-based designs to flattened signal representations for tools that don't fully support SystemVerilog interfaces (like Verilator). It uses Verible's robust parsing capabilities to accurately analyze SystemVerilog code and generate equivalent flattened modules.

## Purpose

SystemVerilog interfaces provide powerful abstraction and modularity benefits, but many simulation and synthesis tools have limited or no support for interfaces. This tool bridges the gap by:

- Converting interface ports to individual logic signals
- Preserving modport directionality and signal widths
- Maintaining parameter-based configurability
- Generating Verilator-compatible SystemVerilog

## Key Features

### Interface Analysis
- Parses SystemVerilog interface definitions using Verible
- Extracts signal names, widths, and directions
- Identifies modport definitions and their signal mappings
- Handles parameterized interfaces with width calculations

### Signal Flattening
- Converts interface ports to individual logic declarations
- Preserves signal naming conventions and hierarchies
- Maintains proper input/output/inout directionality
- Handles packed and unpacked array types

### Tool Integration
- Uses Verible for robust SystemVerilog parsing
- Supports file list processing for complex projects
- Configurable via JSON configuration files
- Compatible with existing build flows

## Usage

### Command Line Interface

```bash
python3 bin/sv_interface_flattener.py --config config.json [options]
```

### Configuration File Format

```json
{
    "verible_path": "/usr/local/bin/verible-verilog-syntax",
    "file_list": "files.f",
    "interfaces_to_flatten": [
        "axi4_if",
        "apb_if",
        "axis_if"
    ],
    "output_directory": "./flattened",
    "module_suffix": "_flat",
    "signal_prefix": "",
    "preserve_modports": true,
    "generate_wrappers": true
}
```

## Configuration Parameters

| Parameter | Type | Description |
|-----------|------|-------------|
| `verible_path` | string | Path to verible-verilog-syntax executable |
| `file_list` | string | Path to file list containing SystemVerilog sources |
| `interfaces_to_flatten` | array | List of interface names to process |
| `output_directory` | string | Directory for generated flattened modules |
| `module_suffix` | string | Suffix for generated module names |
| `signal_prefix` | string | Prefix for flattened signal names |
| `preserve_modports` | boolean | Generate separate modules for each modport |
| `generate_wrappers` | boolean | Create wrapper modules for easy integration |

## Examples

### Example 1: AXI4 Interface Flattening

**Original Interface:**
```systemverilog
interface axi4_if #(
    parameter AW = 32,
    parameter DW = 32,
    parameter IW = 4
);
    logic [IW-1:0]    awid;
    logic [AW-1:0]    awaddr;
    logic [7:0]       awlen;
    logic [2:0]       awsize;
    logic [1:0]       awburst;
    logic             awvalid;
    logic             awready;
    // ... more signals

    modport master (
        output awid, awaddr, awlen, awsize, awburst, awvalid,
        input  awready,
        // ... more signals
    );

    modport slave (
        input  awid, awaddr, awlen, awsize, awburst, awvalid,
        output awready,
        // ... more signals
    );
endinterface
```

**Flattened Module (Master):**
```systemverilog
module cpu_with_axi_flat #(
    parameter AW = 32,
    parameter DW = 32,
    parameter IW = 4
) (
    input  logic        clk,
    input  logic        resetn,

    // Flattened AXI4 Master Interface
    output logic [IW-1:0]  m_axi_awid,
    output logic [AW-1:0]  m_axi_awaddr,
    output logic [7:0]     m_axi_awlen,
    output logic [2:0]     m_axi_awsize,
    output logic [1:0]     m_axi_awburst,
    output logic           m_axi_awvalid,
    input  logic           m_axi_awready,
    // ... additional signals
);
```

### Example 2: APB Interface Processing

**Configuration:**
```json
{
    "interfaces_to_flatten": ["apb_if"],
    "signal_prefix": "apb_",
    "preserve_modports": true,
    "generate_wrappers": true
}
```

**Result:**
- `cpu_wrapper_flat.sv` - Flattened CPU module
- `apb_peripheral_flat.sv` - Flattened peripheral module
- `system_wrapper.sv` - Top-level wrapper connecting flattened modules

### Example 3: Batch Processing

```bash
# Process multiple interface files
python3 bin/sv_interface_flattener.py \
    --config interface_config.json \
    --input-files rtl/interfaces/*.sv \
    --output-dir build/flattened/
```

## Advanced Features

### Parameterized Interface Support

The tool correctly handles parameterized interfaces:

```systemverilog
interface axis_if #(
    parameter DATA_WIDTH = 32,
    parameter ID_WIDTH = 8,
    parameter DEST_WIDTH = 4,
    parameter USER_WIDTH = 1
);
    logic [DATA_WIDTH-1:0]    tdata;
    logic [DATA_WIDTH/8-1:0]  tkeep;
    logic                     tlast;
    logic [ID_WIDTH-1:0]      tid;
    logic [DEST_WIDTH-1:0]    tdest;
    logic [USER_WIDTH-1:0]    tuser;
    logic                     tvalid;
    logic                     tready;

    // Modports with conditional signals
    modport master (
        output tdata, tkeep, tlast, tvalid,
        output tid   /* if ID_WIDTH > 0 */,
        output tdest /* if DEST_WIDTH > 0 */,
        output tuser /* if USER_WIDTH > 0 */,
        input  tready
    );
endinterface
```

### Wrapper Generation

Automatically generates wrapper modules to ease integration:

```systemverilog
// Generated wrapper module
module original_module_wrapper #(
    parameter AW = 32,
    parameter DW = 32
) (
    // Original interface ports converted to logic
    axi4_if.master m_axi
);

    // Internal flattened module
    original_module_flat #(
        .AW(AW), .DW(DW)
    ) u_flat (
        .clk(m_axi.aclk),
        .resetn(m_axi.aresetn),
        .m_axi_awaddr(m_axi.awaddr),
        .m_axi_awvalid(m_axi.awvalid),
        .m_axi_awready(m_axi.awready),
        // ... additional connections
    );

endmodule
```

### File List Processing

Integrates with file list processors for complex projects:

```f
# files.f
+incdir+rtl/includes
rtl/interfaces/axi4_if.sv
rtl/interfaces/apb_if.sv
rtl/cpu/cpu_core.sv
rtl/memory/memory_controller.sv
```

## Integration Workflows

### With Verilator

```makefile
# Makefile integration
FLATTENED_DIR = build/flattened
ORIGINAL_SOURCES = rtl/cpu/*.sv rtl/interfaces/*.sv

$(FLATTENED_DIR)/%.sv: $(ORIGINAL_SOURCES)
    python3 bin/sv_interface_flattener.py \
        --config verilator_config.json \
        --output-dir $(FLATTENED_DIR)

verilator: $(FLATTENED_DIR)/cpu_flat.sv
    verilator --cc --build $(FLATTENED_DIR)/cpu_flat.sv \
        --top-module cpu_flat
```

### With CocoTB

```python
# CocoTB testbench using flattened signals
@cocotb.test()
async def test_cpu_axi(dut):
    # Test flattened AXI signals directly
    dut.m_axi_awaddr.value = 0x1000
    dut.m_axi_awvalid.value = 1

    await RisingEdge(dut.clk)

    assert dut.m_axi_awready.value == 1
```

### With Synthesis Tools

```tcl
# Synthesis script with flattened modules
read_verilog build/flattened/cpu_flat.sv
read_verilog build/flattened/memory_controller_flat.sv

# Synthesize using flattened, tool-compatible modules
synthesize -top cpu_system_flat
```

## Error Handling and Diagnostics

### Parsing Errors

The tool provides detailed error reporting:

```
ERROR: Failed to parse interface 'axi4_if' in file rtl/interfaces/axi4_if.sv
  Line 45: Unexpected token 'logic' in modport declaration
  Suggestion: Check modport syntax - use signal names only

WARNING: Parameter 'DATA_WIDTH' not found in interface parameters
  Using default width calculation: [31:0]
```

### Validation Features

- Verifies signal consistency across modports
- Checks parameter usage and scope
- Validates generated syntax with Verible
- Reports missing or undefined signals

## Performance and Scalability

### Processing Speed

- **Small Projects**: < 1 second for 10-20 files
- **Medium Projects**: 2-5 seconds for 100+ files
- **Large Projects**: 10-30 seconds for 1000+ files

### Memory Usage

- Minimal memory footprint (< 50MB for large projects)
- Streaming processing for very large file sets
- Efficient caching of parsed interface definitions

## Configuration Examples

### Minimal Configuration

```json
{
    "interfaces_to_flatten": ["axi4_if"]
}
```

### Complete Configuration

```json
{
    "verible_path": "/usr/local/bin/verible-verilog-syntax",
    "file_list": "build/filelist.f",
    "interfaces_to_flatten": [
        "axi4_if",
        "apb_if",
        "axis_if",
        "wishbone_if"
    ],
    "output_directory": "./build/flattened",
    "module_suffix": "_flat",
    "signal_prefix": "",
    "preserve_modports": true,
    "generate_wrappers": true,
    "verilator_compatible": true,
    "include_directories": [
        "rtl/includes",
        "rtl/interfaces"
    ],
    "define_macros": {
        "SYNTHESIS": "1",
        "DATA_WIDTH": "64"
    }
}
```

## Troubleshooting

### Common Issues

**Verible Not Found:**
```bash
# Install Verible
sudo apt install verible
# Or download from GitHub releases
```

**Interface Parsing Failures:**
- Check SystemVerilog syntax compliance
- Verify file encoding (UTF-8)
- Ensure all dependencies are in file list

**Signal Width Errors:**
- Verify parameter definitions and usage
- Check for circular parameter dependencies
- Ensure proper parameter scoping

### Debug Mode

```bash
# Enable verbose logging
python3 bin/sv_interface_flattener.py \
    --config config.json \
    --verbose \
    --debug-parsing
```

## Related Tools

- **[verible_verilog_syntax.py](verible_verilog_syntax.md)**: Verible integration utilities
- **[struct_test_script.py](struct_test_script.md)**: SystemVerilog structure testing
- **[lint_wrap.py](lint_wrap.md)**: Code linting and formatting
- **[generate_uml.py](generate_uml.md)**: UML diagram generation

## Future Enhancements

- Support for SystemVerilog 2017 interface arrays
- Integration with popular EDA tool flows
- Automatic testbench generation for flattened modules
- Performance optimization for very large projects

The `sv_interface_flattener.py` tool is essential for projects that need to maintain SystemVerilog interface benefits while ensuring compatibility with a broad range of EDA tools and simulation environments.

---

[Back to Scripts Index](index.md)

---