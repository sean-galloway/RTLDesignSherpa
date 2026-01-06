# Contributing to RTL Design Sherpa

Thank you for your interest in contributing to RTL Design Sherpa! This document provides guidelines and information about contributing to this educational hardware design repository.

---

## Table of Contents

- [Code of Conduct](#code-of-conduct)
- [Getting Started](#getting-started)
- [Development Environment](#development-environment)
- [Contribution Types](#contribution-types)
- [RTL Development Guidelines](#rtl-development-guidelines)
- [Testing Requirements](#testing-requirements)
- [Documentation Standards](#documentation-standards)
- [Pull Request Process](#pull-request-process)
- [Coding Standards](#coding-standards)

---

## Code of Conduct

This project follows a standard code of conduct. Be respectful, constructive, and inclusive in all interactions. Focus on technical merit and educational value.

---

## Getting Started

### Prerequisites

- **Python 3.10+** with virtual environment
- **Verilator 5.0+** for simulation
- **CocoTB 1.8+** for verification
- **Git** for version control

### Setting Up Your Environment

```bash
# Clone the repository
git clone https://github.com/sean-galloway/RTLDesignSherpa.git
cd RTLDesignSherpa

# Create and activate virtual environment
python3 -m venv venv
source venv/bin/activate

# Install dependencies
pip install -r requirements.txt

# Verify installation
pytest val/common/test_counter_bin.py -v
```

---

## Development Environment

### Directory Structure

```
rtldesignsherpa/
├── rtl/                    # RTL source code
│   ├── common/            # Reusable building blocks
│   ├── amba/              # AMBA protocol modules
│   └── ...
├── val/                    # Validation tests (pytest + CocoTB)
├── bin/CocoTBFramework/   # Verification infrastructure
├── projects/components/   # Production-ready components
└── docs/                   # Documentation
```

### Key Configuration Files

- `CLAUDE.md` - AI assistant guidelines (read this first!)
- `GLOBAL_REQUIREMENTS.md` - Mandatory coding standards
- `rtl/{subsystem}/PRD.md` - Product requirements for each subsystem
- `rtl/{subsystem}/TASKS.md` - Current work items

---

## Contribution Types

### 1. RTL Modules

New or improved SystemVerilog modules for `rtl/common/` or `rtl/amba/`.

**Requirements:**
- Synthesizable RTL (no vendor-specific primitives except in `rtl/xilinx/`)
- Comprehensive CocoTB test
- Documentation in `docs/markdown/`

### 2. Testbench Components

New verification components for `bin/CocoTBFramework/`.

**Requirements:**
- Python 3.10+ compatible
- Follow existing patterns in the framework
- Include docstrings and usage examples

### 3. Documentation

Improvements to existing documentation or new tutorials.

**Requirements:**
- Markdown format
- Follow existing documentation structure
- No emojis in technical specifications (breaks PDF generation)

### 4. Bug Fixes

Fixes for existing issues.

**Requirements:**
- Include test case that reproduces the bug
- Document the fix in commit message

---

## RTL Development Guidelines

### Before Creating New RTL

**ALWAYS search for existing implementations first:**

```bash
# Search for similar functionality
find rtl/ -name "*.sv" | xargs grep -l "keyword"

# Find module definitions
find rtl/{subsystem}/ -name "*.sv" -exec grep -H "^module" {} \;
```

### Naming Conventions

| Element | Convention | Example |
|---------|------------|---------|
| Module files | `{category}_{function}.sv` | `counter_bin.sv` |
| Parameters | `UPPER_CASE` | `DATA_WIDTH` |
| Input ports | `i_*` | `i_clk`, `i_data` |
| Output ports | `o_*` | `o_valid`, `o_result` |
| Registers | `r_*` | `r_counter`, `r_state` |
| Wires | `w_*` | `w_sum`, `w_match` |
| Reset | `aresetn` | Active-low async reset |
| Clock | `aclk` or `i_clk` | AXI or common modules |

### Module Template

```systemverilog
// Module: module_name
// Description: Brief description of functionality
// Parameters:
//   - PARAM1: Description, valid range, default
// Notes:
//   - Special constraints or assumptions

module module_name #(
    parameter int WIDTH = 8
) (
    input  logic              i_clk,
    input  logic              i_rst_n,
    input  logic [WIDTH-1:0]  i_data,
    output logic [WIDTH-1:0]  o_result
);

    // Internal signals
    logic [WIDTH-1:0] r_data;

    // Sequential logic
    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            r_data <= '0;
        end else begin
            r_data <= i_data;
        end
    end

    assign o_result = r_data;

endmodule
```

---

## Testing Requirements

### Every RTL Module Requires a Test

```bash
# Run specific test
pytest val/{subsystem}/test_{module}.py -v

# Run all tests in subsystem
pytest val/{subsystem}/ -v
```

### Test Structure

Tests in `val/` use CocoTB with pytest:

```python
import cocotb
from cocotb.triggers import RisingEdge, Timer

@cocotb.test(timeout_time=10, timeout_unit="ms")
async def test_basic_operation(dut):
    """Test basic functionality."""
    # Setup
    dut.i_rst_n.value = 0
    await Timer(100, units="ns")
    dut.i_rst_n.value = 1

    # Test
    dut.i_data.value = 0x55
    await RisingEdge(dut.i_clk)

    # Verify
    assert dut.o_result.value == 0x55, "Output mismatch"
```

### Coverage Target

- **Functional coverage:** >95%
- **Code coverage:** >90%

---

## Documentation Standards

### RTL Module Documentation

Every RTL module should have corresponding documentation in `docs/markdown/RTL{Common,Amba}/`.

**Required Sections:**
1. Overview
2. Parameters table
3. Ports table
4. Architecture diagram (Mermaid)
5. Usage example
6. Related documentation links

### No Emojis in Technical Docs

Emojis break PDF generation tools. Use plain text for all technical documentation.

---

## Pull Request Process

### 1. Create a Feature Branch

```bash
git checkout -b feature/module-name
```

### 2. Make Changes

- Follow coding standards
- Add/update tests
- Update documentation

### 3. Run Tests

```bash
# Run affected tests
pytest val/{subsystem}/test_{module}.py -v

# Run lint checks
verilator --lint-only rtl/{subsystem}/{module}.sv
```

### 4. Commit with Descriptive Message

```bash
git commit -m "Add counter_bin module with overflow detection

- Implement parameterized binary counter
- Add comprehensive CocoTB test suite
- Document in RTLCommon/counters/"
```

### 5. Create Pull Request

- Clear title describing the change
- Reference any related issues
- Include test results summary

---

## Coding Standards

### SystemVerilog

- Use `logic` instead of `reg`/`wire`
- Prefer `always_ff` and `always_comb` over `always`
- Use named port connections in instantiations
- Document all parameters and constraints

### Python (Testbenches)

- Follow PEP 8 style guide
- Use type hints where practical
- Include docstrings for classes and functions
- Use async/await patterns for CocoTB

### General

- Keep lines under 100 characters
- Use meaningful variable names
- Comment complex logic
- Avoid magic numbers - use parameters

---

## Questions?

- Check `CLAUDE.md` for AI-assisted development guidelines
- Review `GLOBAL_REQUIREMENTS.md` for mandatory standards
- Look at existing code for patterns and examples
- Open an issue for clarification

---

## License

All contributions are subject to the [MIT License](LICENSE).

---

**Thank you for contributing to RTL Design Sherpa!**
