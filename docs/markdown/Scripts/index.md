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

**[← Back to Main Index](../index.md)**

# Python Scripts and Tools

This directory contains comprehensive documentation for all Python scripts and tools in the RTL Design Sherpa framework. These tools support RTL design, verification, analysis, and automation workflows.

## Quick Start

For common tasks, check out the [Cheat Sheet](./cheat_sheet.md) which covers the most frequently used scripts and their basic usage patterns.

## Main Command Line Tools

### Design and Analysis Tools

* **[AXI Split Calculator](axi_split_calculator.md)** - Calculate AXI transaction splitting for boundary compliance
* **[SystemVerilog Interface Flattener](sv_interface_flattener.md)** - Convert SystemVerilog interfaces to logic signals for Verilator compatibility
* **[Generate UML](generate_uml.md)** - Create UML diagrams from SystemVerilog code structure
* **[Find Instances Used](find_instances_used.md)** - Analyze module instantiation dependencies
* **[Structure Test Script](struct_test_script.md)** - Automated structural testing framework

### Code Quality and Formatting

* **[Lint Wrapper](lint_wrap.md)** - Wrapper for Verible linting and formatting tools
* **[Case Fix](casefix.md)** - Fix SystemVerilog case statement formatting
* **[Search and Replace Directory](search_and_replace_directory.md)** - Batch text processing across project files

### RTL Generation and Math

* **[Math Generate](math_generate.md)** - Generate optimized adder and multiplier RTL
* **[ECC Generate](ecc_generate.md)** - Generate Hamming encoder/decoder RTL

### Documentation and Visualization

* **[VCD to Wavedrom 2](vcd2wavedrom2.md)** - Convert VCD simulation data to Wavedrom diagrams
* **[Markdown Filename Massage](md_filename_massage.md)** - Batch process markdown file names and paths
* **[Markdown to DOCX](md_to_docx.md)** - Convert markdown documentation to Word format
* **[PyTree](pytree.md)** - Generate directory tree visualizations

### Test Automation and Analysis

* **[Update FST Tracing](update_fst_tracing.md)** - Update FST waveform tracing in RTL files

## Core Framework Classes

### Primary Infrastructure

* **[Lint](lint.md)** - Core linting functionality and Verible integration
* **[REMatcher](REMatcher.md)** - Regular expression matching utilities

### Math Generation Framework

The math generation system creates optimized arithmetic RTL:

* **[Brent Kung Adder](brent_kung_adder.md)** - Parallel prefix adder generation
* **[Dadda Multiplier](dadda_multiplier.md)** - High-speed multiplier architecture
* **[Wallace Multiplier](wallace_multiplier.md)** - Wallace tree multiplier implementation

### SystemVerilog Generation Classes

Core classes for programmatic RTL generation:

* **[Verilog Class Overview](verilog_class_overview.md)** - Architecture overview of RTL generation framework
* **[Module](module.md)** - SystemVerilog module representation and generation
* **[Signal](signal.md)** - Signal declaration and manipulation
* **[Parameter](param.md)** - Parameter handling and generation
* **[Verilog Parser](verilog_parser.md)** - SystemVerilog parsing and analysis

### Math Generation Building Blocks

Low-level components for arithmetic circuit generation:

* **[Bit-wise PG Logic](bitwise_pg_logic.md)** - Propagate/Generate logic for adders
* **[PG](pg.md)** - Core PG logic implementation
* **[Black](black.md)** - Black cell implementation for parallel prefix
* **[Gray](gray.md)** - Gray cell implementation for parallel prefix
* **[Group PG Logic](group_pg_logic.md)** - Grouped propagate/generate logic
* **[Multiplier Mixin](multiplier_mixin.md)** - Common multiplier functionality
* **[Utils](utils.md)** - Utility functions for math generation
* **[Sum Logic](sum_logic.md)** - Final sum generation logic

### VCD to Wavedrom Components

Tools for waveform visualization:

* **[VCD2Wavedrom2](vcd2wavedrom2.md)** - Main converter functionality
* **[V2WConvert](v2wconvert.md)** - Core conversion logic
* **[V2WConfig](v2wconfig.md)** - Configuration handling for waveform conversion

## Tool Categories

### By Function

**Design Tools:**
- axi_split_calculator.py
- sv_interface_flattener.py
- generate_uml.py
- math_generate.py

**Analysis Tools:**
- find_instances_used.py
- struct_test_script.py
- update_fst_tracing.py

**Code Quality:**
- lint_wrap.py
- casefix.py
- search_and_replace_directory.py

**Documentation:**
- vcd2wavedrom2.py
- md_filename_massage.py
- md_to_docx.py
- pytree.py

### By Complexity

**Simple Utilities:**
- casefix.py
- search_and_replace_directory.py
- pytree.py

**Intermediate Tools:**
- lint_wrap.py
- math_generate.py
- md_to_docx.py

**Advanced Frameworks:**
- sv_interface_flattener.py
- axi_split_calculator.py
- vcd2wavedrom2.py
- generate_uml.py

## Installation and Dependencies

Most scripts require:
- Python 3.8+
- Standard library modules
- Project-specific dependencies (see individual documentation)

### External Tool Dependencies

Some scripts require external tools:
- **Verible**: For SystemVerilog parsing and linting
- **Graphviz**: For UML diagram generation
- **Pandoc**: For document conversion (optional)

### Usage Patterns

**Command Line:**
```bash
python3 bin/script_name.py [options]
```

**Import as Module:**
```python
from bin.project_automation.module_name import ClassName
```

**Configuration-Based:**
Many tools support JSON configuration files for complex setups.

## Development Guidelines

### Adding New Scripts

1. Place script in appropriate `bin/` subdirectory
2. Follow existing naming conventions
3. Include comprehensive docstrings
4. Add corresponding documentation in `docs/markdown/Scripts/`
5. Update this index file

### Documentation Standards

- One markdown file per script
- Include purpose, usage examples, and parameter descriptions
- Show both command-line and programmatic usage
- Document configuration file formats
- Include troubleshooting sections

## Integration with RTL Design Flow

These tools integrate with the broader RTL design and verification flow:

1. **Design Phase**: math_generate.py, generate_uml.py
2. **Analysis Phase**: find_instances_used.py, struct_test_script.py
3. **Quality Check**: lint_wrap.py, casefix.py
4. **Verification**: vcd2wavedrom2.py, update_fst_tracing.py
5. **Tool Compatibility**: sv_interface_flattener.py, axi_split_calculator.py
6. **Documentation**: md_to_docx.py, pytree.py

---

[Back to Readme](../../../README.md)

---
