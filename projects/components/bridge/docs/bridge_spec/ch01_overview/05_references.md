# 1.5 References

This section provides references to external specifications, tools, and related documentation that support the Bridge component.

## Specifications and Standards

### AMBA AXI4 Specification
**ARM IHI 0022E (ID022613)**  
AMBA AXI and ACE Protocol Specification AXI3, AXI4, and AXI4-Lite, ACE and ACE-Lite  
Publisher: ARM Limited  
URL: https://developer.arm.com/documentation/ihi0022/latest/

This is the authoritative specification for the AXI4 protocol implemented by the Bridge. Key sections:
- Chapter A2: Signal Descriptions
- Chapter A3: Single Interface Requirements
- Chapter A5: Transaction Attributes
- Chapter A7: Interconnect and Ordering

### AMBA APB Specification
**ARM IHI 0024C**  
AMBA APB Protocol Specification  
Publisher: ARM Limited  
URL: https://developer.arm.com/documentation/ihi0024/latest/

Referenced for APB slave conversion functionality.

### SystemVerilog IEEE Standard
**IEEE Std 1800-2017**  
IEEE Standard for SystemVerilog - Unified Hardware Design, Specification, and Verification Language  
Publisher: IEEE

The Bridge RTL is generated as SystemVerilog IEEE 1800-2017 compliant code.

## Tools and Frameworks

### Verilator
Open-source SystemVerilog simulator and lint tool  
URL: https://www.veripool.org/verilator/  
Documentation: https://verilator.org/guide/latest/

Verilator Version: 5.006 or later recommended  
Used for: RTL simulation, lint checking

### CocoTB
Coroutine-based cosimulation testbench environment for verifying VHDL and SystemVerilog RTL  
URL: https://www.cocotb.org/  
Documentation: https://docs.cocotb.org/  
GitHub: https://github.com/cocotb/cocotb

CocoTB Version: 1.8.0 or later  
Used for: Bridge verification framework, test development

### Python
Python Programming Language  
URL: https://www.python.org/  
Documentation: https://docs.python.org/3/

Python Version: 3.8 or later required  
Used for: Bridge generator, test infrastructure, automation scripts

### Make
GNU Make - Build automation tool  
URL: https://www.gnu.org/software/make/  
Documentation: https://www.gnu.org/software/make/manual/

Used for: Build system, test execution, automation

### TOML
Tom's Obvious Minimal Language  
URL: https://toml.io/  
Specification: https://toml.io/en/v1.0.0

Configuration file format for Bridge specifications

### Jinja2
Template engine for Python  
URL: https://palletsprojects.com/p/jinja/  
Documentation: https://jinja.palletsprojects.com/

Jinja2 Version: 3.0 or later  
Used for: RTL template generation

## Related RTL Components

### Stream Components
**Location**: `projects/components/stream/`  
**Documentation**: `projects/components/stream/docs/stream_spec/`

Stream protocol components that may be integrated with Bridge masters/slaves for data streaming applications.

### Common Utilities
**Location**: `projects/components/common/`

Shared RTL utilities used across multiple projects, including:
- FIFO implementations
- Clock domain crossing modules
- Synchronizers
- Standard interfaces

### AMBA Components
**Location**: `projects/components/amba/`

Additional AMBA protocol components that complement the Bridge:
- AXI monitors
- AXI protocol checkers
- APB components

## Project Documentation

### Global Requirements
**Location**: `GLOBAL_REQUIREMENTS.md`

Project-wide coding standards, naming conventions, and design rules.

### Testing Guide
**Location**: `TESTING.md`

Project-level testing methodology and infrastructure documentation.

### Product Requirements Document
**Location**: `PRD.md`

High-level product requirements for the RTL Design Sherpa project.

## Design and Verification Resources

### AXI4 Transaction Ordering
ARM Developer: Understanding AXI4 Transaction Ordering  
Useful for understanding ordering requirements in multi-master systems.

### CocoTB Verification Guide
CocoTB Documentation: Writing Testbenches  
https://docs.cocotb.org/en/stable/writing_testbenches.html

Essential reading for developing Bridge test cases.

### Python Async/Await
Python Documentation: Coroutines and Tasks  
https://docs.python.org/3/library/asyncio-task.html

Background on async programming model used in CocoTB tests.

## FPGA Vendor Tools

### Xilinx Vivado
Xilinx Vivado Design Suite  
URL: https://www.xilinx.com/products/design-tools/vivado.html

For synthesis, implementation, and timing analysis on Xilinx FPGAs.

Relevant constraint formats:
- XDC (Xilinx Design Constraints)
- SDC (Synopsys Design Constraints)

### Intel Quartus
Intel Quartus Prime  
URL: https://www.intel.com/content/www/us/en/products/details/fpga/development-tools/quartus-prime.html

For synthesis and implementation on Intel FPGAs.

## Open Source Hardware

### LibreCores
Collaborative platform for open source digital hardware designs  
URL: https://www.librecores.org/

Community resource for reusable IP cores and design methodologies.

### FOSSi Foundation
Free and Open Source Silicon Foundation  
URL: https://www.fossi-foundation.org/

Promotes free and open digital hardware design.

## Academic and Industry Papers

### High-Performance Interconnects
**"On-Chip Networks" by Natalie Enright Jerger and Li-Shiuan Peh**  
Morgan & Claypool Publishers (2009)  
Comprehensive coverage of NoC architectures and interconnect design.

### AXI Protocol Analysis
Various whitepapers available from ARM and FPGA vendors discussing:
- AXI4 performance optimization
- Width conversion techniques
- Clock domain crossing strategies
- Arbitration algorithms

## Conference Proceedings

### Design Automation Conference (DAC)
Annual conference covering EDA tools and methodologies  
URL: https://www.dac.com/

### International Conference on Computer-Aided Design (ICCAD)
Research in design automation and verification  
URL: https://iccad.com/

## Online Communities and Forums

### Stack Overflow - Verilog/SystemVerilog
Questions and answers on HDL design  
Tag: `[systemverilog]`, `[verilog]`, `[axi]`

### Reddit - r/FPGA
Community discussion on FPGA design and development  
URL: https://www.reddit.com/r/FPGA/

### Verification Academy
Mentor Graphics verification training and resources  
URL: https://verificationacademy.com/

## Version Control

### Git
Distributed version control system  
URL: https://git-scm.com/  
Documentation: https://git-scm.com/doc

Project uses Git for source control and collaboration.

## Documentation Tools

### Markdown
Lightweight markup language  
Specification: https://commonmark.org/

Used for all Bridge documentation files.

### Pandoc
Universal document converter  
URL: https://pandoc.org/

Recommended tool for converting Markdown to PDF for final documentation deliverables.

### Graphviz
Graph visualization software  
URL: https://graphviz.org/

For generating architecture diagrams (future enhancement).

### Mermaid
JavaScript-based diagramming and charting tool  
URL: https://mermaid.js.org/

For generating diagrams in Markdown (future enhancement).

## Bridge-Specific References

### Generator Architecture
**Location**: Appendix A - Generator Deep Dive  
Detailed documentation on the Python-based RTL generation system.

### Verification Framework
**Location**: Chapter 5 - Verification  
Comprehensive guide to the CocoTB-based test suite.

### Configuration Examples
**Location**: `projects/components/bridge/configs/`  
Sample TOML/CSV configuration files for various Bridge topologies.

### Test Cases
**Location**: `val/bridge/`  
Complete set of verification tests with documentation.

## Errata and Updates

For the latest updates, bug fixes, and errata:

**Project Repository**: Check commit history and issue tracker  
**Internal Documentation**: Refer to release notes for version-specific changes

---

## Document Revision History

This references section is maintained as part of the Bridge MAS documentation. For questions or suggestions regarding additional references, consult the project maintainers.

**Note**: External URLs and specifications are subject to change. If a link is broken, consult the publisher's main website or use a web search engine to locate updated resources.
