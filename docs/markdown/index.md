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

# RTL Design Sherpa

*A comprehensive framework for modern RTL design using industry-standard practices and open-source tools*

## Overview

RTL Design Sherpa is a professional-grade hardware design framework that bridges the gap between academic learning and industry practice. Built entirely with open-source tools, it provides a complete ecosystem for RTL development, verification, and automation that rivals commercial solutions.

The framework emphasizes **practical industry workflows**, **comprehensive verification**, and **automated quality assurance** - the same standards used in professional IC design teams. Whether you're learning digital design or building production-ready IP, RTL Design Sherpa provides the tools and methodologies to create high-quality hardware.

## Core Philosophy

### Industry-Standard Practices
- **Automated Testing**: Every module includes comprehensive CocoTB test suites with regression automation
- **Code Quality**: Integrated linting, formatting, and style checking using Verible
- **Design Methodology**: Modern SystemVerilog with parameterized, reusable IP blocks
- **Documentation**: Comprehensive module documentation with timing diagrams and usage examples

### Open-Source Excellence
- **Complete Toolchain**: Built exclusively with free, open-source tools
- **Production Ready**: Code quality and practices match commercial IC design flows
- **Educational Value**: Learn industry methodologies without expensive EDA licenses
- **Community Driven**: Extensible framework designed for collaboration and learning

## Framework Components

### 📦 RTL IP Libraries

#### **[RTL Common Modules](RTLCommon/index.md)**
Fundamental building blocks for digital design:
- **Arithmetic**: Advanced adders (Brent-Kung, ripple), multipliers (Wallace, Dadda), dividers
- **Data Structures**: FIFOs, shift registers, counters, timers with comprehensive parameterization
- **Control Logic**: Arbiters, encoders, decoders, state machines
- **Signal Processing**: CRC engines, LFSR generators, data integrity checkers
- **Clock/Reset**: ICG modules, reset synchronizers, clock domain crossing utilities

*86+ modules with comprehensive documentation and test coverage*

#### **[RTL AMBA Protocol Suite](RTLAmba/index.md)**
Complete implementation of ARM AMBA protocols:
- **APB (Advanced Peripheral Bus)**: Masters, slaves, crossbars with full APB4/APB5 compliance
- **AXI4 (Full)**: High-performance memory-mapped interfaces with burst support
- **AXI4-Lite**: Register access interfaces with simplified protocol
- **AXI4-Stream**: High-throughput streaming data interfaces
- **Infrastructure**: Skid buffers, arbiters, protocol bridges, monitors

*66+ modules supporting complete AMBA-based system design*

### 🧪 Verification Framework

#### **[CocoTB Framework](CocoTBFramework/)**
Professional verification environment:
- **Protocol VIP**: AXI4, APB, AXI4-Stream verification IP with configurable drivers and monitors
- **Testbench Classes**: Reusable testbench components for common verification patterns
- **Scoreboards**: Transaction-level modeling and checking infrastructure
- **Coverage**: Functional coverage collection and analysis tools

#### **[Testing Tutorials](TestTutorial/index.md)**
Comprehensive guides for hardware verification:
- **Getting Started**: CocoTB fundamentals and basic test writing
- **Advanced Patterns**: Protocol compliance testing, constrained random verification
- **Automation**: Regression testing, CI/CD integration, automated reporting
- **Performance**: Bandwidth testing, latency analysis, stress testing

### 🛠️ Development Tools

#### **[Python Scripts and Automation](Scripts/index.md)**
Professional development and automation tools:
- **Code Generation**: Automated RTL generation for arithmetic circuits
- **Analysis Tools**: AXI transaction analyzers, interface flatteners, dependency checkers
- **Quality Assurance**: Integrated linting, formatting, and style checking
- **Documentation**: Wavedrom generation, UML diagram creation, markdown processing
- **Test Automation**: Regression runners, test list managers, result analyzers

*27+ tools supporting complete RTL development lifecycle*

## Key Features

### 🎯 **Production-Ready Quality**
- **Rigorous Testing**: Every module includes comprehensive test suites with multiple configurations
- **Code Standards**: Consistent coding style with automated lint checking and formatting
- **Documentation**: Professional-grade documentation with timing diagrams and usage examples
- **Performance Validated**: Modules tested across frequency ranges from 100MHz to 800MHz+

### ⚡ **Modern SystemVerilog**
- **Parameterized IP**: Highly configurable modules adaptable to various system requirements
- **Interface-Based Design**: Clean abstraction layers with SystemVerilog interfaces
- **Synthesis Optimized**: Code written for optimal synthesis results across different tools
- **Industry Compliance**: Full adherence to SystemVerilog standards and best practices

### 🔧 **Complete Toolchain Integration**
- **Verilator**: Fast simulation with VCD/FST waveform generation
- **Verible**: Professional-grade linting and code formatting
- **CocoTB**: Python-based verification with pytest integration
- **GTKWave**: Waveform viewing with pre-configured signal groups

### 📈 **Scalable Architecture**
- **Modular Design**: Individual IP blocks can be used independently or as system components
- **Hierarchical Organization**: Clear separation between common utilities and protocol-specific modules
- **Extensible Framework**: Well-defined interfaces for adding new modules and protocols
- **Multiple Abstraction Levels**: From basic building blocks to complete system-level components

## Getting Started

### Quick Setup
```bash
# Clone the repository
git clone https://github.com/sean-galloway/RTLDesignSherpa.git
cd RTLDesignSherpa

# Set up Python environment
python3 -m venv venv
source venv/bin/activate
pip install -r requirements.txt
source env_python

# Run your first test
cd val/unit_common/test_counter
pytest
```

### Development Environment
The framework is designed for Linux development (Ubuntu recommended) with these core tools:
- **Python 3.8+** with CocoTB and pytest
- **Verilator** for fast simulation
- **Verible** for code quality
- **GTKWave** for waveform analysis
- **VSCode** with SystemVerilog extensions

*Complete setup instructions available in the repository README*

## Use Cases

### 🎓 **Learning and Education**
- **Academic Projects**: Complete framework for digital design coursework
- **Industry Preparation**: Learn professional verification and design methodologies
- **Skill Development**: Hands-on experience with industry-standard tools and practices

### 🏢 **Professional Development**
- **IP Creation**: Foundation for developing reusable intellectual property
- **Prototyping**: Rapid development of digital designs with proven building blocks
- **Verification**: Professional-grade testbench development and automation
- **Tool Evaluation**: Compare open-source flows against commercial alternatives

### 🔬 **Research and Innovation**
- **Algorithm Implementation**: Hardware implementation of computational algorithms
- **Protocol Development**: Framework for developing new bus protocols and interfaces
- **Performance Analysis**: Tools for analyzing timing, area, and power characteristics
- **Academic Research**: Foundation for hardware architecture research projects

## Architecture Highlights

### RTL Module Statistics
- **Common Modules**: 86+ fundamental building blocks
- **AMBA Protocols**: 66+ protocol-specific components
- **Test Coverage**: 1000+ individual test cases
- **Documentation**: 150+ pages of comprehensive module documentation

### Performance Characteristics
| Component Type | Frequency Range | Typical Use |
|---------------|----------------|-------------|
| Basic Logic | 100-800 MHz | Counters, registers, simple arithmetic |
| Advanced Arithmetic | 200-600 MHz | Multipliers, dividers, CRC engines |
| Memory Interfaces | 300-500 MHz | AXI4 masters/slaves, memory controllers |
| Streaming Interfaces | 400-600 MHz | AXI4-Stream, high-throughput data paths |

### Quality Metrics
- **Code Coverage**: >95% line coverage across all modules
- **Functional Coverage**: Protocol compliance verification for all AMBA components
- **Regression Testing**: Automated nightly testing with >1000 test points
- **Documentation Coverage**: 100% of public modules documented with examples

## Contributing and Community

### Development Guidelines
- **Code Standards**: Follow project coding guidelines and use automated formatting
- **Testing Requirements**: All new modules must include comprehensive test suites
- **Documentation**: Include detailed module documentation with usage examples
- **Review Process**: All contributions reviewed for quality and industry best practices

### Learning Resources
- **[Testing Tutorial](TestTutorial/index.md)**: Complete guide to hardware verification
- **[Scripts Documentation](Scripts/index.md)**: Automation tools and development utilities
- **Module Examples**: Every RTL module includes usage examples and testbenches
- **Design Patterns**: Common design patterns documented with working examples

## Technical Foundation

RTL Design Sherpa is built on solid technical foundations inspired by industry-leading resources:

**Design Methodology**: Based on proven approaches from "Advanced FPGA Design" by Steve Kilts and "Synthesis of Arithmetic Circuits" by Deschamps, Bioul, and Sutter, but extended with modern SystemVerilog practices and comprehensive verification.

**Verification Approach**: Professional UVM-inspired methodologies adapted for CocoTB, providing the same verification rigor as commercial flows.

**Tool Integration**: Seamless integration between open-source tools, creating a cohesive development environment that rivals commercial EDA suites.

---

## Navigation

### 📚 **RTL IP Documentation**
- **[RTL Common Modules](RTLCommon/index.md)** - Fundamental digital design building blocks
- **[RTL AMBA Protocols](RTLAmba/index.md)** - Complete AMBA protocol implementation

### 🧪 **Verification and Testing**
- **[CocoTB Framework](CocoTBFramework/)** - Verification IP and testbench components
- **[Testing Tutorial](TestTutorial/index.md)** - Complete guide to hardware verification

### 🛠️ **Tools and Automation**
- **[Python Scripts](Scripts/index.md)** - Development tools and automation scripts

### 📖 **Additional Resources**
- **[Repository README](../../README.md)** - Setup instructions and getting started guide
- **[Contributing Guidelines](CONTRIBUTING.md)** - Development standards and contribution process

---

*RTL Design Sherpa: Bringing professional IC design practices to the open-source community*