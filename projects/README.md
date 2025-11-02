# RTL Design Sherpa - FPGA Projects

This directory contains complete, ready-to-build FPGA projects demonstrating practical applications of the rtldesignsherpa common library modules.

---

## Project Organization

Projects are organized by FPGA development board:

```
projects/
├── NexysA7/           # Digilent Nexys A7 projects
│   └── cdc_counter_display/
└── (future boards)/
```

Each project includes:
- Complete RTL design
- Constraints files (.xdc)
- Vivado TCL build scripts
- CocoTB simulation testbench
- Comprehensive documentation
- Makefile for convenience

---

## Available Projects

### Nexys A7

#### [CDC Counter Display](NexysA7/cdc_counter_display/)

**Educational demonstration of Clock Domain Crossing (CDC)**

- **Description:** Debounced button counter with pulse-based CDC handshake to 7-segment display
- **Clock Domains:** 2 independent (button @ 10Hz, display @ 1kHz)
- **Features:**
  - Button debouncing
  - 8-bit hex counter (00-FF)
  - Safe CDC using sync_pulse
  - Dual 7-segment display
  - Visual heartbeat LEDs
- **Educational Value:** Production-quality CDC techniques, timing constraints, metastability analysis
- **Build Time:** ~5-10 minutes
- **Status:** ✅ Complete and tested

**Quick Start:**
```bash
cd NexysA7/cdc_counter_display
make sim      # Run simulation
make build    # Build bitstream
make program  # Program FPGA
```

---

## Quick Reference

### Prerequisites

**Software:**
- Xilinx Vivado 2020.2 or newer
- Python 3.8+ with CocoTB and pytest
- Verilator (optional, for linting)

**Hardware:**
- Supported FPGA development board
- USB programming cable

### General Workflow

All projects follow the same workflow:

1. **Simulate** - Verify design before synthesis
   ```bash
   make sim
   ```

2. **Build** - Generate bitstream
   ```bash
   make build
   ```

3. **Program** - Load onto FPGA
   ```bash
   make program
   ```

4. **Test** - Verify on hardware

### Project Structure Template

Each project follows this structure:

```
project_name/
├── rtl/                 # RTL design sources
│   └── top.sv          # Top-level module
├── constraints/         # Timing and pin constraints
│   └── board.xdc       # Constraints file
├── tcl/                 # Vivado TCL scripts
│   ├── create_project.tcl
│   ├── build_all.tcl
│   └── program_fpga.tcl
├── sim/                 # CocoTB simulation
│   └── test_*.py       # Testbench
├── docs/                # Documentation
│   ├── README.md       # Project guide
│   └── *.md            # Additional docs
├── Makefile             # Build automation
└── README.md            # Project README
```

---

## Design Philosophy

All projects demonstrate:

1. **Module Reuse** - Leverage rtldesignsherpa common library
2. **Best Practices** - Industry-standard coding style
3. **Education First** - Extensive documentation and comments
4. **Simulation** - CocoTB testbenches for verification
5. **Automation** - Scripted builds (no manual clicking)
6. **Portability** - Clean separation of design and constraints

---

## Future Projects

Planned additions:

### Nexys A7
- [ ] AXI4-Lite peripheral example
- [ ] VGA pattern generator
- [ ] UART echo with FIFO
- [ ] Multi-clock FIFO demonstration
- [ ] PWM motor controller

### Other Boards
- [ ] Arty A7 projects
- [ ] Basys 3 educational examples
- [ ] PYNQ-Z2 (PS-PL integration)

---

## Contributing

When adding new projects:

1. Follow the project structure template
2. Include comprehensive documentation
3. Provide CocoTB simulation
4. Test on actual hardware
5. Document resource usage and timing results

---

## Support

- **Documentation:** See individual project READMEs
- **Issues:** Open issue in rtldesignsherpa repository
- **Questions:** Refer to board-specific documentation

---

## Related Documentation

- [rtldesignsherpa README](../README.md) - Repository overview
- [Common Library Guide](../rtl/common/CLAUDE.md) - Module reference
- [CocoTB Framework](../bin/CocoTBFramework/README.md) - Testbench infrastructure

---

**Last Updated:** 2025-10-15
**Maintainer:** RTL Design Sherpa Project
