# RTL Design Sherpa - FPGA Projects

This directory contains complete, ready-to-build FPGA projects demonstrating practical applications of the rtldesignsherpa common library modules.

---

## Project Organization

Projects are organized by FPGA development board:

```
projects/
├── components/        # Reusable RTL components / IP (see components/README.md)
│   ├── apbx_xbar/  bridge/  converters/  delta/  hive/
│   ├── memory-controllers/  misc/  rapids/  retro_legacy_blocks/  stream/
│   └── ...
├── NexysA7/           # Digilent Nexys A7-100T projects
│   ├── cdc_counter_display/       # CDC teaching demo
│   ├── timing_characterization/   # generic timing/fmax characterization
│   ├── stream_characterization/   # STREAM DMA on-chip characterization
│   ├── rapids_characterization/   # RAPIDS beats DMA on-chip characterization
│   └── ddr2-characterization/     # DDR2 controller on-chip characterization
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

#### [STREAM Characterization](NexysA7/stream_characterization/)

**On-chip DMA characterization of the STREAM engine (2×2 DMA × bridge matrix)**

- **Component:** [stream](components/dmas/stream/) — docs: [PRD](components/dmas/stream/PRD.md)
- **Report:** [findings](NexysA7/stream_characterization/docs/characterization_v1_findings.md) · sub-reports: [perf](NexysA7/stream_characterization/reports/perf/README.md), [area](NexysA7/stream_characterization/reports/area/README.md), [compression](NexysA7/stream_characterization/reports/compression/README.md)
- **Board:** Nexys A7-100T · UART host + on-chip pattern/CRC memory
- **Status:** ✅ Characterized (perf + area + compression sweeps)

---

#### [RAPIDS Characterization](NexysA7/rapids_characterization/)

**On-chip characterization of the split RAPIDS "beats" DMA (two wholly-separate src/snk engines)**

- **Component:** [rapids](components/dmas/rapids/) — docs: [PRD](components/dmas/rapids/PRD.md) · [spec](components/dmas/rapids/docs/)
- **Report:** [characterization findings](NexysA7/rapids_characterization/docs/rapids_characterization_findings.md) (regenerate the PDF with `NexysA7/rapids_characterization/docs/generate_pdf.sh`) · host flow: [flows-rapids-beats](NexysA7/rapids_characterization/flows-rapids-beats/)
- **Board:** Nexys A7-100T · timing-closed @ 100 MHz; both data paths CRC-validated on silicon (`make smoke` / `make suite`)
- **Status:** ✅ Characterized (split engines, golden-CRC suite 48/48 on hardware)

---

#### [DDR2 Characterization](NexysA7/ddr2-characterization/)

**On-chip characterization of the DDR2 memory controller**

- **Component:** [memory-controllers](components/memory-controllers/)
- **Report:** [README + docs](NexysA7/ddr2-characterization/) · [reports](NexysA7/ddr2-characterization/)
- **Board:** Nexys A7-100T (on-board DDR2)
- **Status:** 🟡 Active

---

#### [Timing Characterization](NexysA7/timing_characterization/)

**Generic timing / fmax characterization harness**

- **Report / docs:** [README + docs](NexysA7/timing_characterization/)
- **Board:** Nexys A7-100T
- **Status:** 🟡 Active

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
- [CocoTB Framework](../bin/TBClasses/) - Testbench infrastructure
- [Components Quick Status](components/PROJECT_QUICK_STATUS.md) - status of all components

### Component documentation

| Component | Status | Docs |
|-----------|--------|------|
| [converters](components/converters/) | Production Ready | [README](components/converters/README.md) |
| [apbx_xbar](components/apbx_xbar/) | Production Ready | [PRD](components/apbx_xbar/PRD.md) |
| [stream](components/dmas/stream/) | Active | [PRD](components/dmas/stream/PRD.md) · char: [report](NexysA7/stream_characterization/docs/characterization_v1_findings.md) |
| [rapids](components/dmas/rapids/) | Active | [PRD](components/dmas/rapids/PRD.md) · [spec](components/dmas/rapids/docs/) · char: [report](NexysA7/rapids_characterization/docs/rapids_characterization_findings.md) |
| [bridge](components/bridge/) | Active | [PRD](components/bridge/PRD.md) |
| [memory-controllers](components/memory-controllers/) | Active | [README](components/memory-controllers/README.md) · char: [ddr2](NexysA7/ddr2-characterization/) |
| [hive](components/hive/) | Spec | [PRD](components/hive/PRD.md) · [spec](components/hive/docs/hive_spec/) |
| [delta](components/delta/) | Spec | [PRD](components/delta/PRD.md) · [spec](components/delta/docs/delta_spec/) |
| [retro_legacy_blocks](components/retro_legacy_blocks/) | Active | [PRD](components/retro_legacy_blocks/PRD.md) |
| [misc](components/misc/) | — | [README](components/misc/README.md) |

### Characterization reports (Nexys A7-100T)

- [STREAM](NexysA7/stream_characterization/docs/characterization_v1_findings.md) — [perf](NexysA7/stream_characterization/reports/perf/README.md) · [area](NexysA7/stream_characterization/reports/area/README.md) · [compression](NexysA7/stream_characterization/reports/compression/README.md)
- [RAPIDS](NexysA7/rapids_characterization/docs/rapids_characterization_findings.md) — split src/snk engines, golden-CRC suite (48/48 on silicon)
- [DDR2](NexysA7/ddr2-characterization/) · [Timing](NexysA7/timing_characterization/)

---

**Last Updated:** 2026-07-04
**Maintainer:** RTL Design Sherpa Project
