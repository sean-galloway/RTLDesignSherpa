# RTL Design Sherpa - FPGA Projects

This directory contains complete, ready-to-build FPGA projects demonstrating practical applications of the rtldesignsherpa common library modules.

---

## Project Organization

Projects are organized by IP area (board targets live inside each harness):

```
projects/
├── components/        # Reusable RTL components / IP (see components/README.md)
│   ├── fabric-gen-ip/  dma-ip/  ecc-ip/  mem-ctrl-ip/
│   ├── noc-ip/  compute-eng-ip/  cache-ip/
│   ├── utility-ip/  retro_legacy_blocks/
│   └── ...
├── fpga-systems/      # Board harnesses, grouped by the same IP areas
│   ├── misc-ip/cdc_counter_display/   # CDC teaching demo (Nexys A7)
│   ├── NexysA7/pumice/                # DDR2 characterization (Nexys A7)
│   ├── Genesys2/bch/  Genesys2/reed-solomon/   # ECC loopbacks (Genesys 2)
│   ├── Genesys2/stream/  Genesys2/rapids/  Genesys2/rapids_beats/
│   └── ...
└── asic-trials/timing_characterization/
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

#### [CDC Counter Display](fpga-systems/misc-ip/cdc_counter_display/)

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
- **Status:** Complete and tested

**Quick Start:**
```bash
cd misc-ip/cdc_counter_display
make sim      # Run simulation
make build    # Build bitstream
make program  # Program FPGA
```

---

#### [RAPIDS Characterization](fpga-systems/Genesys2/rapids_beats/)

**On-chip characterization of the split RAPIDS "beats" DMA (two wholly-separate src/snk engines)**

- **Component:** [rapids](components/dma-ip/rapids/) — docs: [PRD](components/dma-ip/rapids/PRD.md) · [spec](components/dma-ip/rapids/docs/)
- **Report:** [characterization findings](fpga-systems/Genesys2/rapids_beats/docs/rapids_beats_findings.md) (regenerate the PDF with `fpga-systems/Genesys2/rapids_beats/docs/generate_pdf.sh`) · host flow: [flows-rapids-beats](fpga-systems/Genesys2/rapids_beats/flows-rapids-beats/)
- **Board:** Nexys A7-100T · timing-closed @ 100 MHz; both data paths CRC-validated on silicon (`make smoke` / `make suite`)
- **Status:** Characterized (split engines, golden-CRC suite 48/48 on hardware)

---

#### [DDR2 Characterization](fpga-systems/NexysA7/pumice/ddr2-characterization/)

**On-chip characterization of the DDR2 memory controller**

- **Component:** [mem-ctrl-ip](components/mem-ctrl-ip/)
- **Report:** [README + docs](fpga-systems/NexysA7/pumice/ddr2-characterization/) · [reports](fpga-systems/NexysA7/pumice/ddr2-characterization/)
- **Board:** Nexys A7-100T (on-board DDR2)
- **Status:** Active

---

#### [Timing Characterization](asic-trials/timing_characterization/)

**Generic timing / fmax characterization harness**

- **Report / docs:** [README + docs](asic-trials/timing_characterization/)
- **Board:** Nexys A7-100T
- **Status:** Active

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
│   └── build_all.tcl
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
- [Components index](components/index.md) - component list with status; live work items in [vault/Tasks/INDEX.md](../vault/Tasks/INDEX.md)

### Component documentation

| Component | Status | Docs |
|-----------|--------|------|
| [converters](components/utility-ip/converters/) | Production Ready | [README](components/utility-ip/converters/README.md) |
| [apbx_xbar](components/fabric-gen-ip/apbx-xbar/) | Production Ready | [PRD](components/fabric-gen-ip/apbx-xbar/PRD.md) |
| [stream](components/dma-ip/stream/) | Active | [PRD](components/dma-ip/stream/PRD.md) |
| [rapids](components/dma-ip/rapids/) | Active | [PRD](components/dma-ip/rapids/PRD.md) · [spec](components/dma-ip/rapids/docs/) · char: [report](fpga-systems/Genesys2/rapids_beats/docs/rapids_beats_findings.md) |
| [bridge](components/fabric-gen-ip/bridge/) | Active | [PRD](components/fabric-gen-ip/bridge/PRD.md) |
| [mem-ctrl-ip](components/mem-ctrl-ip/) | Active | [README](components/mem-ctrl-ip/README.md) · char: [ddr2](fpga-systems/NexysA7/pumice/ddr2-characterization/) |
| [hive](components/compute-eng-ip/hive/) | Retired 2026-09-27 | [PRD](components/compute-eng-ip/hive/PRD.md) · [spec](components/compute-eng-ip/hive/docs/hive_spec/) |
| [delta](components/noc-ip/delta/) | Retired 2026-09-27 | [PRD](components/noc-ip/delta/PRD.md) · [spec](components/noc-ip/delta/docs/delta_spec/) |
| [retro_legacy_blocks](components/retro_legacy_blocks/) | Active | [PRD](components/retro_legacy_blocks/PRD.md) |
| [misc](components/utility-ip/misc/) | — | [README](components/utility-ip/misc/README.md) |

### Characterization reports (Nexys A7-100T)

- [RAPIDS](fpga-systems/Genesys2/rapids_beats/docs/rapids_beats_findings.md) — split src/snk engines, golden-CRC suite (48/48 on silicon)
- [DDR2](fpga-systems/NexysA7/pumice/ddr2-characterization/) · [Timing](asic-trials/timing_characterization/)

---

**Last Updated:** 2026-07-04
**Maintainer:** RTL Design Sherpa Project
