# User Guides and How-Tos

**Purpose:** Practical guides for using RTL Design Sherpa framework and tools

---

## Available Guides

### [AXI_Monitor_Configuration_Guide.md](AXI_Monitor_Configuration_Guide.md)
**What:** How to configure AXI monitors correctly
**When to use:** Setting up AXI4/AXI4-Lite monitoring in your testbench
**Key topics:**
- Packet type configuration (`cfg_*_enable` signals)
- Avoiding monitor bus congestion
- Separate test configurations for different packet types
- Debug strategies when monitors fail

**Critical warning:** Never enable `cfg_compl_enable` and `cfg_perf_enable` together - causes packet congestion

---

### [VERIFICATION_ARCHITECTURE_GUIDE.md](VERIFICATION_ARCHITECTURE_GUIDE.md)
**What:** Comprehensive verification methodology and best practices
**When to use:** Understanding the testbench architecture, writing new tests
**Key topics:**
- CocoTB framework structure
- Testbench components (BFMs, monitors, scoreboards)
- Test levels (minimal, basic, full, protocol)
- Coverage strategies
- Common verification patterns

**Start here if:** You're new to the verification framework

---

### [descriptor_engine_waveform_guide.md](descriptor_engine_waveform_guide.md)
**What:** Debugging descriptor engine using waveforms
**When to use:** Troubleshooting MIOP descriptor processing issues
**Key topics:**
- Descriptor engine state machine signals
- Waveform patterns for normal operation
- Identifying common failure modes
- VCD dump analysis

---

### [Wavedrom_AutoBind_Guide.md](Wavedrom_AutoBind_Guide.md) → [Link to markdown/](../markdown/CocoTBFramework/components/wavedrom/wavedrom_auto_binding.md)
**What:** Using WaveDrom automatic signal binding for documentation
**When to use:** Generating timing diagrams from simulations
**Key topics:**
- FieldConfig auto-binding setup
- Signal capture and waveform generation
- WaveDrom JSON generation
- Integration with test framework

**Note:** Symlink to main documentation - see `markdown/CocoTBFramework/components/wavedrom/`

---

## Quick Navigation

**Looking for design specs?** See [../design/](../design/)
**Looking for experimental work?** See [../investigations/](../investigations/)
**Looking for RTL/framework reference?** See [../markdown/](../markdown/)
**Back to main docs:** See [../README.md](../README.md)

---

**Maintained by:** RTL Design Sherpa Contributors
**Last Updated:** 2025-10-17
