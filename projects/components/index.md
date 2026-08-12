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

# RTL Design Sherpa - Production Components Index

**Last Updated:** 2025-10-25

---

## Overview

This directory contains production-ready and in-development component projects for RTL Design Sherpa. Each component has complete documentation, verification, and integration support.

**For detailed component documentation**, see [docs/markdown/projects/index.md](../../docs/markdown/projects/index.md)

---

## Component List

| Component | Status | Location | Documentation |
|-----------|--------|----------|---------------|
| **Retro Legacy Blocks (HPET, PIT, ...)** | ✅ Production | [retro_legacy_blocks/](retro_legacy_blocks/) | [HPET Specification](retro_legacy_blocks/docs/hpet_mas/hpet_mas_index.md) |
| **APB Crossbar** | ✅ Production | [apbx_xbar/](apbx_xbar/) | [Specification](apbx_xbar/docs/apbx_xbar_mas/apbx_xbar_mas_index.md) |
| **STREAM** | ✅ Production | [stream/](dmas/stream/) | [Specification](dmas/stream/docs/stream_mas/stream_index.md) |
| **RAPIDS** | 🟢 Functional | [rapids/](dmas/rapids/) | [Specification](dmas/rapids/docs/rapids_beats_mas/rapids_beats_mas_index.md) |
| **Bridge** | 🟡 Development | [bridge/](bridge/) | See [bridge/docs/](bridge/docs/) |
| **Converters** | 🟡 Development | [converters/](converters/) | See [converters/docs/](converters/docs/) |
| **Delta** | 🟡 Development | [delta/](delta/) | [Specification](delta/docs/delta_spec/delta_index.md) |
| **Hive** | 🟡 Development | [hive/](hive/) | [Specification](hive/docs/hive_spec/hive_index.md) |

---

## Quick Links

### By Category

**Timing and Control:**
- [Retro Legacy Blocks](retro_legacy_blocks/) - HPET, 8254 PIT, and other legacy timers/peripherals (absorbed the old apb4_hpet)

**Interconnect:**
- [APB Crossbar](apbx_xbar/) - MxN APB interconnect

**DMA and Data Transfer:**
- [STREAM](dmas/stream/) - Tutorial DMA engine
- [RAPIDS](dmas/rapids/) - Advanced DMA with network

**Integration:**
- [Bridge](bridge/) - Protocol bridges
- [Converters](converters/) - Protocol converters

**Other:**
- [Delta](delta/) - Component description pending
- [Hive](hive/) - Component description pending

---

## Documentation Structure

Each component follows this standard structure:

```
{component}/
├── rtl/                    # RTL source code
│   ├── {name}_fub/         # Functional unit blocks
│   ├── {name}_macro/       # Top-level integration
│   └── includes/           # Package definitions
├── dv/                     # Design verification
│   ├── tests/              # Test runners
│   ├── tbclasses/          # Testbench classes
│   └── components/         # BFMs (if needed)
├── docs/                   # Component documentation
│   ├── {name}_spec/        # Detailed specification
│   └── IMPLEMENTATION_STATUS.md
├── bin/                    # Component-specific scripts
├── known_issues/           # Issue tracking
├── PRD.md                  # Product requirements
├── CLAUDE.md               # AI assistance guide
├── TASKS.md                # Work tracking
└── README.md               # Quick start
```

---

## Status Legend

- ✅ **Production Ready** - Complete, verified, ready for integration
- 🟢 **Functional** - Working, test cleanup/refinement ongoing
- 🟡 **In Development** - Active development, partial functionality
- 🔴 **Planned** - Design phase, not yet implemented

---

## Project-Level Resources

### Documentation
- **[Project README](README.md)** - Overview and getting started
- **[Project PRD](PRD.md)** - Requirements and goals
- **[Project Status](PROJECT_STATUS.md)** - Current status
- **[Project CLAUDE Guide](CLAUDE.md)** - AI assistance
- **[Makefile Guide](MAKEFILE_GUIDE.md)** - Build system
- **[Makefile Hierarchy](MAKEFILE_HIERARCHY.md)** - Build organization

### Testing
- **[Makefile](Makefile)** - Central build and test control
- Run all component tests: `make test`
- Individual component: `make test-{component}`

---

## For More Information

- **Detailed Component Documentation:** [docs/markdown/projects/index.md](../../docs/markdown/projects/index.md)
- **RTL Building Blocks:** [rtl/common/](../../rtl/common/) and [rtl/amba/](../../rtl/amba/)
- **Main Repository Guide:** [Root README](../../README.md)

---

**Maintained By:** RTL Design Sherpa Project
**Last Review:** 2025-10-25
