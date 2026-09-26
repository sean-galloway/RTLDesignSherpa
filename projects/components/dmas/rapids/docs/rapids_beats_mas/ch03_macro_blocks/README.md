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

# Chapter 3: Macro Blocks Overview

**Last Updated:** 2025-01-10

---

## Macro Block Summary

Macro blocks integrate multiple FUB modules into larger functional units that form the complete RAPIDS "beats" architecture.

### Block Hierarchy

```
rapids_core_beats (Top Level)
├── beats_scheduler_group_array
│   └── beats_scheduler_group [8x]
│       ├── scheduler
│       └── descriptor_engine
│
├── sink_data_path (or sink_data_path_axis)
│   ├── snk_sram_controller
│   │   └── snk_sram_controller_unit [8x]
│   └── axi_write_engine
│
└── source_data_path (or source_data_path_axis)
    ├── src_sram_controller
    │   └── src_sram_controller_unit [8x]
    └── axi_read_engine
```

---

## Module Quick Reference

| Module | Section | Purpose |
|--------|---------|---------|
| `beats_scheduler_group` | 3.1 | Single-channel scheduler + descriptor engine |
| `beats_scheduler_group_array` | 3.2 | 8-channel scheduler array with shared AXI |
| `sink_data_path` | 3.3 | Network-to-memory transfer path |
| `sink_data_path_axis` | 3.4 | Sink path with AXIS interface |
| `snk_sram_controller_beats` | 3.5 | Sink SRAM wrapper over STREAM's sram_controller |
| `src_data_path_beats` | 3.6 | Memory-to-network transfer path |
| `src_data_path_axis_beats` | 3.7 | Source path with AXIS interface |
| `src_sram_controller_beats` | 3.8 | Source SRAM wrapper over STREAM's sram_controller |
| `rapids_core_beats` | 3.9 | Complete RAPIDS core integration |
| `rapids_regs` | 3.10 | Generated register block |
| `rapids_config_block` | 3.11 | Configuration distribution |
| `rapids_beats_top` | 3.12 | Top-level integration |

: Table 3.0.1: Macro Block Reference

---

## Chapter Contents

- [Beats Scheduler Group](01_beats_scheduler_group.md)
- [Beats Scheduler Group Array](02_beats_scheduler_group_array.md)
- [Sink Data Path](03_sink_data_path.md)
- [Sink Data Path AXIS](04_sink_data_path_axis.md)
- [Sink SRAM Controller](05_snk_sram_controller.md)
- [Source Data Path](06_source_data_path.md)
- [Source Data Path AXIS](07_source_data_path_axis.md)
- [Source SRAM Controller](08_src_sram_controller.md)
- [RAPIDS Core Beats](09_rapids_core_beats.md)
- [RAPIDS Registers](10_rapids_regs.md)
- [RAPIDS Config Block](11_rapids_config_block.md)
- [RAPIDS Beats Top](12_rapids_beats_top.md)

---

**Last Updated:** 2025-01-10
