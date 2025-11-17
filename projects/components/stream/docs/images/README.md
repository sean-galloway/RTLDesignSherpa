# STREAM Documentation Images

This directory contains PNG diagrams generated from Mermaid code blocks in the STREAM specification documentation.

## Generation

PNG files are automatically generated from Mermaid diagrams in markdown files using the conversion script:

```bash
cd /mnt/data/github/rtldesignsherpa/projects/components/stream/docs
python3 convert_mermaid_to_png.py
```

### Requirements

- Node.js and npm
- Mermaid CLI: `npm install -g @mermaid-js/mermaid-cli`

### Conversion Script

The `convert_mermaid_to_png.py` script:
1. Scans all markdown files in `stream_spec/ch02_blocks/`
2. Extracts Mermaid code blocks (` ```mermaid ... ``` `)
3. Converts each diagram to PNG using `mmdc` (Mermaid CLI)
4. Saves PNGs with descriptive filenames in this directory

### Filename Convention

PNGs are named: `{source_file}_L{line_number}.png`

Examples:
- `02_scheduler_L025.png` - Diagram from 02_scheduler.md at line 25
- `08_axi_read_engine_L024.png` - Diagram from 08_axi_read_engine.md at line 24

## Generated Files

| File | Source | Description |
|------|--------|-------------|
| `02_scheduler_L025.png` | 02_scheduler.md:25 | Scheduler block diagram |
| `02_scheduler_L284.png` | 02_scheduler.md:284 | Scheduler FSM state diagram |
| `05_sram_controller_L028.png` | 05_sram_controller.md:28 | Multi-channel SRAM architecture |
| `06_sram_controller_unit_L033.png` | 06_sram_controller_unit.md:33 | Three-component pipeline |
| `07_stream_alloc_ctrl_L063.png` | 07_stream_alloc_ctrl.md:63 | Allocation controller virtual FIFO |
| `08_axi_read_engine_L024.png` | 08_axi_read_engine.md:24 | AXI read engine architecture |
| `09_stream_drain_ctrl_L063.png` | 09_stream_drain_ctrl.md:63 | Drain controller virtual FIFO |
| `10_axi_write_engine_L025.png` | 10_axi_write_engine.md:25 | AXI write engine architecture |
| `11_scheduler_group_L027.png` | 11_scheduler_group.md:27 | Scheduler group integration |
| `12_scheduler_group_array_L028.png` | 12_scheduler_group_array.md:28 | 8-channel array architecture |

## PDF Generation

These PNG files are used during PDF generation to ensure diagrams render correctly in the final document.

## Maintenance

When markdown files are updated with new or modified Mermaid diagrams:

1. Re-run the conversion script
2. Commit updated PNG files to git
3. Update this README if new diagrams are added

## Image Specifications

- Format: PNG
- Width: 1200 pixels (default)
- Background: White
- DPI: Screen resolution (96 DPI)

For print-quality PDFs, images can be regenerated at higher resolution by editing `convert_mermaid_to_png.py` and changing the `width` parameter.
