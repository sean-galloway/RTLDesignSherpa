# STREAM Mermaid Diagrams

This directory contains Mermaid diagram source files (.mmd) and their generated PNG images.

**Key principle:** Source and generated files stay together in the same directory.

## Directory Contents

Each diagram has two files:
- **Source:** `{diagram_id}.mmd` - Editable Mermaid source
- **Generated:** `{diagram_id}.png` - PNG for PDF rendering

Example:
```
08_axi_read_engine_block.mmd   ← Edit this
08_axi_read_engine_L034.png   ← Auto-generated from .mmd
```

## Workflow

### Creating/Editing Diagrams

1. **Edit the .mmd source file:**
   ```bash
   vim 08_axi_read_engine_block.mmd
   ```

2. **Regenerate PNG:**
   ```bash
   cd /mnt/data/github/rtldesignsherpa/projects/components/stream/docs/stream_spec/assets/mermaid
   mmdc -i 08_axi_read_engine_block.mmd -o 08_axi_read_engine_L034.png -w 1200 -b white --quiet
   ```

3. **Commit both files:**
   ```bash
   git add 08_axi_read_engine_block.mmd 08_axi_read_engine_L034.png
   git commit -m "Update AXI read engine diagram"
   ```

### Bulk Regeneration

To regenerate ALL diagrams:

```bash
cd /mnt/data/github/rtldesignsherpa/projects/components/stream/docs/stream_spec/assets/mermaid

for mmd in *.mmd; do
    base="${mmd%.mmd}"
    mmdc -i "$mmd" -o "${base}.png" -w 1200 -b white --quiet
    echo "Generated ${base}.png"
done
```

## Markdown References

Markdown files reference diagrams like this:

```markdown
![Diagram](../assets/mermaid/08_axi_read_engine_L034.svg)

**Source:** [08_axi_read_engine_block.mmd](../assets/mermaid/08_axi_read_engine_block.mmd)
```

This provides:
- **PNG** for immediate viewing and PDF generation
- **Link to source** for future editing

## File Naming Convention

Format: `{document}_{line_number}.{ext}`

Examples:
- `02_scheduler_block.mmd` - Diagram from 02_scheduler.md at line 35
- `08_axi_read_engine_block.mmd` - Diagram from 08_axi_read_engine.md at line 34

The line number helps track which diagram came from which location in the original markdown.

## Current Files

| Diagram ID | Source Doc | Description |
|------------|------------|-------------|
| `02_apbtodescr_L020` | 02_apbtodescr.md:20 | APB to Descriptor block diagram |
| `02_apbtodescr_L120` | 02_apbtodescr.md:120 | APB to Descriptor FSM |
| `02_scheduler_L035` | 02_scheduler.md:35 | Scheduler block diagram |
| `02_scheduler_L301` | 02_scheduler.md:301 | Scheduler FSM state diagram |
| `05_sram_controller_L038` | 05_sram_controller.md:38 | Multi-channel SRAM architecture |
| `06_sram_controller_unit_L043` | 06_sram_controller_unit.md:43 | Three-component pipeline |
| `06_stream_latency_bridge_L030` | 06_stream_latency_bridge.md:30 | Latency bridge block diagram |
| `07_stream_alloc_ctrl_L073` | 07_stream_alloc_ctrl.md:73 | Allocation controller virtual FIFO |
| `08_axi_read_engine_L034` | 08_axi_read_engine.md:34 | AXI read engine architecture |
| `09_sram_controller_L030` | 09_sram_controller.md:30` | SRAM controller architecture |
| `09_stream_drain_ctrl_L073` | 09_stream_drain_ctrl.md:73 | Drain controller virtual FIFO |
| `10_axi_write_engine_L051` | 10_axi_write_engine.md:51 | AXI write engine architecture |
| `11_scheduler_group_L037` | 11_scheduler_group.md:37 | Scheduler group integration |
| `12_scheduler_group_array_L038` | 12_scheduler_group_array.md:38 | 8-channel array architecture |

## Requirements

- **Mermaid CLI:** `npm install -g @mermaid-js/mermaid-cli`
- **Node.js:** v14 or later

## Troubleshooting

**Parse errors:**
- Escape special characters in labels: use `"label (a, b)"` not `{a, b}`
- Test at: https://mermaid.live/

**PNG not rendering:**
- Check .mmd syntax first
- Increase timeout: `mmdc -i diagram.mmd -o diagram.png --puppeteerConfigFile /tmp/puppeteer-config.json`

**Missing diagrams:**
- Check markdown file for references
- Line numbers may have shifted - verify source

## History

- **2025-11-21:** Reorganized structure
  - Moved PNG files from `../images/` to this directory
  - Source (.mmd) and generated (.svg) now colocated
  - Updated all markdown references
  - Removed commented Mermaid blocks from markdown files

---

**Last Updated:** 2025-11-21
**Maintained By:** STREAM Documentation Team
