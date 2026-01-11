# RAPIDS Beats MAS - Mermaid Diagrams

**Last Updated:** 2025-01-10

---

## Overview

This directory contains Mermaid diagram source files (.mmd) for the RAPIDS Beats MAS documentation.

## Rendering Diagrams

### Using Mermaid CLI

```bash
# Install mermaid-cli
npm install -g @mermaid-js/mermaid-cli

# Render single diagram
mmdc -i 01_rapids_beats_architecture.mmd -o 01_rapids_beats_architecture.png

# Render all diagrams
for f in *.mmd; do
    mmdc -i "$f" -o "${f%.mmd}.png"
done
```

### Using Online Editor

1. Visit [Mermaid Live Editor](https://mermaid.live/)
2. Paste .mmd file contents
3. Export as PNG/SVG

---

## File List

| File | Description | Used In |
|------|-------------|---------|
| `01_rapids_beats_architecture.mmd` | Top-level architecture | ch01/01_architecture.md |
| `02_scheduler_fsm.mmd` | Scheduler state machine | ch02/01_scheduler.md |
| `03_sink_data_path_block.mmd` | Sink path block diagram | ch03/03_sink_data_path.md |
| `04_source_data_path_block.mmd` | Source path block diagram | ch03/07_source_data_path.md |
| `05_virtual_fifo_concept.mmd` | Virtual FIFO explanation | ch02/05_beats_alloc_ctrl.md |
| `06_monbus_aggregation.mmd` | MonBus aggregation tree | ch04/03_monbus_interface_spec.md |

---

## Diagram Guidelines

1. **Theme:** Use light backgrounds for documentation
2. **Colors:** Use consistent color coding:
   - Green: Input/Fill interfaces
   - Blue: Control/Scheduler
   - Orange: Output/Drain interfaces
   - Pink: Memory interfaces
3. **Labels:** Keep labels concise but descriptive
4. **Direction:** Use TB (top-to-bottom) for hierarchy, LR (left-to-right) for flow

---
