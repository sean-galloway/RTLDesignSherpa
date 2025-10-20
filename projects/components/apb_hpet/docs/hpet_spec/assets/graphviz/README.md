# HPET Flow Diagrams - Graphviz

This directory contains Graphviz flowcharts for HPET software and operational flows.

## Files

| File | Description |
|------|-------------|
| **software_init.dot** | Software initialization sequence |
| **oneshot_timer.dot** | One-shot timer operation flow |
| **periodic_timer.dot** | Periodic timer operation flow |
| **interrupt_handling.dot** | Interrupt service routine flow |
| **timer_mode_switch.dot** | Switching between one-shot and periodic modes |
| **multi_timer_concurrent.dot** | Multiple timers running concurrently |
| **cdc_handshake.dot** | Clock domain crossing handshake protocol |
| **Makefile** | Build script to render all diagrams |

## Rendering Diagrams

### Option 1: Using Makefile (Recommended)

```bash
# Render all diagrams to PNG
make all

# Render all diagrams to SVG
make svg

# Render specific diagram
make software_init.png

# Clean all generated files
make clean
```

### Option 2: Manual Rendering

```bash
# Render to PNG
dot -Tpng software_init.dot -o software_init.png

# Render to SVG (scalable, better quality)
dot -Tsvg software_init.dot -o software_init.svg

# Render to PDF
dot -Tpdf software_init.dot -o software_init.pdf
```

### Option 3: Interactive Viewing

```bash
# Install xdot for interactive viewing
sudo apt-get install xdot  # Ubuntu/Debian
# or
brew install xdot  # macOS

# View interactively
xdot software_init.dot
```

### Option 4: Online Viewer

1. Copy the .dot file contents
2. Go to https://dreampuf.github.io/GraphvizOnline/
3. Paste and view

## Diagram Descriptions

### 1. Software Initialization (software_init.dot)

Shows the complete software initialization sequence:
- Disable HPET
- Reset counter
- Read capabilities
- Configure timers
- Enable HPET

**Use Case:** Understanding how to initialize HPET from software

### 2. One-Shot Timer (oneshot_timer.dot)

Detailed flow of one-shot timer operation:
- Timer enable
- Counter comparison
- Fire detection
- IRQ assertion
- Timer goes idle

**Use Case:** Understanding one-shot timer behavior

### 3. Periodic Timer (periodic_timer.dot)

Complete periodic timer operation:
- Timer enable
- Counter comparison
- Fire detection
- Auto-increment comparator
- Continuous operation

**Use Case:** Understanding periodic timer auto-reload

### 4. Interrupt Handling (interrupt_handling.dot)

ISR (Interrupt Service Routine) flow:
- Read STATUS register
- Check which timers fired
- Handle each timer
- Clear interrupts (W1C)
- Verify all cleared

**Use Case:** Implementing interrupt service routines

### 5. Timer Mode Switching (timer_mode_switch.dot)

Switching between one-shot and periodic modes:
- From one-shot → periodic
- From periodic → one-shot
- Critical: disable timer first
- Comparator meaning changes

**Use Case:** Dynamic timer reconfiguration

### 6. Multi-Timer Concurrent (multi_timer_concurrent.dot)

Multiple timers operating simultaneously:
- Timer 0: one-shot at 100
- Timer 1: periodic at 200, 400, 600...
- Timer 2: one-shot at 700
- Independent operation
- Shared counter

**Use Case:** Understanding concurrent timer behavior

### 7. CDC Handshake (cdc_handshake.dot)

Clock domain crossing protocol (CDC_ENABLE=1):
- APB clock domain
- HPET clock domain
- Handshake synchronization
- Latency impact (4-6 cycles)

**Use Case:** Understanding asynchronous clock operation

## Color Coding

The diagrams use consistent color coding:

- **Light Green**: Start/End states, successful operations
- **Light Blue**: Normal processing steps
- **Light Yellow**: Decision points, checks, waiting states
- **Light Cyan**: Configuration/setup steps
- **Light Coral**: Events (timer fires, errors)
- **Red/Orange**: Interrupts, critical states
- **White**: Wait cycles, idle states
- **Yellow Notes**: Important information, best practices

## Embedding in Documentation

### Markdown

```markdown
### Software Initialization Flow

![Software Init](assets/graphviz/software_init.png)

See [software_init.dot](assets/graphviz/software_init.dot) for details.
```

### HTML

```html
<h3>Software Initialization Flow</h3>
<img src="assets/graphviz/software_init.svg" alt="Software Init Flow">
```

### LaTeX

```latex
\begin{figure}
\includegraphics[width=\textwidth]{assets/graphviz/software_init.pdf}
\caption{HPET Software Initialization Flow}
\end{figure}
```

## Updating Diagrams

To modify flows:

1. Edit the .dot file in any text editor
2. Re-render: `dot -Tpng file.dot -o file.png`
3. Verify changes visually
4. Commit both .dot and generated image files

## Graphviz Syntax Tips

```dot
// Node styles
node [shape=box, style="rounded,filled", fillcolor=lightblue];

// Decision points
decision [label="Condition?", shape=diamond];

// Notes/annotations
note [label="Important info", shape=note, fillcolor=yellow];

// Edge labels
node1 -> node2 [label="Yes", style=dashed];

// Subgraphs (grouping)
subgraph cluster_name {
    label="Group Name";
    node1; node2;
}

// Rank (horizontal alignment)
{rank=same; node1; node2;}
```

## Dependencies

- **graphviz** package required
  - Ubuntu/Debian: `sudo apt-get install graphviz`
  - macOS: `brew install graphviz`
  - Windows: Download from https://graphviz.org/download/

## References

- **Graphviz Documentation**: https://graphviz.org/documentation/
- **DOT Language Guide**: https://graphviz.org/doc/info/lang.html
- **Node Shapes**: https://graphviz.org/doc/info/shapes.html
- **HPET PRD**: `../../PRD.md`
- **HPET CLAUDE.md**: `../../CLAUDE.md`
