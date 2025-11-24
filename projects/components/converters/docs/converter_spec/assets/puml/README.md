# Converters PlantUML FSM Diagrams

This directory contains PlantUML source files (.puml) and generated SVG diagrams for Converters FSM documentation.

## Files

### Source Files (.puml)

- **`axi4_to_apb_fsm.puml`** - APB state machine for AXI4-to-APB protocol converter

### Generated Images (.svg)

- **`axi4_to_apb_fsm.svg`** - FSM diagram for AXI4-to-APB converter

## FSM Overview

### AXI4-to-APB Converter FSM

**States:**
- **IDLE** - Wait for AXI4 transaction (AR or AW)
- **READ** - Process AXI4 AR transaction → APB read
- **WRITE** - Process AXI4 AW+W transaction → APB write

**Key Features:**
- Read priority over write when both pending
- Burst support (continues in READ/WRITE until all beats complete)
- APB protocol phases (Setup → Access → Wait)
- Error response handling (PSLVERR → BRESP/RRESP)

**Transitions:**
- IDLE → READ: AXI4 read request (ARVALID && ARREADY)
- IDLE → WRITE: AXI4 write request (AWVALID && AWREADY)
- READ → IDLE: APB read complete (PREADY && all beats done)
- WRITE → IDLE: APB write complete (PREADY && all beats done)
- Self-loops: Continue burst transfers

## Note on Other Converters

**Data width converters (axi_data_upsize, axi_data_dnsize) do not have FSMs:**
- They use simple counter-based control logic
- Upsize: Beat counter (0→N-1) to accumulate narrow beats
- Downsize: Output counter (0→N-1) to split wide beats
- No complex state transitions needed

**Only protocol converters have FSMs:**
- AXI4-to-APB: Protocol translation requires state machine
- PeakRDL adapter: Simple passthrough, no FSM needed

## Regenerating Diagrams

### Prerequisites

- PlantUML installed
- Java runtime (required by PlantUML)

### Install PlantUML

```bash
# Ubuntu/Debian
sudo apt install plantuml

# Or download JAR
wget https://github.com/plantuml/plantuml/releases/download/v1.2023.13/plantuml-1.2023.13.jar
```

### Generate SVG from PlantUML

```bash
# Using regeneration script
./regenerate_diagrams.sh

# Or manually using installed plantuml
plantuml -tsvg axi4_to_apb_fsm.puml

# Or using downloaded JAR
java -jar plantuml.jar -tsvg axi4_to_apb_fsm.puml

# Output: axi4_to_apb_fsm.svg
```

### Generate PNG (for legacy docs)

```bash
plantuml -tpng axi4_to_apb_fsm.puml
# Not recommended - use SVG instead for crisp vector graphics
```

### Generate PDF (for documentation)

```bash
plantuml -tpdf axi4_to_apb_fsm.puml
```

## FSM Style

**Colors:**
- Default state colors (light blue/yellow as per PlantUML defaults)
- Transition arrows with labels showing conditions

**Annotations:**
- Entry actions described in state boxes
- Transition conditions on arrows
- Notes explaining protocol sequences

**Format:**
- Standard UML state machine notation
- Clear state names matching RTL enumeration
- Transition guards showing trigger conditions

## Referenced In Documentation

These diagrams are referenced in:
- `ch03_protocol_converters/02_axi4_to_apb.md` - AXI4-to-APB converter chapter
- `converter_index.md` - Main specification index

## Adding New FSM Diagrams

If future converters include FSMs:

1. Create new .puml file:
   ```plantuml
   @startuml my_converter_fsm
   title My Converter FSM

   [*] --> IDLE
   IDLE --> ACTIVE : trigger
   ACTIVE --> IDLE : done

   @enduml
   ```

2. Generate SVG:
   ```bash
   ./regenerate_diagrams.sh
   ```

3. Link from documentation:
   ```markdown
   ![My Converter FSM](../assets/puml/my_converter_fsm.svg)
   ```

## Tools

**PlantUML Version:** Any recent version (tested with 1.2023+)

**Alternative Renderers:**
- Online: http://www.plantuml.com/plantuml/uml/ (paste .puml content)
- VS Code: Install "PlantUML" extension
- IntelliJ IDEA: Built-in PlantUML support

## Notes

- SVG files are version controlled for high-quality viewing
- Source .puml files are the authoritative source
- Regenerate SVGs after any .puml changes using `./regenerate_diagrams.sh`
- Keep FSM diagrams synchronized with RTL state definitions
- SVG provides crisp vector graphics at any zoom level (preferred over PNG)

---

**Last Updated:** 2025-10-26
**Maintainer:** RTL Design Sherpa Project
