# RTLCommon Block Diagram Generation Plan

## Overview

This plan outlines the approach for generating Mermaid block diagrams for the 56 RTLCommon markdown files that currently lack visual architecture diagrams.

**Important:** Diagrams will be stored as external SVG files and referenced via markdown image syntax to ensure PDF compatibility.

## Current Status

- **Total markdown files:** 76
- **Files WITH diagrams:** 18 (24%) - ASCII art in code blocks
- **Files WITHOUT diagrams:** 56 (74%, excluding index.md)
- **Target location:** `/mnt/data/github/rtldesignsherpa/docs/markdown/assets/RTLCommon/`

## Output Format

### SVG Image References (PDF Compatible)
```markdown
## Architecture

### Block Diagram

![arbiter_round_robin Block Diagram](../assets/RTLCommon/arbiter_round_robin.svg)
```

### File Organization
```
docs/markdown/
├── RTLCommon/
│   ├── arbiter_round_robin.md      # References ../assets/RTLCommon/arbiter_round_robin.svg
│   └── ...
└── assets/
    └── RTLCommon/
        ├── arbiter_round_robin.mmd  # Mermaid source
        ├── arbiter_round_robin.svg  # Rendered SVG
        └── ...
```

## Files Requiring Diagrams (Organized by Category)

### Category 1: Arbiters (4 files)
| File | Module | Complexity | Priority |
|------|--------|------------|----------|
| arbiter_round_robin.md | arbiter_round_robin | Medium | High |
| arbiter_round_robin_simple.md | arbiter_round_robin_simple | Low | High |
| arbiter_round_robin_weighted.md | arbiter_round_robin_weighted | Medium | High |
| arbiter_priority_encoder.md | arbiter_priority_encoder | Low | High |

### Category 2: Counters (7 files)
| File | Module | Complexity | Priority |
|------|--------|------------|----------|
| counter.md | counter | Low | Medium |
| counter_bin.md | counter_bin | Low | Medium |
| counter_bin_load.md | counter_bin_load | Low | Medium |
| counter_bingray.md | counter_bingray | Medium | Medium |
| counter_freq_invariant.md | counter_freq_invariant | Medium | High |
| counter_johnson.md | counter_johnson | Low | Medium |
| counter_ring.md | counter_ring | Low | Medium |

### Category 3: Data Integrity (7 files)
| File | Module | Complexity | Priority |
|------|--------|------------|----------|
| dataint_checksum.md | dataint_checksum | Medium | Medium |
| dataint_crc.md | dataint_crc | High | High |
| dataint_crc_xor_shift.md | dataint_crc_xor_shift | Medium | Medium |
| dataint_crc_xor_shift_cascade.md | dataint_crc_xor_shift_cascade | Medium | Medium |
| dataint_ecc_hamming_encode_secded.md | dataint_ecc_hamming_encode_secded | High | High |
| dataint_ecc_hamming_decode_secded.md | dataint_ecc_hamming_decode_secded | High | High |
| dataint_parity.md | dataint_parity | Low | Low |

### Category 4: Encoders/Decoders (4 files)
| File | Module | Complexity | Priority |
|------|--------|------------|----------|
| decoder.md | decoder | Low | Low |
| encoder.md | encoder | Low | Low |
| encoder_priority_enable.md | encoder_priority_enable | Low | Medium |
| hex_to_7seg.md | hex_to_7seg | Low | Low |

### Category 5: Gray Code Converters (2 files)
| File | Module | Complexity | Priority |
|------|--------|------------|----------|
| gray2bin.md | gray2bin | Low | Low |
| grayj2bin.md | grayj2bin | Low | Low |

### Category 6: Clock/Reset Utilities (4 files)
| File | Module | Complexity | Priority |
|------|--------|------------|----------|
| clock_divider.md | clock_divider | Low | Medium |
| clock_pulse.md | clock_pulse | Low | Low |
| icg.md | icg | Low | High |
| reset_sync.md | reset_sync | Low | High |

### Category 7: Synchronization (2 files)
| File | Module | Complexity | Priority |
|------|--------|------------|----------|
| debounce.md | debounce | Low | Low |
| sync_pulse.md | sync_pulse | Medium | Medium |

### Category 8: Bit Manipulation (4 files)
| File | Module | Complexity | Priority |
|------|--------|------------|----------|
| count_leading_zeros.md | count_leading_zeros | Medium | High |
| find_first_set.md | find_first_set | Medium | Medium |
| find_last_set.md | find_last_set | Medium | Medium |
| leading_one_trailing_one.md | leading_one_trailing_one | Medium | Medium |

### Category 9: CAM (1 file)
| File | Module | Complexity | Priority |
|------|--------|------------|----------|
| cam_tag.md | cam_tag | High | High |

### Category 10: Shifters (3 files)
| File | Module | Complexity | Priority |
|------|--------|------------|----------|
| shifter_barrel.md | shifter_barrel | Medium | High |
| shifter_lfsr.md | shifter_lfsr | Medium | Medium |
| shifter_universal.md | shifter_universal | Medium | Medium |

### Category 11: FIFOs (2 files)
| File | Module | Complexity | Priority |
|------|--------|------------|----------|
| fifo_control.md | fifo_control | Medium | Medium |
| fifo_sync.md | fifo_sync | Medium | High |

### Category 12: Math - Adders (8 files)
| File | Module | Complexity | Priority |
|------|--------|------------|----------|
| math_adder_basic.md | math_adder_full/half | Low | Medium |
| math_adder_brent_kung.md | math_adder_brent_kung_* | High | High |
| math_adder_carry_lookahead.md | math_adder_carry_lookahead | Medium | High |
| math_adder_carry_save.md | math_adder_carry_save | Medium | Medium |
| math_adder_han_carlson.md | math_adder_han_carlson_* | High | High |
| math_adder_kogge_stone.md | math_adder_kogge_stone | High | High |
| math_adder_ripple_carry.md | math_adder_ripple_carry | Low | Medium |
| math_subtractor.md | math_subtractor_* | Low | Medium |

### Category 13: Math - Multipliers (4 files)
| File | Module | Complexity | Priority |
|------|--------|------------|----------|
| math_multiplier_basic.md | math_multiplier_basic_cell | Low | Medium |
| math_multiplier_dadda_4to2.md | math_multiplier_dadda_4to2_008 | High | High |
| math_multiplier_dadda_tree.md | math_multiplier_dadda_tree_* | High | High |
| math_multiplier_wallace_tree.md | math_multiplier_wallace_tree_* | High | High |

### Category 14: Math - Prefix Cells (1 file)
| File | Module | Complexity | Priority |
|------|--------|------------|----------|
| math_prefix_cell.md | math_prefix_cell | Low | Medium |

### Category 15: BF16 Sub-blocks (2 files)
| File | Module | Complexity | Priority |
|------|--------|------------|----------|
| math_bf16_exponent_adder.md | math_bf16_exponent_adder | Medium | High |
| math_bf16_mantissa_mult.md | math_bf16_mantissa_mult | Medium | High |

### Category 16: Miscellaneous (1 file)
| File | Module | Complexity | Priority |
|------|--------|------------|----------|
| pwm.md | pwm | Low | Low |

## Diagram Types and Templates

### Type 1: Simple Datapath (Low Complexity)
For modules with linear data flow (counters, basic adders, encoders).

**Mermaid Source (.mmd file):**
```
%%{init: {'theme': 'neutral', 'themeVariables': { 'fontSize': '14px'}}}%%
flowchart LR
    subgraph Inputs
        A[i_clk]
        B[i_rst_n]
        C[i_data]
    end

    subgraph Module["module_name"]
        D[Logic Block]
    end

    subgraph Outputs
        E[o_result]
    end

    A --> D
    B --> D
    C --> D
    D --> E
```

### Type 2: Multi-Stage Pipeline (Medium Complexity)
For modules with pipeline stages (shifters, prefix adders).

```
%%{init: {'theme': 'neutral'}}%%
flowchart LR
    subgraph Inputs
        I1[input_a]
        I2[input_b]
    end

    subgraph Stage1["Stage 1"]
        S1[Process]
    end

    subgraph Stage2["Stage 2"]
        S2[Process]
    end

    subgraph Outputs
        O1[output]
    end

    I1 --> S1
    I2 --> S1
    S1 --> S2
    S2 --> O1
```

### Type 3: Hierarchical Block (High Complexity)
For modules that instantiate submodules (tree multipliers, FMA).

```
%%{init: {'theme': 'neutral'}}%%
flowchart TB
    subgraph Top["top_module"]
        subgraph Sub1["submodule_1"]
            A[Logic]
        end
        subgraph Sub2["submodule_2"]
            B[Logic]
        end
        C[Combine Logic]
    end

    I[Inputs] --> Sub1
    I --> Sub2
    Sub1 --> C
    Sub2 --> C
    C --> O[Outputs]
```

### Type 4: FSM Diagram
For state machine modules (arbiters, FIFO control).

```
%%{init: {'theme': 'neutral'}}%%
stateDiagram-v2
    [*] --> IDLE
    IDLE --> ACTIVE: condition
    ACTIVE --> DONE: complete
    DONE --> IDLE: reset
```

## Implementation Approach

### Phase 1: High Priority Files (16 files)
Focus on files that are frequently referenced or have complex logic:
1. Arbiters (4)
2. Parallel prefix adders (3): brent_kung, han_carlson, kogge_stone
3. Tree multipliers (3): dadda_4to2, dadda_tree, wallace_tree
4. BF16 subblocks (2)
5. Key utilities (4): icg, reset_sync, count_leading_zeros, cam_tag

### Phase 2: Medium Priority Files (20 files)
- Counters with special features
- Data integrity modules
- Shifters
- FIFOs

### Phase 3: Low Priority Files (20 files)
- Simple encoders/decoders
- Basic adders/subtractors
- Simple converters

## Directory Structure

```
docs/markdown/assets/RTLCommon/
├── arbiter_round_robin.mmd         # Mermaid source
├── arbiter_round_robin.svg         # Rendered SVG
├── arbiter_round_robin_simple.mmd
├── arbiter_round_robin_simple.svg
├── ...
└── pwm.svg
```

## Generator Script Design

Create a Python script that:
1. Reads RTL module to extract ports and structure
2. Generates Mermaid diagram definition (.mmd file)
3. Uses `mmdc` (Mermaid CLI) to render SVG
4. Updates markdown file with image reference

### Script: `bin/generate_rtlcommon_diagrams.py`

```python
#!/usr/bin/env python3
"""Generate block diagrams for RTLCommon markdown documentation.

Reads RTL modules, generates Mermaid definitions, renders SVGs,
and updates markdown files with image references.
"""

import os
import re
import subprocess
from pathlib import Path
from dataclasses import dataclass
from typing import List, Dict, Optional

@dataclass
class PortInfo:
    name: str
    direction: str  # 'input', 'output', 'inout'
    width: str
    description: str = ""

@dataclass
class ModuleInfo:
    name: str
    inputs: List[PortInfo]
    outputs: List[PortInfo]
    submodules: List[str]
    description: str = ""

class RTLParser:
    """Parse SystemVerilog modules to extract structure."""

    def __init__(self, rtl_dir: str):
        self.rtl_dir = Path(rtl_dir)

    def parse_module(self, module_name: str) -> Optional[ModuleInfo]:
        """Parse a SystemVerilog file and extract module info."""
        sv_file = self.rtl_dir / f"{module_name}.sv"
        if not sv_file.exists():
            return None

        content = sv_file.read_text()

        # Extract inputs
        inputs = self._extract_ports(content, 'input')
        outputs = self._extract_ports(content, 'output')
        submodules = self._extract_submodules(content)

        return ModuleInfo(
            name=module_name,
            inputs=inputs,
            outputs=outputs,
            submodules=submodules
        )

    def _extract_ports(self, content: str, direction: str) -> List[PortInfo]:
        """Extract port declarations from module."""
        ports = []
        pattern = rf'{direction}\s+(?:logic\s+)?(?:\[([^\]]+)\]\s+)?(\w+)'
        for match in re.finditer(pattern, content):
            width = match.group(1) if match.group(1) else "1"
            name = match.group(2)
            ports.append(PortInfo(name=name, direction=direction, width=width))
        return ports

    def _extract_submodules(self, content: str) -> List[str]:
        """Extract instantiated submodule names."""
        pattern = r'(\w+)\s+(?:#\s*\([^)]*\)\s+)?u_\w+\s*\('
        return list(set(re.findall(pattern, content)))


class MermaidGenerator:
    """Generate Mermaid diagram definitions."""

    THEME_CONFIG = "%%{init: {'theme': 'neutral', 'themeVariables': { 'fontSize': '14px'}}}%%"

    def generate_datapath_diagram(self, module: ModuleInfo) -> str:
        """Generate a datapath-style flowchart."""
        lines = [self.THEME_CONFIG, "flowchart LR"]

        # Input subgraph
        lines.append('    subgraph Inputs')
        for port in module.inputs:
            lines.append(f'        {port.name}["{port.name}"]')
        lines.append('    end')

        # Module processing
        lines.append(f'    subgraph Module["{module.name}"]')
        lines.append('        LOGIC[Processing Logic]')
        lines.append('    end')

        # Output subgraph
        lines.append('    subgraph Outputs')
        for port in module.outputs:
            lines.append(f'        {port.name}["{port.name}"]')
        lines.append('    end')

        # Connections
        for port in module.inputs:
            lines.append(f'    {port.name} --> LOGIC')
        for port in module.outputs:
            lines.append(f'    LOGIC --> {port.name}')

        return '\n'.join(lines)

    def generate_hierarchical_diagram(self, module: ModuleInfo) -> str:
        """Generate a hierarchical diagram with submodules."""
        lines = [self.THEME_CONFIG, "flowchart TB"]

        lines.append(f'    subgraph TOP["{module.name}"]')

        # Add submodules
        for i, sub in enumerate(module.submodules):
            lines.append(f'        subgraph SUB{i}["{sub}"]')
            lines.append(f'            S{i}[Logic]')
            lines.append('        end')

        lines.append('        COMBINE[Output Logic]')
        lines.append('    end')

        # Input/output
        lines.append('    IN[Inputs] --> TOP')
        lines.append('    TOP --> OUT[Outputs]')

        # Submodule connections
        for i in range(len(module.submodules)):
            lines.append(f'    SUB{i} --> COMBINE')

        return '\n'.join(lines)


class DiagramRenderer:
    """Render Mermaid to SVG using mmdc."""

    def __init__(self, output_dir: str):
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)

    def render(self, mermaid_content: str, output_name: str) -> Path:
        """Render Mermaid content to SVG."""
        mmd_file = self.output_dir / f"{output_name}.mmd"
        svg_file = self.output_dir / f"{output_name}.svg"

        # Write Mermaid source
        mmd_file.write_text(mermaid_content)

        # Render to SVG
        result = subprocess.run(
            ['mmdc', '-i', str(mmd_file), '-o', str(svg_file), '-t', 'neutral'],
            capture_output=True,
            text=True
        )

        if result.returncode != 0:
            print(f"Error rendering {output_name}: {result.stderr}")
            return None

        return svg_file


class MarkdownUpdater:
    """Update markdown files with diagram references."""

    def __init__(self, md_dir: str, assets_rel_path: str = "../assets/RTLCommon"):
        self.md_dir = Path(md_dir)
        self.assets_rel_path = assets_rel_path

    def update_markdown(self, module_name: str, svg_filename: str) -> bool:
        """Insert diagram reference into markdown file."""
        md_file = self.md_dir / f"{module_name}.md"
        if not md_file.exists():
            return False

        content = md_file.read_text()

        # Check if diagram already exists
        if f"![{module_name}" in content:
            print(f"Diagram already exists in {md_file.name}")
            return True

        # Find insertion point (after ## Architecture or create section)
        img_ref = f"\n![{module_name} Block Diagram]({self.assets_rel_path}/{svg_filename})\n"

        if "## Architecture" in content:
            # Insert after Architecture heading
            content = content.replace(
                "## Architecture",
                f"## Architecture\n\n### Block Diagram\n{img_ref}"
            )
        elif "## Purpose" in content:
            # Insert after Purpose section
            purpose_match = re.search(r'(## Purpose.*?)(\n## )', content, re.DOTALL)
            if purpose_match:
                insert_pos = purpose_match.end(1)
                content = (
                    content[:insert_pos] +
                    f"\n\n## Architecture\n\n### Block Diagram\n{img_ref}" +
                    content[insert_pos:]
                )
        else:
            # Insert after first heading
            first_heading = re.search(r'^# .+\n', content, re.MULTILINE)
            if first_heading:
                insert_pos = first_heading.end()
                content = (
                    content[:insert_pos] +
                    f"\n## Architecture\n\n### Block Diagram\n{img_ref}\n" +
                    content[insert_pos:]
                )

        md_file.write_text(content)
        return True


def main():
    """Main entry point."""
    import argparse

    parser = argparse.ArgumentParser(description='Generate RTLCommon diagrams')
    parser.add_argument('--rtl-dir', default='rtl/common',
                       help='RTL source directory')
    parser.add_argument('--md-dir', default='docs/markdown/RTLCommon',
                       help='Markdown documentation directory')
    parser.add_argument('--assets-dir', default='docs/markdown/assets/RTLCommon',
                       help='Output directory for diagrams')
    parser.add_argument('--modules', nargs='+',
                       help='Specific modules to process (default: all)')
    args = parser.parse_args()

    rtl_parser = RTLParser(args.rtl_dir)
    mermaid_gen = MermaidGenerator()
    renderer = DiagramRenderer(args.assets_dir)
    md_updater = MarkdownUpdater(args.md_dir)

    # Get list of modules to process
    if args.modules:
        modules = args.modules
    else:
        # Get all markdown files
        modules = [f.stem for f in Path(args.md_dir).glob('*.md')
                  if f.stem not in ('index', 'overview')]

    for module_name in modules:
        print(f"Processing {module_name}...")

        # Parse RTL
        module_info = rtl_parser.parse_module(module_name)
        if not module_info:
            print(f"  Could not parse RTL for {module_name}")
            continue

        # Generate Mermaid
        if module_info.submodules:
            mermaid = mermaid_gen.generate_hierarchical_diagram(module_info)
        else:
            mermaid = mermaid_gen.generate_datapath_diagram(module_info)

        # Render SVG
        svg_file = renderer.render(mermaid, module_name)
        if not svg_file:
            continue

        # Update markdown
        if md_updater.update_markdown(module_name, svg_file.name):
            print(f"  Updated {module_name}.md with diagram reference")


if __name__ == '__main__':
    main()
```

## Regeneration Script

Create a shell script to regenerate all diagrams:

### Script: `docs/markdown/assets/RTLCommon/regenerate_diagrams.sh`

```bash
#!/bin/bash
# Regenerate all RTLCommon block diagrams from Mermaid sources

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

echo "Regenerating RTLCommon diagrams..."

for mmd_file in *.mmd; do
    if [ -f "$mmd_file" ]; then
        svg_file="${mmd_file%.mmd}.svg"
        echo "  Rendering $mmd_file -> $svg_file"
        mmdc -i "$mmd_file" -o "$svg_file" -t neutral -b transparent
    fi
done

echo "Done. Regenerated $(ls -1 *.svg 2>/dev/null | wc -l) diagrams."
```

## Mermaid CLI Requirements

```bash
# Install mermaid-cli globally
npm install -g @mermaid-js/mermaid-cli

# Or use npx (no install required)
npx -p @mermaid-js/mermaid-cli mmdc -i diagram.mmd -o diagram.svg

# Render with options
mmdc -i diagram.mmd -o diagram.svg -t neutral -b transparent -w 800
```

## Quality Standards

1. **Consistency**: All diagrams use neutral theme with transparent background
2. **Accuracy**: Ports and signals match RTL exactly
3. **Readability**: Clear labels, appropriate sizing (800px default width)
4. **Maintainability**: Source .mmd files stored alongside .svg files
5. **PDF Compatibility**: External SVG references, no embedded Mermaid code

## Markdown Integration Pattern

**Before (no diagram):**
```markdown
# Round Robin Arbiter

## Purpose
The `arbiter_round_robin` module implements...

## Parameters
...
```

**After (with diagram):**
```markdown
# Round Robin Arbiter

## Purpose
The `arbiter_round_robin` module implements...

## Architecture

### Block Diagram

![arbiter_round_robin Block Diagram](../assets/RTLCommon/arbiter_round_robin.svg)

## Parameters
...
```

## Estimated Effort

| Phase | Files | Est. Time | Priority |
|-------|-------|-----------|----------|
| Setup & Script | - | 2 hours | - |
| Phase 1 | 16 | 4-6 hours | High |
| Phase 2 | 20 | 4-5 hours | Medium |
| Phase 3 | 20 | 3-4 hours | Low |
| **Total** | **56** | **13-17 hours** | - |

## Next Steps

1. [ ] Create directory: `docs/markdown/assets/RTLCommon/`
2. [ ] Install mermaid-cli: `npm install -g @mermaid-js/mermaid-cli`
3. [ ] Create generator script: `bin/generate_rtlcommon_diagrams.py`
4. [ ] Create regeneration script: `regenerate_diagrams.sh`
5. [ ] Generate Phase 1 diagrams (high priority modules)
6. [ ] Validate PDF generation with sample files
7. [ ] Generate Phase 2 and 3 diagrams
8. [ ] Update all markdown files with image references
9. [ ] Final validation of all links and rendering

## Notes

- **PDF Compatibility**: Using external SVG files with markdown image syntax ensures compatibility with pandoc, weasyprint, and other PDF generators
- **Version Control**: Store both .mmd source and .svg output for reproducibility
- **Regeneration**: The regenerate_diagrams.sh script allows quick updates when Mermaid sources change
- **Graphviz Alternative**: For complex tree structures (prefix adders), consider Graphviz DOT format if Mermaid layout is inadequate
