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

**[← Back to Scripts Index](index.md)**

# md_to_docx

The `md_to_docx` script at `bin/md_to_docx.py` is a comprehensive markdown to DOCX/PDF converter built on top of Pandoc. It provides advanced features including index expansion, diagram rendering (Mermaid, Wavedrom), corporate styling, and automated table of contents generation with clickable links and PDF bookmarks.

## Overview

This script bridges the gap between markdown documentation and professional document formats required for formal deliverables. It handles complex document structures including multi-file indexes, embedded diagrams, custom title pages, and corporate styling specifications.

## Features

### Document Structure Features

- **Index Expansion** (`--expand-index`): Parse an index.md file and inline linked chapter .md files in order
- **Skip Index Content** (`--skip-index-content`): Exclude index file content, only include linked chapters
- **Title Page** (`--title-page [path]`): Prepend a title page (auto-generated if no path given)
- **Page Breaks** (`--pagebreak`): Insert page breaks between concatenated files
- **Section Breaks** (`--section-breaks`): Start each top-level section on a new page (PDF only)

### Table of Contents and Lists

- **Table of Contents** (`--toc`): Generate clickable TOC with depth=3
- **Number Sections** (`--number-sections`): Add section numbering (1, 1.1, 1.1.1)
- **List of Tables** (`--lot`): Include List of Tables after TOC (PDF only)
- **List of Figures** (`--lof`): Include List of Figures after TOC (PDF only)
- **List of Waveforms** (`--low`): Include List of Waveforms after TOC (PDF only)

### Diagram Rendering

- **Mermaid Diagrams**: `\`\`\`mermaid` blocks rendered to PNG via mmdc CLI
- **Wavedrom Diagrams**: `\`\`\`wavedrom` JSON blocks rendered to SVG
- **Wavedrom Images**: `![title](diagram.json)` references rendered to SVG
- **Degraded Fallback**: If rendering tools unavailable, keeps diagrams as code blocks

### PDF-Specific Features

- **Hyperref Integration**: Clickable TOC, internal links, and PDF bookmarks
- **Unicode Support**: Force Unicode-friendly PDF engine (xelatex) by default
- **Font Controls**: `--mainfont`, `--monofont`, `--sansfont`, `--mathfont` options
- **Emoji Mapping**: Robust emoji handling for PDF compatibility
- **Narrow Margins** (`--narrow-margins`): Use 0.75in margins for more content per page

### Corporate Styling

- **YAML Style Config** (`--style`): Apply corporate styling to DOCX and PDF
- **Custom Title Pages**: Logo, company name split coloring, configurable fonts
- **Header/Footer**: Document title, confidential text, page numbers
- **Heading Styling**: Custom colors, backgrounds, underlines, spacing
- **Table Styling**: Header row backgrounds, font sizes
- **List Generation**: Automatic List of Figures/Tables/Waveforms with TOC-style formatting

## Usage

### Basic Conversion

Convert single markdown file to DOCX:
```bash
python3 bin/md_to_docx.py input.md output.docx
```

Convert with PDF output:
```bash
python3 bin/md_to_docx.py input.md output.docx --pdf
```

### Index Expansion

Convert index with linked chapters:
```bash
python3 bin/md_to_docx.py index.md output.docx --expand-index
```

Skip index content, only include chapters:
```bash
python3 bin/md_to_docx.py index.md output.docx --expand-index --skip-index-content
```

### Table of Contents and Numbering

Generate TOC with numbered sections:
```bash
python3 bin/md_to_docx.py input.md output.docx --toc --number-sections
```

Add lists of figures and tables:
```bash
python3 bin/md_to_docx.py input.md output.docx --pdf --toc --lof --lot
```

### Title Pages

Auto-generate title page:
```bash
python3 bin/md_to_docx.py input.md output.docx --title-page
```

Use custom title page:
```bash
python3 bin/md_to_docx.py input.md output.docx --title-page custom_title.md
```

### Diagram Rendering

Enable all diagram types (default behavior):
```bash
python3 bin/md_to_docx.py input.md output.docx --pdf
```

Skip diagram rendering for faster processing:
```bash
python3 bin/md_to_docx.py input.md output.docx --no-mermaid --no-wavedrom
```

### Corporate Styling

Apply YAML style configuration:
```bash
python3 bin/md_to_docx.py input.md output.docx --pdf --style corporate_style.yaml --toc --lof --lot
```

### Advanced Options

Multiple asset directories:
```bash
python3 bin/md_to_docx.py input.md output.docx \
  --assets-dir images \
  --assets-dir diagrams \
  --assets-dir waveforms
```

Custom fonts for PDF:
```bash
python3 bin/md_to_docx.py input.md output.pdf --pdf \
  --mainfont "DejaVu Serif" \
  --monofont "DejaVu Sans Mono"
```

Debug merged markdown:
```bash
python3 bin/md_to_docx.py input.md output.docx --debug-md
# Creates output.build.md for inspection
```

## Parameters and Options

### Required Arguments

- `input`: Input Markdown file (index or single chapter)
- `output`: Output .docx filename (PDF uses same basename with .pdf extension)

### Document Structure Options

- `--expand-index`: Parse input as index and inline linked chapters
- `--skip-index-content`: Don't include index file content (only chapters)
- `--pagebreak`: Insert page breaks between concatenated files
- `--section-breaks`: Start each top-level section on new page (PDF only)
- `--title-page [PATH]`: Prepend title page (auto if omitted)

### Table of Contents Options

- `--toc`: Include table of contents
- `--number-sections`: Number sections hierarchically
- `--lot`: Include List of Tables (PDF only)
- `--lof`: Include List of Figures (PDF only)
- `--low`: Include List of Waveforms (PDF only)

### Diagram Rendering Options

- `--no-mermaid`: Skip mermaid diagram rendering
- `--no-wavedrom`: Skip wavedrom diagram rendering

### PDF Generation Options

- `--pdf`: Generate PDF alongside DOCX
- `--pdf-engine ENGINE`: Override PDF engine (default: xelatex)
- `--narrow-margins`: Use 0.75in margins instead of default

### Font Options (XeLaTeX/LuaLaTeX)

- `--mainfont FONT`: Main text font (default: "DejaVu Serif")
- `--monofont FONT`: Monospace font (default: "DejaVu Sans Mono")
- `--sansfont FONT`: Sans-serif font (optional)
- `--mathfont FONT`: Math font (optional)

### Corporate Styling Options

- `--style CONFIG.yaml`: Apply corporate styling from YAML config
- `--reference-doc TEMPLATE.docx`: Use DOCX template for styling

### Resource and Asset Options

- `--assets-dir DIR`: Add asset directory (repeatable)

### Debug and Output Options

- `--quiet`: Reduce Pandoc output verbosity
- `--debug-md`: Save merged markdown for debugging

## Diagram Rendering

### Mermaid Diagrams

Requires: `npm install -g @mermaid-js/mermaid-cli`

Markdown syntax:
```markdown
### Figure 1: System Architecture

\`\`\`mermaid
graph TD
    A[Start] --> B[Process]
    B --> C[End]
\`\`\`
```

The script:
1. Extracts the mermaid code block
2. Calls `mmdc` CLI to render to PNG (scale=2 for high resolution)
3. Replaces code block with image reference
4. Uses white background for better PDF embedding
5. Preserves figure title for caption

### Wavedrom Diagrams

Requires: `pip install wavedrom` OR `npm install -g wavedrom-cli`

**Inline blocks:**
```markdown
### Waveform 1: Clock and Data

\`\`\`wavedrom
{ "signal": [
  { "name": "clk", "wave": "p......." },
  { "name": "data", "wave": "x.34.5x." }
]}
\`\`\`
```

**External JSON files:**
```markdown
![AXI Transaction](diagrams/axi_waveform.json)
```

The script:
1. Tries python-wavedrom first for rendering
2. Falls back to wavedrom-cli if available
3. Renders to SVG for vector graphics quality
4. Adds to List of Waveforms if `--low` specified

### Diagram Fallback

If rendering tools are unavailable:
- Mermaid blocks remain as code blocks
- Wavedrom blocks remain as JSON code blocks
- External references become text links

## Corporate Styling (YAML Config)

### YAML Configuration Format

```yaml
# Color definitions
colors:
  primary: "#CC0000"      # Red
  secondary: "#2E74B5"    # Blue
  black: "#000000"
  table_header: "#D9E2F3"

# Company information
company:
  confidential_text: "Proprietary and Confidential"

# Title page configuration
title_page:
  enabled: true
  logo: "assets/logo.png"
  logo_width: 2.0          # inches
  company: "QernelAI"
  title: "Engineering Specification"
  subtitle: "Q32 Processor"
  date: "December 2024"
  company_color: "primary"  # Reference to colors
  title_color: "black"
  company_size: 72         # Font size in points
  title_size: 36
  date_size: 36

# Header and footer
header_footer:
  enabled: true
  font_size: 8

# List configurations
lists:
  lot: true                # List of Tables
  lof: true                # List of Figures
  low: true                # List of Waveforms

# Heading styles
headings:
  h1:
    font_size: 18
    color: "secondary"
    bold: true
    background: "table_header"
    space_before: 12
    space_after: 6
  h2:
    font_size: 14
    color: "secondary"
    bold: true
    underline_color: "primary"

# Body text
body:
  font_size: 11

# Table styling
tables:
  header:
    background: "#D9E2F3"
    bold: true
    font_size: 11

# Font configuration
fonts:
  main: "Calibri"
  heading: "Calibri"
  code: "Consolas"
```

### Corporate Styling Features

**Title Page:**
- Logo image (centered, configurable width)
- Company name with split coloring (e.g., "Qernel" black + "AI" red)
- Title and subtitle combined
- Date
- All with configurable font sizes
- Page break before TOC

**Headers and Footers:**
- Left: Document title
- Center: Confidential text
- Right: Page numbers (Page X of Y)

**Heading Styles:**
- Custom colors per heading level
- Background shading
- Bottom border/underline
- Configurable spacing
- Bold/italic options

**Lists (LoF, LoT, LoW):**
- TOC-style formatting with dot leaders
- Clickable hyperlinks to figures/tables/waveforms
- Right-aligned page numbers
- Automatic bookmark generation

**Tables:**
- Header row background colors
- Custom font sizes
- Bold headers

## TOC Update Workflow

When using `--style` with `--pdf`:

1. Generate DOCX from markdown
2. Apply corporate styling to DOCX
3. Update TOC using LibreOffice UNO API
4. Re-apply title page fonts (LibreOffice may reset them)
5. Convert styled DOCX to PDF using LibreOffice

This ensures the PDF matches the DOCX styling exactly.

## Internal Functionality

### Index Collection (`collect_from_index`)

Scans index markdown for links to .md files:
1. Finds inline comment directives: `<!-- include: path/file.md -->`
2. Finds markdown links: `[Title](path/file.md)`
3. Resolves paths relative to index directory
4. Returns ordered list of paths to concatenate

### Markdown Concatenation (`concat_markdown`)

Merges multiple markdown files:
1. Reads each file with UTF-8 encoding
2. Rewrites relative image paths to absolute paths
3. Inserts page breaks between files if `--pagebreak` specified
4. Joins all parts with newlines

### Diagram Rewriting

**Mermaid blocks** (`rewrite_mermaid_blocks`):
1. Finds `\`\`\`mermaid` fenced code blocks with regex
2. Extracts optional figure title from preceding heading
3. Calls `mmdc` CLI with puppeteer config (--no-sandbox for Ubuntu 23.10+)
4. Renders to PNG with scale=2 and white background
5. Replaces code block with image reference

**Wavedrom blocks** (`rewrite_wavedrom_blocks`):
1. Finds `\`\`\`wavedrom` fenced code blocks
2. Tries python-wavedrom library first
3. Falls back to wavedrom-cli
4. Renders to SVG for vector graphics
5. If `--low`, adds to List of Waveforms with raw LaTeX

**Wavedrom images** (`rewrite_wavedrom_images`):
1. Finds image references to .json files
2. Resolves paths relative to base directory
3. Renders to SVG using python-wavedrom or CLI
4. Replaces image reference with SVG path

### Pandoc Execution

**DOCX generation** (`run_pandoc_docx`):
- Uses `markdown+yaml_metadata_block+pipe_tables+fenced_code_blocks`
- Builds resource path from assets directories
- Applies reference document if specified
- Generates TOC and section numbers if requested

**PDF generation** (`run_pandoc_pdf`):
- Uses xelatex engine by default for Unicode support
- Includes title page via `--include-before-body`
- Configures fonts (mainfont, monofont, sansfont, mathfont)
- Enables hyperref for clickable links and PDF bookmarks
- Adds titlesec for section breaks if requested
- Includes tocloft for List of Waveforms if requested

### Corporate Styling (`apply_docx_style`)

Uses python-docx library to modify DOCX XML:

1. **Title Page** (`add_title_page_to_docx`):
   - Creates paragraphs with custom formatting
   - Inserts logo image if specified
   - Applies split coloring for company name
   - Uses keep_with_next to prevent page breaks
   - Inserts page break after title page

2. **Lists** (`add_lists_to_docx`):
   - Scans document for Figure/Table/Waveform headings
   - Adds XML bookmarks to each
   - Creates list entries with TOC-style formatting
   - Adds dot leaders and PAGEREF fields
   - Inserts between title page and content

3. **Styling**:
   - Iterates through paragraphs by style
   - Applies font sizes, colors, backgrounds
   - Adds bottom borders for heading underlines
   - Styles table header rows

4. **Footer**:
   - Creates 3-column table for left/center/right alignment
   - Removes table borders
   - Adds PAGE and NUMPAGES fields for page numbering

### TOC Update (`update_docx_toc`)

Uses LibreOffice UNO API:
1. Starts LibreOffice in headless listening mode
2. Connects via UNO resolver
3. Opens document hidden
4. Refreshes all document indexes
5. Saves and closes document
6. Shuts down LibreOffice

### Font Re-application (`reapply_title_page_fonts`)

After LibreOffice TOC update:
1. Re-opens DOCX with python-docx
2. Identifies title page paragraphs
3. Re-applies configurable font sizes
4. Fixes list heading styles if present

## Required Tools

### Core Requirements

- **Pandoc**: Markdown to DOCX/PDF conversion
  ```bash
  sudo apt-get install pandoc
  ```

### Diagram Rendering

- **Mermaid CLI** (optional, for mermaid diagrams):
  ```bash
  npm install -g @mermaid-js/mermaid-cli
  ```

- **Wavedrom** (optional, for waveform diagrams):
  ```bash
  pip install wavedrom
  # OR
  npm install -g wavedrom-cli
  ```

- **Inkscape** (optional, for SVG to PDF conversion):
  ```bash
  sudo apt-get install inkscape
  ```

### Corporate Styling

- **Python-DOCX** (for DOCX styling):
  ```bash
  pip install python-docx
  ```

- **PyYAML** (for style configuration):
  ```bash
  pip install pyyaml
  ```

- **LibreOffice** (for TOC update and DOCX to PDF):
  ```bash
  sudo apt-get install libreoffice
  ```

### PDF Generation

- **XeLaTeX** (for Unicode PDF support):
  ```bash
  sudo apt-get install texlive-xetex
  ```

- **DejaVu Fonts** (recommended for wide Unicode coverage):
  ```bash
  sudo apt-get install fonts-dejavu
  ```

## Error Handling

The script handles various error conditions:

1. **Missing Pandoc**: Raises RuntimeError with clear message
2. **Missing Diagram Tools**: Degrades gracefully, keeps diagrams as code
3. **Missing Style Config**: Logs warning, continues without styling
4. **TOC Update Failure**: Logs warning, fallback to Pandoc PDF
5. **Font Rendering Issues**: Falls back to SVG if inkscape unavailable

## Troubleshooting

### Mermaid Rendering Fails

**Symptoms:** Diagrams remain as code blocks

**Solutions:**
- Install mermaid-cli: `npm install -g @mermaid-js/mermaid-cli`
- On Ubuntu 23.10+, script handles --no-sandbox automatically
- Check puppeteer config in temp directory
- Use `--no-mermaid` to skip rendering

### Wavedrom Rendering Fails

**Symptoms:** Waveforms remain as JSON blocks

**Solutions:**
- Install python-wavedrom: `pip install wavedrom`
- OR install wavedrom-cli: `npm install -g wavedrom-cli`
- Check JSON syntax (must be valid Wavedrom format)
- Use `--no-wavedrom` to skip rendering

### PDF Generation Fails

**Symptoms:** DOCX created but PDF fails

**Solutions:**
- Install texlive-xetex: `sudo apt-get install texlive-xetex`
- Install fonts: `sudo apt-get install fonts-dejavu`
- Try fallback to LibreOffice: Ensure soffice/libreoffice is installed
- Use `--pdf-engine lualatex` as alternative

### TOC Not Populated in DOCX

**Symptoms:** TOC shows "No table of contents entries found"

**Solutions:**
- In Word: Ctrl+A (select all), F9 (update fields)
- Use `--style` with LibreOffice for automatic TOC update
- Check that headings are using proper markdown syntax (#, ##, ###)

### Corporate Styling Not Applied

**Symptoms:** DOCX generated but styling missing

**Solutions:**
- Install python-docx: `pip install python-docx`
- Install pyyaml: `pip install pyyaml`
- Check YAML syntax (validate with online YAML validator)
- Verify logo path is relative to YAML config file

## Use Cases

### Technical Documentation

Generate professional specifications from markdown:
```bash
python3 bin/md_to_docx.py spec_index.md deliverable.docx \
  --expand-index \
  --toc --number-sections \
  --lof --lot --low \
  --pdf \
  --style corporate.yaml
```

### User Manuals

Create multi-chapter manuals:
```bash
python3 bin/md_to_docx.py manual_index.md user_manual.docx \
  --expand-index \
  --skip-index-content \
  --toc \
  --pagebreak
```

### Design Documents

Technical designs with diagrams:
```bash
python3 bin/md_to_docx.py design.md design_doc.docx \
  --pdf \
  --title-page \
  --lof \
  --assets-dir diagrams \
  --assets-dir waveforms
```

### Quick Conversions

Fast conversion without rendering:
```bash
python3 bin/md_to_docx.py notes.md notes.docx \
  --no-mermaid --no-wavedrom \
  --quiet
```

## Dependencies

**Standard Library:**
- argparse, pathlib, re, subprocess, sys, tempfile, datetime

**External (Required):**
- Pandoc (command-line tool)

**External (Optional):**
- mermaid-cli (npm package)
- wavedrom (pip package) OR wavedrom-cli (npm package)
- python-docx (pip package)
- pyyaml (pip package)
- LibreOffice (soffice/libreoffice command)
- inkscape (for SVG to PDF conversion)

---

[Back to Scripts Index](index.md)

---
