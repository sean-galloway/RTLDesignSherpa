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

# STREAM Specification Update Plan

**Purpose:** Update STREAM Micro-Architecture Specification to match Q32 MAS quality standards
**Date:** 2026-01-02
**Author:** seang

---

## Current Issues

1. **Title Page Layout** - Logo, company name, title, and date are spread across multiple pages instead of being on a single centered title page
2. **Empty List of Figures** - Markdown doesn't use pandoc caption syntax for figures
3. **Empty List of Tables** - Tables lack the `: Caption` suffix required by pandoc
4. **No Revision History** - Missing document and per-block revision tracking
5. **Empty List of Waveforms** - Waveforms lack `#### Waveform X.Y.Z: Title` format

---

## Required Changes

### Phase 1: Fix Title Page (md_to_docx.py) - COMPLETED

**Issue:** The DOCX title page generator creates separate paragraphs that don't stay on one page.

**Solution:** Modified `add_title_page_to_docx()` to use `keep_with_next` Word XML property:
- Added `set_keep_with_next()` helper function
- Applied to all title page paragraphs (logo, company, title, date)
- Page break paragraph does not need the property

**File:** `bin/md_to_docx.py`

**Changes:**
- [x] Update `add_title_page_to_docx()` to keep all elements on one page
- [x] Ensure logo, company name, title, subtitle, and date flow correctly
- [x] Test with LibreOffice PDF conversion

---

### Phase 2: Add Document Front Matter - COMPLETED

**Created:** `stream_spec/ch00_front_matter/00_document_info.md`

**Content includes:**
- Document Information (STREAM subsystem description)
- References table (PRD, RAPIDS MAS, ARM AXI/APB specs)
- Terminology section (AXI, APB, Beat, Burst, Channel, Descriptor, DMA, FUB, MAC, MonBus, V1/V2/V3, etc.)
- Revision History table with seang as author

---

### Phase 3: Update Index to Include Front Matter - COMPLETED

**File:** `stream_spec/stream_index.md`

**Changes:**
- [x] Added front matter link before Chapter 1

---

### Phase 4: Add Table Captions to All Markdown Files - COMPLETED

**Required Format:** Add `: Caption text` line immediately after each table.

**Implementation:** Used automated script to add captions based on section headers.

**Results:**
- **435 table captions added** across 29 markdown files
- Captions derived from nearest section header above each table
- All chapter 1-6 files updated

**Files updated:**
- [x] ch01_overview/*.md (3 files)
- [x] ch02_blocks/*.md (16 files)
- [x] ch03_interfaces/*.md (5 files)
- [x] ch04_registers/*.md (2 files)
- [x] ch05_programming/*.md (4 files)
- [x] ch06_configuration/*.md (1 file)

---

### Phase 5: Add Figure Numbers to Diagrams - COMPLETED

**Required Format:** Use `### Figure N: Title` before each mermaid/image block.

**Implementation:** Used automated script to add figure headings before diagrams.

**Results:**
- **27 figure numbers added** across 14 markdown files
- Captions derived from section headers or image alt text
- Numbering restarts at 1 for each document

**Files updated:**
- ch01_overview/01_architecture.md (5 figures)
- ch02_blocks/01_stream_core.md (3 figures)
- ch02_blocks/04_scheduler.md (4 figures)
- ch02_blocks/06_axi_read_engine.md (2 figures)
- ch02_blocks/07_stream_alloc_ctrl.md (1 figure)
- ch02_blocks/08_sram_controller.md (1 figure)
- ch02_blocks/09_sram_controller_unit.md (1 figure)
- ch02_blocks/10_stream_latency_bridge.md (1 figure)
- ch02_blocks/11_stream_drain_ctrl.md (1 figure)
- ch02_blocks/12_axi_write_engine.md (3 figures)
- ch02_blocks/13_apbtodescr.md (2 figures)
- ch02_blocks/14_apb_config.md (1 figure)
- ch02_blocks/15_perf_profiler.md (1 figure)
- ch02_blocks/16_monbus_axil_group.md (1 figure)

---

### Phase 6: Add Per-Block Revision History - COMPLETED

**Required Format:** Add revision history table at end of each block document.

**Implementation:** Used automated script to add revision history section to all block documents.

**Results:**
- **21 revision histories added** across ch01_overview, ch02_blocks, and ch03_interfaces
- Each includes Version, Date, Author, Description table
- Initial version 0.90 (2025-11-22) and current 0.91 (2026-01-02)
- Caption and Last Updated footer included

**Files updated:**
- ch01_overview/*.md (2 files)
- ch02_blocks/*.md (16 files)
- ch03_interfaces/*.md (3 files)

**Template used:**
```markdown
---

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 0.90 | 2025-11-22 | seang | Initial block specification |
| 0.91 | 2026-01-02 | seang | Added table captions and figure numbers |

: {Block Name} Revision History

---

**Last Updated:** 2026-01-02
```

---

### Phase 7: Add Waveform Numbers to Timing Diagrams - COMPLETED

**Status:** Added waveform headings to 13 wavedrom timing diagrams.

**Implementation:** Changed wavedrom SVG references from `### Figure N:` to `#### Waveform X.Y.Z:` format:

**Files updated:**
- ch02_blocks/01_stream_core.md:
  - Waveform 2.1.1: STREAM Core Data Flow
- ch02_blocks/05_descriptor_engine.md:
  - Waveform 2.5.1: Descriptor Engine APB Basic Kick-off
- ch02_blocks/06_axi_read_engine.md:
  - Waveform 2.6.1: AXI Read Engine - Perfect Streaming
  - Waveform 2.6.2: Datapath Read - Multi-Channel
- ch02_blocks/08_sram_controller.md:
  - Waveform 2.8.1: SRAM Controller Write/Read Operation
- ch02_blocks/10_stream_latency_bridge.md:
  - Waveform 2.10.1: Stream Latency Bridge Backpressure
- ch02_blocks/12_axi_write_engine.md:
  - Waveform 2.12.1: AXI Write Engine - Perfect Streaming
  - Waveform 2.12.2: Datapath Write - Multi-Channel
- ch02_blocks/13_apbtodescr.md:
  - Waveform 2.13.1: APB Normal Write Sequence
  - Waveform 2.13.2: APB Write with Backpressure
  - Waveform 2.13.3: Channel 0 Kick-off
  - Waveform 2.13.4: Channel 7 Kick-off
  - Waveform 2.13.5: Multi-Channel Kick-off Sequence

**Note:** Format follows Q32 pattern: `#### Waveform {chapter}.{section}.{num}: Title`

---

### Phase 8: Update YAML Styles for All Lists

**File:** `stream_spec/stream_styles.yaml`

Ensure `lists` section has all three enabled:
```yaml
# List of Tables/Figures/Waveforms (inserted after TOC)
lists:
  lot: true    # List of Tables
  lof: true    # List of Figures
  low: true    # List of Waveforms
```

**Already Updated:** This change has been applied.

---

## Implementation Order

1. **md_to_docx.py** - Fix title page layout (keeps all on one page), add LoW support
2. **stream_styles.yaml** - Enable LoT, LoF, AND LoW
3. **Create front matter** - ch00_front_matter/00_document_info.md
4. **Update index** - Add front matter link
5. **Add table captions** - All markdown files (`: Caption` syntax)
6. **Add figure numbers** - All diagrams (`### Figure N: Title`)
7. **Add waveform numbers** - All timing diagrams (`#### Waveform X.Y.Z: Title`)
8. **Add revision histories** - All block documents
9. **Test build** - `make clean && make pdf`

---

## Validation Checklist

After all changes:

- [x] Title page shows logo, company, title, subtitle, date on ONE page
- [x] List of Figures has entries (not empty) - 18 figures with hierarchical numbering
- [x] List of Tables has entries (not empty) - 447 table captions
- [x] List of Waveforms has entries - 13 waveforms with hierarchical numbering
- [x] Page numbers appear in footer ("Page X of Y")
- [x] TOC entries are correct
- [x] All figures numbered with hierarchical format (X.Y.Z) - 18 figures across 12 files
- [x] All tables have captions - 447 captions across 29 files
- [x] All waveforms numbered with hierarchical format (X.Y.Z) - 13 waveforms across 7 files
- [x] Front matter section appears after TOC
- [x] Revision history present in document info and each block - 21 block revision histories
- [x] List entries are clickable with page numbers (bookmarks + PAGEREF fields)

---

## Future Propagation

Once STREAM is clean, propagate to other components:

1. **RAPIDS** - `projects/components/rapids/docs/`
2. **Bridge** - `projects/components/bridge/docs/`
3. **APB HPET** - `projects/components/apb_hpet/docs/`

Each will need:
- Similar front matter structure
- Table captions added (`: Caption` syntax)
- Figure numbers added (`### Figure N: Title`)
- Waveform numbers added (`#### Waveform X.Y.Z: Title`)
- Per-block revision histories
- Styles YAML adapted (with `low: true` if waveforms exist)
- Makefile for building

---

## Quick Reference: Pandoc Caption Syntax

### Tables
```markdown
| Col1 | Col2 |
|------|------|
| A    | B    |

: This is the table caption
```

### Figures (with mermaid)
```markdown
### Figure 1: Architecture Overview

```mermaid
flowchart LR
    A --> B
```
```

### Figures (with images)
```markdown
### Figure 2: Block Diagram

![Block Diagram](assets/images/block_diagram.png)
```

### Waveforms (hierarchical numbering)
```markdown
#### Waveform 3.1.1: AXI Read Basic Timing

```wavedrom
{signal: [
  {name: 'clk', wave: 'p....'},
  {name: 'arvalid', wave: '01..0'},
  {name: 'arready', wave: '1....'}
]}
```

#### Waveform 3.1.2: AXI Read with Wait States

```wavedrom
{signal: [...]}
```
```

**Naming Convention:**
- `X.Y.Z` where X=chapter, Y=section, Z=waveform number
- Restart Z at 1 for each new section
- Example: `3.2.1` = Chapter 3, Section 2, Waveform 1

---

**Document Version:** 1.3 (All phases completed + clickable lists + all 13 waveforms integrated)
**Last Updated:** 2026-01-03
