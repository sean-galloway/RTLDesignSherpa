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

# RLB Top Specification

**Status:** Written - see [rlb_top_mas_index.md](rlb_top_mas_index.md) for the
chapter list and which planned sections remain unwritten

---

## Overview

This directory holds the specification for `rlb_top`, the integration level of
the Retro Legacy Blocks subsystem. The other nine books in this directory each
describe one peripheral; this one describes what holds them together.

That distinction is the reason this book exists. Three things live only at the
top and appear in no per-block book:

- the 1-to-10 APB crossbar and the ten-window address map
- the interrupt fabric, which routes every block's interrupt onto a
  conventional legacy line and aggregates them for both 8259s and the IOAPIC
- the cascade cross-connect between the master and slave 8259, including the
  IR2 masking that makes it correct

The index is the authoritative table of contents.

### Documentation Structure

**Chapter 1: Overview**
- What the subsystem is, and the block inventory
- Integration architecture and hierarchy
- Clocking and reset, including the CDC parameterisation
- Acronyms and external references

**Chapter 2: Blocks**
- The instantiated submodules and what each contributes

**Chapter 3: Interfaces**
- Parameters, the full port list, and the address decode contract

**Chapter 4: Programming Model**
- Subsystem bring-up order
- The interrupt fabric as a programming surface: 8259 single and cascade
  configuration, IOAPIC redirection entries, boot-interrupt rerouting

**Chapter 5: Registers**
- The window map, and where each block's own register map is documented

### Document Generation

```bash
cd projects/components/retro_legacy_blocks/docs
./generate_mas_pdf.sh --component rlb_top
```

That produces `RLB_TOP_MAS_v1.0.docx` and `RLB_TOP_MAS_v1.0.pdf` in `docs/`.
Omit `--component` to rebuild all ten books.

## References

- **RTL:** [../../rtl/rlb_top/rlb_top.sv](../../rtl/rlb_top/rlb_top.sv)
- **Filelist:** [../../rtl/rlb_top/filelists/rlb_top.f](../../rtl/rlb_top/filelists/rlb_top.f)
- **Tests:** [../../dv/tests/test_rlb_top.py](../../dv/tests/test_rlb_top.py)
- **Testbench:** [../../dv/tbclasses/rlb_top/](../../dv/tbclasses/rlb_top/)
- Per-block specifications: the other nine `*_mas/` directories here

---

**Last Updated:** 2026-09-30
