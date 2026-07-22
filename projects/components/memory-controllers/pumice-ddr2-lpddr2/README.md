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

# DDR2 / LPDDR2 Family Memory Controller

Unified parameterized memory controller targeting both DDR2 SDRAM and
LPDDR2 SDRAM via DFI v2.1. One controller engine; the wire-encoding
difference is isolated to a swappable encoder module.

## Status

**Implemented and characterized** — the full controller RTL is in `rtl/`
(`fub/`, `macro/`, `top/`) with cocotb suites under `dv/tests/{fub,macro,top}`.
The design has been brought up on silicon on the Nexys A7 DDR2 board via the
`projects/NexysA7/ddr2-characterization/` UART harness. Published specs:
`docs/DDR2_LPDDR2_HAS_v0.5.pdf` and `docs/DDR2_LPDDR2_MAS_v0.5.pdf`.

## Layout

| Directory | Purpose |
|---|---|
| `bin/` | Build / packaging scripts |
| `coverage_combined/` | Combined coverage reports |
| `coverage_data/` | Raw coverage artifacts from regression |
| `docs/` | Hardware Architecture Spec + companion documents |
| `dv/` | Verification environment (cocotb tests, scoreboards, testbench classes) |
| `regs/` | Register-map sources and generated headers |
| `reports/` | Performance / characterization reports |
| `rtl/` | SystemVerilog implementation (`top/`, `macro/`, `fub/`, `includes/`, `filelists/`) |

## Documents

- `docs/DDR2_LPDDR2_HAS_v0.5.pdf` — current HAS (fully styled)
- `docs/DDR2_LPDDR2_MAS_v0.5.pdf` — current MAS (fully styled)
- `docs/pumice_has/` / `docs/pumice_mas/` — Markdown sources
- `docs/generate_has_pdf.sh` / `docs/generate_mas_pdf.sh` — build scripts

### Build Requirements

The HAS build pipeline requires the following on PATH:

| Tool | Install |
|---|---|
| `python3` ≥ 3.10 | system |
| `pandoc` | `sudo apt-get install pandoc` |
| LibreOffice (`soffice` / `libreoffice`) | `sudo apt-get install libreoffice` |
| `mmdc` (Mermaid CLI) | `npm install -g @mermaid-js/mermaid-cli` |
| Python `python-docx` ≥ 1.0 | `pip install --user python-docx` |
| Python `PyYAML` | `pip install --user PyYAML` |

`python-docx` is **critical** — without it, `md_to_docx.py` silently
skips the title page, corporate styling (forest-green H2, dark-gray H1
backgrounds), and logo placement, producing a plain unstyled PDF. The
build script now checks for it explicitly and fails loudly with a
clear remediation message if it's missing.

On Ubuntu 23.10+ / Debian 12+ (PEP 668 systems), add
`--break-system-packages` to the `pip install` commands.

## See Also

- Parent: [`../README.md`](../README.md)
- Sibling: [`../../dmas/stream/README.md`](../../dmas/stream/README.md) — the layout reference
- Research material (research dirs, oppo, JEDEC links): kept at
  `/mnt/data/github/dfi-specs/pumice/` (local-only working area)
