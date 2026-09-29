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

# Components

Production and tutorial components built on the `rtl/common`, `rtl/amba` and
`rtl/math` libraries: DMA engines, interconnect generators, protocol bridges
and converters, a DDR2/LPDDR2 memory controller, and the retro legacy
peripheral set. Each component is its own area with `rtl/`, `dv/`, `docs/`
and a `CLAUDE.md` of area facts; the method that applies to all of them lives
in the handbook, not here.

This page is a link page (see the doc-placement rule below). The one status
table for this directory is in [index.md](index.md); work items are in the
tracker. Nothing here is a second copy of either.

## Where to go

| You want | Go to |
|---|---|
| The component list with status and spec links | [index.md](index.md) |
| Requirements for the area | [PRD.md](PRD.md) |
| Area facts for agents (layout, traps, TB placement) | [CLAUDE.md](CLAUDE.md) |
| Live work items, per component | [vault/Tasks/INDEX.md](../../vault/Tasks/INDEX.md) |
| Running a regression (`make clean-all` first, always) | [running-regressions](../../vault/handbook/dv/running-regressions.md); this directory's [Makefile](Makefile) drives every component (`make help`) |
| Test structure (Pattern B, `cocotb_test_*`, gate/func/full) | [test-runner](../../vault/handbook/dv/test-runner.md) and the `test-patterns` skill |
| Coverage | [coverage](../../vault/handbook/dv/coverage.md) |
| Filelists (every `.f` in a `filelists/` dir; the registry) | [filelists](../../vault/handbook/design/filelists.md), `bin/filelists.toml` |
| Where a document belongs | [doc-placement](../../vault/handbook/authoring/doc-placement.md) |
| HAS/MAS spec standards and the PDF pipeline | [spec-doc-standards](../../vault/handbook/authoring/spec-doc-standards.md), `bin/DOC_GENERATION.md` |
| Generated RTL: regenerate everything, never hand-edit | [generated-rtl-discipline](../../vault/handbook/design/generated-rtl-discipline.md); `/CLAUDE.md` Rule #0 |
| Reader-facing component pages | [docs/markdown/projects/index.md](../../docs/markdown/projects/index.md) |

## Components

| Component | Entry point |
|---|---|
| apbx-xbar (generated APB crossbars) | [fabric-gen-ip/apbx-xbar/README.md](fabric-gen-ip/apbx-xbar/README.md) |
| bridge (generated AXI4/AXI5/APB/WB4 crossbar bridges) | [fabric-gen-ip/bridge/docs/bridge_has/bridge_has_index.md](fabric-gen-ip/bridge/docs/bridge_has/bridge_has_index.md), [fabric-gen-ip/bridge/CLAUDE.md](fabric-gen-ip/bridge/CLAUDE.md) |
| converters (width and protocol converters) | [utility-ip/converters/README.md](utility-ip/converters/README.md) |
| dma-ip/stream (tutorial scatter-gather DMA) | [dma-ip/stream/README.md](dma-ip/stream/README.md) |
| dma-ip/rapids (DMA with network integration) | [dma-ip/rapids/docs/rapids_beats_mas/rapids_beats_mas_index.md](dma-ip/rapids/docs/rapids_beats_mas/rapids_beats_mas_index.md), [dma-ip/rapids/CLAUDE.md](dma-ip/rapids/CLAUDE.md) |
| mem-ctrl-ip (pumice DDR2/LPDDR2; DDR3 and DDR4 placeholders) | [mem-ctrl-ip/README.md](mem-ctrl-ip/README.md) |
| misc (ROM/RAM wrappers and utilities) | [utility-ip/misc/README.md](utility-ip/misc/README.md) |
| ecc-ip (error-correction IP family; reed-solomon stood up 2026-09-29, references + draft PRD, no RTL yet) | [ecc-ip/README.md](ecc-ip/README.md), [ecc-ip/reed-solomon/README.md](ecc-ip/reed-solomon/README.md) |
| retro_legacy_blocks (HPET, 8259, 8254, RTC, SMBus, PM/ACPI, IOAPIC, GPIO, UART) | [retro_legacy_blocks/README.md](retro_legacy_blocks/README.md) |
| noc-ip/delta, compute-eng-ip/hive | retired 2026-09-27 (see the tracker); moved into their family directories 2026-09-29, contents as they were |

---

**Last Review:** 2026-09-28 (tooling TASK-004: 1,061-line guide reduced to this
link page; the component narratives it duplicated live in each component's
spec, and its status claims dated 2025-10-24 were replaced by index.md and the
tracker)
