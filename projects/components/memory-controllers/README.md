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

# Memory Controllers

Unified parameterized memory-controller families. Each family combines a
`DDR` and `LPDDR` generation (which share contemporary process node and
JEDEC era) into a single controller engine with a swappable command encoder.

## Families

Each IP carries an igneous-rock codename (felsic/light -> mafic/dense, tracking
generation and capability). The codename is the RTL identifier prefix, the
directory name and the module/package prefix.

| Directory | Codename | Controller scope | DFI | RTL prefix | Status |
|---|---|---|---|---|---|
| [`pumice-ddr2-lpddr2/`](pumice-ddr2-lpddr2/) | **pumice** | DDR2 + LPDDR2 unified | v2.1 | `pumice_*` | Built and board-validated on the Nexys A7 |
| [`ddr3-lpddr3/`](ddr3-lpddr3/) | scoria | DDR3 + LPDDR3 unified | v3.1 | `scoria_*` | Planned; structure only |
| [`ddr4-lpddr4/`](ddr4-lpddr4/) | andesite | DDR4 + LPDDR4 unified | v4.0 | `andesite_*` | Planned; structure only |
| (planned) | basalt | DDR5 | | `basalt_*` | Not started |
| (planned) | gabbro | DDR6 | | `gabbro_*` | Not started |

`basalt` and `gabbro` are the same magma chemistry (gabbro being the coarser,
intrusive form) -- apt for two adjacent generations; `andesite` is the
intermediate composition, i.e. the middle of the DDR2-6 range. **pumice** was
formerly `ddr2-lpddr2` / `ddr2_lpddr2_*`: only the compound IP identifier was
renamed, so the protocol words `DDR2` / `LPDDR2` still appear in comments,
memtype config and timing docs.

Per-IP detail is in each directory's `CLAUDE.md` and `PRD.md`; the DDR3/DDR4
mode roadmap is `vault/Tasks/memory-controllers/ADVANCED_MODES_ROADMAP.md`.

See [`../dmas/stream/README.md`](../dmas/stream/README.md) for the per-component
layout convention this directory follows.
