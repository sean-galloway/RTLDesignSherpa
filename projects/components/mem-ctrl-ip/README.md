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
generation and capability). The codename is the RTL identifier prefix and the
module/package prefix; the DIRECTORY is the compound `<codename>-<protocols>`
form -- `pumice-ddr2-lpddr2`, not `pumice` and not `ddr2-lpddr2`.

**That compound form is the canonical name for the IP everywhere a directory
names one**: the component directory here, the task area
(`vault/Tasks/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/`) and the knowledge-note mirror. Before
2026-09-28 the three siblings were named three different ways, so a new area had
no way to tell which was intended -- see tooling ISSUE-002. The bare codename is
still how an IP is referred to in prose ("pumice reaches 95% of peak"); it is the
DIRECTORY that takes the compound form.

| Directory | Codename | Controller scope | DFI | RTL prefix | Status |
|---|---|---|---|---|---|
| [`research-ip/pumice-ddr2-lpddr2/`](research-ip/pumice-ddr2-lpddr2/) | **pumice** | DDR2 + LPDDR2 unified | v2.1 | `pumice_*` | Built and board-validated on the Nexys A7 |
| [`research-ip/scoria-ddr3-lpddr3/`](research-ip/scoria-ddr3-lpddr3/) | **scoria** | DDR3 + LPDDR3 unified | v3.1 | `scoria_*` | RTL complete, sim-verified; not board-validated |
| [`research-ip/andesite-ddr4-lpddr4/`](research-ip/andesite-ddr4-lpddr4/) | **andesite** | DDR4 + LPDDR4 unified | v4.0 | `andesite_*` | Planned; structure only |
| (planned) | basalt | DDR5 | | `basalt_*` | Not started |
| (planned) | gabbro | DDR6 | | `gabbro_*` | Not started |

`basalt` and `gabbro` are the same magma chemistry (gabbro being the coarser,
intrusive form) -- apt for two adjacent generations; `andesite` is the
intermediate composition, i.e. the middle of the DDR2-6 range. **pumice** was
formerly `ddr2-lpddr2` / `ddr2_lpddr2_*`: only the compound IP identifier was
renamed, so the protocol words `DDR2` / `LPDDR2` still appear in comments,
memtype config and timing docs.

## Layout (2026-10-09 reorg)

- [`research-ip/`](research-ip/) — the proving-ground
  controllers above, one directory each, as-is.
- [`common-ip/`](common-ip/) — what the three controllers
  currently duplicate (AXI front-end, DFI layers, scheduler/training/storage
  layers) extracted into one parameterized source per layer. Today a skeleton:
  `docs/` plus placeholder `rtl/`/`dv/`; extraction is Phase 2 of
  [the reorg spec](../../../docs/superpowers/specs/2026-10-09-mem-ctrl-ip-reorg-design.md).
- `product-ip/` — appears when the first controller graduates from
  research (board-proven + timing-closed config on the common layers).
  Intentionally absent until then.

Shared family design and doctrine — the `mem_ctrl_pkg` shared-core design,
the family doctrine, the DFI boundary lineage, and the JEDEC generation
deltas — lives in [`common-ip/docs/`](common-ip/docs/); it
is owned by no single controller, and each controller's book references it
rather than restating it. Start at
[`common-ip/docs/INDEX.md`](common-ip/docs/INDEX.md).

Per-IP detail is in each directory's `CLAUDE.md` and `PRD.md`; the DDR3/DDR4
mode roadmap is `vault/Tasks/projects/components/mem-ctrl-ip/memory-controllers/ADVANCED_MODES_ROADMAP.md`.

See [`../dma-ip/stream/README.md`](../dma-ip/stream/README.md) for the per-component
layout convention this directory follows.
