# DDR* IP family codenames

The DDR* memory-controller IPs carry igneous-rock codenames (felsic/light →
mafic/dense, tracking generation/capability). The codename is the RTL identifier
prefix, directory name, and module/package prefix for each IP.

| Codename  | Generation | Directory                              | RTL prefix   |
|-----------|------------|----------------------------------------|--------------|
| **pumice**  | DDR2/LPDDR2 | `memory-controllers/pumice`            | `pumice_*`   |
| scoria    | DDR3/LPDDR3 | `memory-controllers/scoria` (planned)  | `scoria_*`   |
| andesite  | DDR4        | (planned)                              | `andesite_*` |
| basalt    | DDR5        | (planned)                              | `basalt_*`   |
| gabbro    | DDR6        | (planned)                              | `gabbro_*`   |

Notes:
- **pumice** is the first built IP (formerly `ddr2-lpddr2` / `ddr2_lpddr2_*`).
  The `pumice_top` module is a DDR2/LPDDR2 controller; the protocol words
  `DDR2`/`LPDDR2` still appear in comments, memtype config, and timing docs —
  only the compound IP identifier was renamed.
- **basalt → gabbro** (DDR5→DDR6) are the same magma chemistry (gabbro is the
  coarser, intrusive form of basalt) — apt for two adjacent generations.
- **andesite** = intermediate composition = the middle of the DDR2–6 range.

See each IP's `CLAUDE.md` / `PRD.md` for details.
