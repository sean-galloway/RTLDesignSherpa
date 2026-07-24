<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# AMBA tasks — dropped (abandoned / superseded / won't do)

_None._

---

## AMBA-PRD-TASKS — 4 open items removed from rtl/amba/PRD/ (2026-07-24)
**Status:** dropped 2026-07-24 — removed from the RTL tree as believed-stale (Sean)

The `rtl/amba/PRD/` directory was a task tracker living in the RTL tree — a
tasks-convention violation. It held 7 `TASK-*.md`; 3 were ✅ COMPLETE (deleted),
and these 4 were 🔴 Not Started. Removed with the directory. Full text is
recoverable from git (`git log --all -- rtl/amba/PRD/`); pulled back into
`open.md` if any turns out to be live work rather than stale:

- **TASK-017** — wavedrom timing diagrams for the APB monitors
- **TASK-018** — wavedrom timing diagrams for the AXI4 monitors
- **TASK-019** — gaxi tutorial docs
- **TASK-020** — identify wavedrom-diagram candidates
