# TASK-012: `formal/` has two competing conventions for where sv2v lives

> Migrated 2026-09-27 from `vault/Tasks/tooling/closed.md` as **TOOL-020** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Priority:** P3
**Status:** Closed 2026-09-23 (598b78d9b). Filed and closed the same day -- the
sweep turned out to be mechanical once measured, so holding it open would have
been the TOOL-017 defect again (an entry whose status disagrees with the tree).

All 117 harnesses now read `SV2V      ?= sv2v`. `?=` so an environment or
command-line override can pin a specific binary without editing 117 files;
PATH resolves the default, and env_python sets that from RTLDS_TOOLS_PREFIX
(TOOL-005).

**The first three verification attempts were worthless, which is the part worth
keeping.** I smoke-tested `formal/converters/uart_tx` -- it passed before and
after, and has no SV2V line at all: its recipe is `sby -f *.sby`, and sby drives
sv2v from the .sby file. I was testing a Makefile the sweep never touched, and
the override probes returned 0 hits for that same reason, not because `?=`
failed.

Redone against `formal/amba/apb4_master_stub`, which defines SV2V at line 12 and
expands `$(SV2V)` at line 34: default resolves to `sv2v`; command-line AND
bare-environment overrides both reach the recipe; a forced rebuild (removing the
generated `.v`) invokes sv2v exactly once and passes rc=0, SBY DONE (PASS); and
`SV2V=/nonexistent/sv2v` fails rc=2 with the bogus path in the recipe. So the
variable is load-bearing, not decorative.

Mechanically clean: +117 -117, every file exactly one line swapped, each left
with exactly one definition and its tab-indented recipes intact.
**Owner:** TBD

Found 2026-09-23 while closing TOOL-005, and deliberately NOT folded into it:
TOOL-005 is about `env_python`, and this is 117 formal harness Makefiles.

Three spellings across `formal/`:

    SV2V      := /mnt/data/tools/sv2v     85 files
    SV2V      := sv2v                     31 files
    SV2V := sv2v                           1 file

So a machine whose tools are not at `/mnt/data/tools` runs 31 harnesses and
fails 85, and nothing says which is intended. Nothing in the repo exports
`SV2V`, so the bare-`sv2v` form depends entirely on PATH -- which
`env_python` now sets from `RTLDS_TOOLS_PREFIX` (TOOL-005).

**Fix:** one form, `SV2V ?= sv2v`, letting PATH resolve it and an environment
override win. `?=` rather than `:=` so a caller can pin a specific binary
without editing 117 files. Do it as one mechanical sweep with a lint/formal
smoke run behind it, not file by file.

Not urgent: both forms work on THIS workstation today (the absolute path
exists and `sv2v` is on PATH), which is exactly why it has gone unnoticed.

---
