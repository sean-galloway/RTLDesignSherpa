# TASK-013: bin/GENERATOR_ARCHITECTURE.md: reconcile the 2025-11 walkthroughs against the generator

**Priority:** P3
**Status:** open
**Owner:** bridge session
**Filed:** 2026-09-29 by bridge TASK-012 (placement pass)

`bin/GENERATOR_ARCHITECTURE.md` is the START HERE page in `CLAUDE.md`, and
most of it was written in 2025-11 against a generator that no longer exists in
that form. TASK-012 rewrote the two sections that were provably wrong (build
flow and Makefile targets: the page described a `dv/tests/Makefile
rebuild-all` that is now a four-line include of `make/tests.mk`, and YAML
configs where the tree holds 43 TOML ports files and 42 connectivity CSVs) and
cut the debugging journal (bridge BUG-001). It did NOT re-verify the rest,
and says so in its currency note. Known-stale or unverified:

- "YAML Configuration Format" section: the example is a `.yaml`; configs are
  `.toml` + `_connectivity.csv` (`load_yaml_ports` still exists, nothing uses it).
  Its `prefix: cpu_m_axi_` examples are legal explicit prefixes but are not
  what the shipped `bridge_batch.csv` configs set.
- "Generator Entry Point": `generate_bridge(ports_file, connectivity_file, ...)`
  and `parse_yaml_config()` -- check against `bridge_generator.py`
  (`load_config`, `generate_tests`, the `--bulk` row loop).
- "Component Generators" 1-4: written before `SlaveAdapterGenerator`,
  typed components, the AMBA5 features and the slave address-window validator
  were added; the later-appended sections (Configuration Validation, AMBA5
  Support, Fabric Options) may now contradict the earlier walkthroughs.
- Every remaining "Line N" pointer is a 2025-11 line number.

**Done when:**

- [ ] every code claim on the page (function names, file names, flags,
      formats) is checked against the tree, fixed or deleted -- no line numbers
- [ ] the currency note at the top is removed because it is no longer needed
- [ ] `CLAUDE.md`'s pointer text no longer says "under reconciliation"
