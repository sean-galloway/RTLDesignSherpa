# TASK-013: bin/GENERATOR_ARCHITECTURE.md: reconcile the 2025-11 walkthroughs against the generator

**Priority:** P3
**Status:** CLOSED 2026-09-29 (done)
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

---

## CLOSED 2026-09-29 -- rewritten against the tree; every named thing checked

`bin/GENERATOR_ARCHITECTURE.md` is 434 lines, of which only the AMBA5 and
Fabric Options sections survive from before (both re-verified; three claims
in AMBA5 corrected: `mte` is connectivity-gated, not phased-out;
`AXI5_PHASED_FEATURES` is empty; the unit suite collects 123 tests, not 52).
Everything else was rewritten from `bridge_generator.py`, `config_loader.py`,
`config_validator.py`, `config.py`, the four generators, `components/`, the
Jinja templates and two generated bridges (`bridge_1x2_rd`, `bridge_1x3_rd`).

What the old page got wrong and the new one states from the code:

- Entry point: `generate_bridge()` returns `(success, [(variant, is_mon)])`
  and emits one directory per `[bridge].variants` entry via
  `_emit_bridge_variant()`; there was no `parse_yaml_config()` and no
  `(bool, str)` return.
- Configuration: TOML ports + connectivity CSV (43 + 42 files; legacy
  `ports.csv` is rejected). The `[bridge]` and port key tables list exactly
  the keys `config_loader.py` reads. The subtractive catch-all slave is added
  by the loader, not by the config.
- Package: there is NO always-64-bit internal path. `PackageGenerator` emits
  one `w`/`r` struct pair per data width present (`axi4_r_32b_t`,
  `axi4_r_64b_t`, ...), and the master adapter carries one struct path per
  connected slave width (adapter-first, converted once) -- shown from
  `bridge_1x3_rd`.
- Names: `<prefix><channel><signal>` from `SignalNaming`; the page no longer
  shows `cpu_m_axi_*` anywhere.
- Validation: lives in `config_validator.py` (function table), not a
  `validate_slave_config()` in the loader; there are no Jinja `min`/`max`
  globals (the only Jinja global anywhere is `range` in the cfg RDL
  renderer).
- Components: seven typed classes, not four (`Axi4ToAxilShim`, `Axi4ToWb4Shim`,
  `MonitoredWrapper` added); the slave adapter generator, the CDC stage, the
  bridge-id FIFO/CAM tracking and the monitored variant were absent.
- No line numbers remain.

Mechanical checks on the finished page: every backticked file path resolves
in the tree (the three non-hits are an ellipsis, a MAS-relative path and the
rejected `ports.csv` format); every backticked `function()` / `Class` exists
in `bridge_generator.py` or `bridge_pkg/`; `check_broken_links --ratchet`
PASS; `check_doc_examples` unchanged at 7. `CLAUDE.md`'s pointer no longer
says "under reconciliation".
