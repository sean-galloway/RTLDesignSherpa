# TASK-021: cocotb-framework's __version__ is a hand-maintained literal that drifts from pyproject

**Priority:** P3
**Status:** CLOSED 2026-09-30 -- option 2 implemented in RTLDesignSherpa-DV
`4713ef8`, with the guard live in CI.
**Owner:** TBD
**Filed:** 2026-09-30 (found while releasing cocotb-framework 0.6.8)

RTLDesignSherpa-DV holds its version in **two unlinked places**:

    pyproject.toml            [project] version = "0.6.8"
    src/CocoTBFramework/__init__.py   __version__ = "0.6.8"

Nothing keeps them in step, and they had drifted for **six releases**. Measured
2026-09-30 in the installed wheel: the published **0.6.7** shipped
`__version__ = "0.6.1"` while its own `METADATA` said `Version: 0.6.7`.

**Why it matters more than a cosmetic mismatch.** `CocoTBFramework.__version__`
is the natural thing to check after an upgrade -- it is what a session reaches
for to confirm a reinstall took effect -- and it was returning a version three
releases stale. Any verification built on it silently passed or silently failed
for the wrong reason.

**What was already done, and what it did not fix.** The literal was corrected to
0.6.8 in the release commit (RTLDesignSherpa-DV `fa11027`), and the published
0.6.8 wheel now self-reports correctly -- verified in a throwaway venv with
`__version__` and metadata both reading 0.6.8. That fixed the **value**, not the
**mechanism**: it drifts again at the next rev unless the two are linked.

## Options

1. **`__init__.py` reads the installed metadata.**
   `from importlib.metadata import version; __version__ = version("cocotb-framework")`.
   Single source becomes `pyproject.toml`. Caveat: raises `PackageNotFoundError`
   for a source tree that is not installed, so it needs a fallback -- and this
   repo is imported from a source tree routinely (tests resolve against `src/`).
2. **setuptools dynamic version** -- `dynamic = ["version"]` plus
   `[tool.setuptools.dynamic] version = {attr = "CocoTBFramework.__version__"}`.
   Single source becomes the literal in `__init__.py`. Works in a source tree,
   needs no fallback, and keeps `pip`-visible metadata derived rather than typed.

**Recommend option 2.** It removes the duplicate without adding an import-time
dependency on install state, which matters because the DV repo's own tests run
against `src/` rather than an installed copy.

## Acceptance

- One source of truth: changing the version in one place changes what both
  `pip show` and `CocoTBFramework.__version__` report.
- A guard that fails when they disagree. Cheapest is a unit test in
  `tests/unit` asserting
  `CocoTBFramework.__version__ == importlib.metadata.version("cocotb-framework")`
  when the package is installed.
- **Note the guard is inert until RDS-DV CI actually runs its tests.** That repo's
  `ci.yml` is `ruff check src/`, a "Verify imports" step and `python -m build`,
  with zero pytest references despite 293 test files and `testpaths` configured.
  Tracked as the blocker on RDS-DV issue #82; a version guard added before that
  lands would never execute in CI.

## Where the work happens

The change is in **RTLDesignSherpa-DV**, not this repo. Filed here because the
tooling area already tracks DV-side items -- see tooling TASK-003 (the arbiter
BFM gaps, fixed in DV `784f905`), BUG-007 and BUG-012.

## References

- RTLDesignSherpa-DV `fa11027` -- the 0.6.8 release; corrected the literal
- RTLDesignSherpa-DV `src/CocoTBFramework/__init__.py:3` and `pyproject.toml:7`
- RDS-DV issue #82 -- the CI-pytest gap that gates the guard
- [[TASK-020]] -- the other loose end from the same release

## Closed 2026-09-30

Option 2, as recommended. RTLDesignSherpa-DV `4713ef8`:

- `pyproject.toml` -- `[project] version = "0.6.8"` replaced by
  `dynamic = ["version"]`, plus
  `[tool.setuptools.dynamic] version = {attr = "CocoTBFramework.__version__"}`.
  The module literal is now the single source and pip metadata is derived.
- `tests/unit/test_version_single_source.py` -- 5 tests.
- `.github/workflows/ci.yml` -- a `unit-tests` job, which is what made the guard
  more than decoration.

**The guard is live, not inert.** That was the stated risk in the acceptance
criteria above and it had to be measured rather than assumed. Run 36781772567 on
`4713ef8`: `Unit tests: success`, **1509 passed with zero skips** -- so
`test_installed_metadata_matches_the_module`, which skips unless the installed
distribution is this tree, genuinely executed. A skip count of 1 there would have
meant the end-to-end half never ran.

**Mutation-tested four ways, all caught:**

| Mutation | Caught by |
| --- | --- |
| a literal `version = "0.6.9"` replaces `dynamic` | 2 tests |
| a literal added *alongside* `dynamic` (the sneaky form -- it looks harmless) | `test_project_has_no_literal_version` |
| `dynamic` points at a different attr | `test_dynamic_points_at_the_module_literal` |
| `__version__` set to `"dev"` | `test_module_version_is_a_sane_literal` |

The fourth needed care and nearly recorded a false negative. Run from the DV tree
it PASSED, which looks like a toothless guard; it is not. Imports were resolving
to a stale snapshot in that tree's venv rather than to `src/`, so the mutation was
never under test. With `src/` actually on the path -- what CI's editable install
gives -- it fails as it should. That measurement artifact is its own finding and is
filed as [[TASK-023]].

Also settled while verifying this: the venv `env_python` activates for THIS repo
reports 0.6.8 from both `pip` metadata and `__version__`, so the owner's swap-in
of the published wheel is correct and consistent.
