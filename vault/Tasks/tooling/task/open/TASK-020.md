# TASK-020: pilot cocotb-test 0.3.0, then decide whether cocotb 2.x is reachable

**Priority:** P2
**Status:** open
**Owner:** TBD
**Filed:** 2026-09-30 (from the cocotb 2.x outage the same day)

`requirements.txt` pins `cocotb-test==0.2.5`, uploaded 2024-02-07. That version
does `import cocotb.config`, which cocotb 2.x **removed**. cocotb 2.1.0 is live
on PyPI, so while we sit on 0.2.5 any dependency-resolving install is a landmine:
every `cocotb_test`-based test in the tree then fails at **collection** with

    ModuleNotFoundError: No module named 'cocotb.config'

That error names the test file and never mentions cocotb-test, so it reads as a
broken repo rather than a dependency conflict. It happened on 2026-09-30 -- the
venv went to cocotb 2.1.0 during a `cocotb-framework` install and every
simulation in the tree died until the `rapids` session restored these pins.

**cocotb-test 0.3.0 (2026-09-23) fixes it upstream.** Verified by pulling the
wheel and reading it, not from release notes: `simulator.py` contains **zero**
`cocotb.config` references and instead does
`from cocotb_test.compat import cocotb_2x_or_newer, cocotb_config` -- an explicit
cocotb-2.x compatibility shim. It declares only `cocotb>=1.5`, and the shim means
it should work on cocotb 1.x as well, so **it can be adopted without moving
cocotb at all**.

Already done, so it is not repeated here: RTLDesignSherpa-DV requires
`cocotb-test>=0.3.0` in its `[sim]` extra (commit `2b20629`, still unreleased).
This repo's pins were deliberately left alone pending the pilot below.

## Two questions, in this order

**1. Does cocotb-test 0.3.0 run this tree's suites unchanged, on cocotb 1.9.2?**
This is the low-risk half and needs no cocotb change. Unknown as of filing --
nobody has run it.

**2. Only then: does CocoTBFramework itself work under cocotb 2.x?**
Never tested. cocotb 2.x is a major release whose removals are not limited to
`cocotb.config`, and the framework's core floor is deliberately uncapped
(`cocotb>=1.9.0`) precisely because nobody has established the answer. If this
turns out non-trivial, file it separately rather than growing this task.

## Acceptance

- 0.3.0 exercised against a representative set at a real level -- not just
  collection: `val/amba`, one `fabric-gen-ip/bridge` area and one `dma-ip` area.
- **Baselined on the same seeds against 0.2.5 first.** A dependency change can
  shift BFM timing, and without a baseline the result is unattributable.
- Measured pass counts reported, not `rc=0`. Capture pytest's own exit code, not
  a pipeline's.
- If green: bump `requirements.txt` `cocotb-test` 0.2.5 -> 0.3.0 in a commit that
  carries the measured evidence.
- Question 2 answered, or explicitly filed as its own item.

## Hazards

- **The venv is shared by concurrent sessions.** Swapping cocotb-test under a
  peer breaks their in-flight regressions. Announce it first; on 2026-09-30 an
  unannounced dependency change did exactly that.
- **Install with `--no-deps`.** `cocotb-framework` declares only `cocotb>=1.9.0`,
  so a resolving install can drag cocotb up regardless of intent. Recovery is
  `pip install -r requirements.txt`.
- Verify the environment before trusting any verdict: `pip check` and
  `python3 -c "import cocotb_test.simulator"`. A suite run during a broken window
  is stale evidence.

## References

- `requirements.txt` lines 6-10 (the pins that currently protect the tree)
- RTLDesignSherpa-DV `2b20629` -- the `[sim]` extra requiring `cocotb-test>=0.3.0`
- RTLDesignSherpa `8344e6852` -- `cocotb-framework` pin 0.6.5 -> 0.6.8
- [[TASK-021]] -- the other loose end from the same release
