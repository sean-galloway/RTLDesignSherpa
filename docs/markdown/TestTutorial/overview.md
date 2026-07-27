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

# Testing Tutorial

**Framework:** `bin/TBClasses/` (shared) plus the CocoTB BFMs from the separate
RTLDesignSherpa-DV repository, editable-installed into the venv
**Tests:** `val/<area>/` for library RTL, `projects/components/<name>/dv/tests/`
for component projects

How verification works in this repository, taught rather than catalogued. The
other books describe hardware; this one describes the Python that drives it.

**Full catalogue:** [index.md](index.md)

## Start here

[The tutorial itself](index.md) is a single long document meant to be read in
order, not sampled. It goes from a first CocoTB test through the framework's
architecture to regression automation and debugging. If you have never written
a CocoTB test, start at
[Quick Start Guide](index.md#quick-start-guide) and keep going.

| Jump to | Covers |
|---------|--------|
| [Quick Start Guide](index.md#quick-start-guide) | Getting a first test running |
| [CocoTB Fundamentals](index.md#cocotb-fundamentals) | Coroutines, triggers, the simulator boundary |
| [Test Framework Architecture](index.md#test-framework-architecture) | How `TBBase`, the BFMs and the scoreboards fit |
| [Writing Your First Test](index.md#writing-your-first-test) | A worked example end to end |
| [Advanced Testing Patterns](index.md#advanced-testing-patterns) | Randomization, coverage, multi-interface tests |
| [Debugging and Analysis](index.md#debugging-and-analysis) | Waveforms, logs, and what to do when a test hangs |

Then the deeper pages, in the order they become useful:

| Page | When you need it |
|---|---|
| [Building Custom Test Classes](custom_classes.md) | Your DUT has no existing TB class |
| [GAXI Field Configuration](gaxi_field_configuration.md) | Driving a multi-field GAXI interface |
| [GAXI Multi-Field Integration](gaxi_multi_field_integration.md) | Several fields across several interfaces |
| [AMBA Protocol Testing](amba_testing.md) | AXI4, AXI-Lite, APB, AXI-Stream |
| [System Level Testing](system_testing.md) | Integrated designs rather than one module |
| [Advanced Examples](advanced_examples.md) | Patterns worth copying |
| [WaveDrom Example](wavedrom_gaxi_example.md) | Turning a run into a timing diagram |

## Two rules that are not negotiable

**Where a TB class lives is determined by who uses it.** A class used by more
than one project belongs in `bin/TBClasses/`; a class used by exactly one
project belongs in that project's `dv/tbclasses/`. Putting a project-specific
class in the shared framework is the most common structural mistake here, and it
is enforced in `/GLOBAL_REQUIREMENTS.md`, not merely recommended.

**Every TB class implements three methods** — `setup_clocks_and_reset`,
`assert_reset`, `deassert_reset`. Tests rely on all three existing regardless of
which class they were handed.

There are also two different test *shapes* — the direct `@cocotb.test()` form
used under `val/`, and the `cocotb_test_*` plus pytest-wrapper form required
under `projects/components/`. Mixing them in one file does not work. The repo
guide has the decision table.

## A caution about these pages

Tutorials date faster than reference pages, and this one predates several
framework changes. Where a snippet disagrees with a working test under `val/`,
**the working test is right.** Read one alongside the tutorial rather than
trusting the tutorial alone.

## Related

- [Scripts](../Scripts/overview.md) — the tools that run and post-process these tests
- [rtl-common](../rtl-common/overview.md) — the modules most of the example tests drive
