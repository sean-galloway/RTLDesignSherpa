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

# Tooling

**Code:** `bin/` (34 top-level tools plus the `rtl_generators/` framework)
**Shared TB classes:** `bin/TBClasses/`

The scripts that surround the RTL: the generators that write arithmetic modules,
the checkers that gate a commit, the converters that turn simulation output into
diagrams and documentation into Word. Nothing here is simulated or synthesized —
this book is about the machinery, not the hardware.

**Full catalogue:** [index.md](index.md)

## Start here

[The cheat sheet](cheat_sheet.md) covers the tools you will reach for in a
normal session and the arguments that matter. Read it before the per-script
pages; most of those exist to document a script's internals, not its everyday
use.

## What the tools are for

Four groups, and the group tells you when you would run it.

**Generation** — writes RTL you should not write by hand.
[`math_generate.py`](math_generate.md) and the
[`rtl_generators/`](multiplier_mixin.md) framework under it produce most of
`rtl/math/`. The rule that governs all of them: change the generator, delete
every generated file, regenerate the whole set. Partial regeneration produces
mismatched ports and widths that surface as confusing simulation failures rather
than compile errors.

**Checking** — answers "is this commit safe". `filelist_registry.py` is the one
that runs in CI: `--check` proves every module is reachable from a filelist,
`--audit` proves the filelists resolve, `--blindspots` reports what the other
two structurally cannot see. [`lint_wrap.py`](lint_wrap.md) wraps Verilator, and
the `audit_*.py` family checks documentation, parameterization, and the signal
naming conflicts that break AXI factory pattern matching.

**Conversion** — moves information between formats.
[`vcd2wavedrom2.py`](vcd2wavedrom2.md) turns a simulation dump into a WaveDrom
timing diagram; [`md_to_docx.py`](md_to_docx.md) turns this documentation into
Word; [`sv_interface_flattener.py`](sv_interface_flattener.md) unpacks
SystemVerilog interfaces for tools that cannot take them.

**Analysis** — answers questions about a tree you did not write.
[`find_instances_used.py`](find_instances_used.md) finds where a module is
actually instantiated, [`generate_uml.py`](generate_uml.md) draws the class
structure of the testbench framework, and [`pytree.py`](pytree.md) prints a
directory tree filtered to what matters.

## A caution about these pages

The per-script pages document scripts as they were when written, and `bin/`
moves faster than its documentation. Four pages here — `cheat_sheet`,
`update_fst_tracing`, `verilog_class_overview`, `wavedrom_troubleshooting` — are
guides with no single script behind them, and a few document scripts that have
since been renamed or absorbed. **`--help` on the script is the authority; this
book is the explanation.** If the two disagree, the script is right and the page
needs fixing.

## Related

- [TestTutorial](../TestTutorial/overview.md) — how to use the testbench classes
  these tools support
- [rtl-math](../rtl-math/overview.md) — the library `math_generate.py` produces
