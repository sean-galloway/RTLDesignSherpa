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

# STREAM Register Definitions

**Purpose:** the PeakRDL-generated register block STREAM's config port exposes,
and the one hand-written file that has to sit beside it. This page is a link
page: the register map itself is the generated documentation, the fields are
the RDL, and the wiring is the RTL that instantiates the block.

## What is here

| Path | What it is | Edit? |
|---|---|---|
| `generated/rtl/stream_regs.sv`, `stream_regs_pkg.sv` | the regblock (`s_cpuif_*` passthrough cpuif in, `hwif_in`/`hwif_out` structs out) | never -- regenerate |
| `generated/docs/stream_regs.md`, `.html` | the register map, field by field | never -- regenerate |
| `generated/stream_regs_regmap.py` | the Python map the DV and host code read registers BY NAME from | never -- regenerate |
| `stream_regs.vlt` | Verilator waiver: PeakRDL's per-field `always_comb` blocks trip a strict MULTIDRIVEN reading; waived for the generated file only. Lives outside `generated/` so a regen cannot erase it | yes |

The source is NOT in this directory: `../rtl/macro/stream_regs.rdl`, which
includes `../rtl/macro/stream_mon_regs.rdl` for the per-monitor block.

## Who uses it

`../rtl/top/stream_config_block.sv` wraps the regblock behind the APB config
port; `../rtl/macro/stream_core.sv` and `../rtl/top/stream_top_ch8.sv`
instantiate it. Look there for the port wiring rather than at an example
here -- an example copied into a README is the copy nobody regenerates, and
this page carried one for months that named ports the block never had.

## Regenerating

Any `.rdl` edit regenerates ALL of `generated/` (root `CLAUDE.md`, Critical
Rule #0), through the repo wrapper and never raw `peakrdl` -- the wrapper is
what also emits the docs and the regmap:

```bash
python3 bin/peakrdl_generate.py projects/components/dmas/stream/rtl/macro/stream_regs.rdl \
    -o projects/components/dmas/stream/regs/generated --no-html
```

then `cd dv/tests && make clean-all && make run-all`. Method:
`vault/handbook/dv/registers-by-name.md` (registers by name, never by offset)
and `vault/handbook/design/generated-rtl-discipline.md`.
