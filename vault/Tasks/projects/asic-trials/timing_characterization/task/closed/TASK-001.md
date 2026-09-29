# TASK-001: Parameter Sweep Automation Scripts

> Migrated 2026-09-25 from
> `projects/asic-trials/timing_characterization/TASKS.md` as **TASK-001**
> (tooling TOOL-001), ID unchanged. That checklist recorded "9 task blocks";
> the file actually held FOUR. Classified against the tree, not the Status line.


**PARTIALLY DONE -- measured 2026-09-25, premise corrected.** (Finished 2026-09-29; see the close note at the end.) The named files
(`bin/syn_sweep_vivado.tcl`, `bin/syn_sweep_quartus.tcl`,
`bin/parse_timing_report.py`) do not exist, but three differently-named scripts
satisfy most of the criteria:

| Criterion | State |
|---|---|
| Vivado batch sweep | DONE -- `fpga/Makefile` `bitstream-sweep` loops FREQS_MHZ and emits CSV |
| Timing report parser | DONE -- `fpga/tools/parse_timing_sweep.py` (slack/WNS, utilization) |
| CSV/JSON output | DONE -- `reports/sweep_wns.csv`; `work/timing_char_sweep.py` writes ASAP7 CSV |
| Quartus batch sweep | NOT DONE -- Quartus appears only in prose and in `char_top.sdc` (multi-flow SDC); no Tcl, no flow |
| Example sweep config file | NOT DONE -- none found |

So this is Quartus support plus an example config, not the whole task.

**Status:** CLOSED 2026-09-29 (done)
**Priority:** P1 (High)
**Effort:** 1-2 days

**Description:**
Create scripts in `bin/` to automate synthesis parameter sweeps and parse
timing reports into structured results.

**Acceptance Criteria:**
- [ ] Vivado batch sweep script (Tcl)
- [ ] Quartus batch sweep script (Tcl)
- [ ] Timing report parser (Python) extracting slack, data path delay, logic levels
- [ ] CSV/JSON output for downstream analysis
- [ ] Example sweep configuration file

**Files:**
- `bin/syn_sweep_vivado.tcl` (to be created)
- `bin/syn_sweep_quartus.tcl` (to be created)
- `bin/parse_timing_report.py` (to be created)

---

---

## CLOSED 2026-09-29 -- Quartus sweep built and RUN; both open criteria met

The two criteria the 2026-09-25 measurement left open, plus what building
them turned up:

**Quartus batch sweep** -- `fpga/quartus/syn_sweep_quartus.tcl`, driven by
`cd fpga && make quartus-sweep` (`QUARTUS_SH`, `QUARTUS_CFG`, `FREQS_MHZ`).
One fresh project per frequency (map, fit, sta; no assembler), compiling
`char_top` itself under the SAME multi-flow SDC as the ASIC and Vivado flows
(`FLOW "quartus"` through a generated 6-line wrapper), then
`fpga/quartus/sta_reports.tcl` writes `fub_slack.csv`: per FUB the worst
register-to-register setup path launched from its flops -- slack, data-path
delay, LOGIC LEVELS -- plus a `<fub>.io` row and a `design` row. That is the
"slack, data path delay, logic levels" the original acceptance criterion asked
of the parser, now produced by the Timing Analyzer rather than scraped.
`-dry-run` prints the plan under plain tclsh (`make quartus-sweep-dry`) for a
machine without Quartus.

**Example sweep config** -- `fpga/quartus/sweep_config.example.tcl`, every
key documented with its default (device, frequencies, top, filelist, master
SDC, parameter overrides, I/O split, fitter effort/seed, virtual pins, output
dirs).

**Run for real** on Quartus Prime Lite 24.1std, Cyclone V GX 5CGXFC5C6F27C7,
100/150/200/250/300 MHz, 76-88 s per point:
`fpga/reports/quartus/sweep_wns.csv` (115 rows) and per-point summaries are
committed. Reg-to-reg slack at 100 MHz is positive for all nine FUBs
(nand +4.84, inv +7.24, xor +2.94, carry +3.13, mult +1.36, mux +3.55,
queue +2.40, clkdiv +7.45, gray +2.71 ns); the design-worst path at every
point is an output-port path under the 20 % output-delay budget
(-2.38 ns at 100 MHz), exactly the "not meant to close" constraint the SDC
header describes.

**Found on the way, all fixed here:**

1. `rtl/top/char_top.sv`, `nand_chain_top.sv`: Quartus rejects inline
   `for (genvar b = ...)`; the genvar is declared at module scope (legal in
   every flow, elaborates identically). Area DV rerun from `make clean-all`:
   `run-all` passed in every area (top 11/11).
2. `rtl/syn/char_top.sdc`: the Timing Analyzer wants
   `set_clock_uncertainty -to <clk> <value>` (value LAST) and does not
   implement `set_load`; `read_sdc` aborts on the first error and the fitter
   then reports "Can't fit design in device". Both folded into the SDC per
   flow; SYNTHESIS_GUIDE 5.3/5.6 updated.
3. `fpga/tcl/filelist_utils.tcl` did not treat `//` as a comment, and
   `char_top.f` is written with `//` headings -- so the Vivado
   `create_project.tcl` could not have expanded it either. Fixed here;
   `make project` (Vivado) now expands 37 sources. Seven more copies of that
   file across the repo have the same gap: **tooling TASK-019**.
4. `fpga/tools/parse_timing_sweep.py`'s per-clock-group regex had never
   matched a real Vivado report (the Intra Clock Table's 3rd/4th columns are
   endpoint COUNTS, and the scan started mid-header), so every Vivado row
   silently fell back to the design-level group. Fixed and pinned against a
   real report; the fixed parser agrees with the design WNS on all 40
   `rtl/amba/fpga/reports/*/timing_summary.txt`. `--tool quartus` added.
   Tests: `fpga/tools/tests/test_parse_timing_sweep.py`, 7/7, fixtures are
   the real Quartus and Vivado report files, not typed.

Not done, deliberately: the spreadsheet builder still does not ingest the
Quartus CSV (README_FPGA 5.7 already lists that gap for Vivado).
