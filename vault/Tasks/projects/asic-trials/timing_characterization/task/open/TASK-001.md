# TASK-001: Parameter Sweep Automation Scripts

> Migrated 2026-09-25 from
> `projects/asic-trials/timing_characterization/TASKS.md` as **TASK-001**
> (tooling TOOL-001), ID unchanged. That checklist recorded "9 task blocks";
> the file actually held FOUR. Classified against the tree, not the Status line.


**PARTIALLY DONE -- measured 2026-09-25, premise corrected.** The named files
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

**Status:** Planned
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
