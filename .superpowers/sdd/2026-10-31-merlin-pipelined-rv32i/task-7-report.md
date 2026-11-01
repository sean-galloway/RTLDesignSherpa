# Task 7 Report: GTKW + Doc Skeletons + Vault Closeout

**Status:** complete  
**Date:** 2026-11-01

## Deliverables

1. **GTKW save file**
   - Path: `projects/components/riscv-ip/merlin-rv32i/dv/tests/GTKW/merlin_tb_top/merlin_tb_top.gtkw`
   - Groups: halt, fetch, pipeline-regs, hazard, ex-branch, data-memory, regfile-write, retire-rvfi.
   - 83 signal names cross-checked against a real `WAVES=1` FST dump using `fst2vcd` and a Python header parser.

2. **Documentation skeletons**
   - `projects/components/riscv-ip/merlin-rv32i/docs/merlin_has/` — index + front matter + 6 chapter directories.
   - `projects/components/riscv-ip/merlin-rv32i/docs/merlin_mas/` — index + front matter + 6 chapter directories, including hazard/forwarding, branch flush, and load-use interlock chapters with GTKW waveform placeholders.

3. **Vault closeout**
   - `git mv` TASK-001 from `open/` to `closed/`.
   - Updated lane `INDEX.md` and area `INDEX.md` counts.
   - Added closure notes to `TASK-001.md`.

## Verification

- `WAVES=1 python -m pytest test_merlin_core.py -q -k focus` → 2 passed.
- `fst2vcd -e .../dump.fst > /tmp/merlin_hdr.vcd` generated header.
- Python cross-check: all 83 GTKW signals found in VCD header.
- `bin/check_broken_links.py --ratchet` → PASS (0 broken, 2 fewer than baseline).
- `bin/check_task_ids.py` → passed (138 areas).
- `bin/filelist_registry.py --check` → PASS (merlin-rv32i 6/6 covered).

## Commit

- Staged only Task 7 files.
- Commit hash: `08aabc33d`

## Concerns

- None. Full HAS/MAS book prose and waveform figures are explicitly a follow-on task.
