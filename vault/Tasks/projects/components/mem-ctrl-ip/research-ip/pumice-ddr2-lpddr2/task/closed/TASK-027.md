# TASK-027: finish the LiteDRAM same-harness A/B (it is already ~80% built)

> **Migrated from `PUMICE-026`** on 2026-09-27, when this area's flat
> `closed.md` was split into one file per item to match the rest of the vault.
> The legacy ID is cited throughout the repo -- RTL comments, DV code, handbook
> notes, commit messages and session memory -- so it is NOT rewritten at those
> call sites; `vault/Tasks/MIGRATION_MAP.md` and this line are how an old
> `PUMICE-026` reference resolves. Body below is verbatim from the flat page.
>
> Lane chosen by reading this item's own Status line and opening, not its title:
> a keyword pass over the 35 items misclassified 14 of them.


**Status:** CLOSED 2026-09-10  **Priority:** was P2
**Intent (Sean):** "drop liteddr into the pumice harness so testing is the same."

**START HERE, DO NOT REBUILD:**
`projects/fpga-systems/NexysA7/mem-ctrl-ip/pumice/ddr2-characterization/flows-litedram-uart/`

That flow already exists and is documented as **WIRED** in its `HARNESS_PLAN.md`:

- `rtl/char_engine_harness.sv` — DUT-agnostic harness (engines + perf meters +
  bandwidth timer + harness_csr + UART bridge) exposing an AXI4 master.
  Verilator-lint-clean standalone.
- `rtl/litedram_char_top.sv` — board top: `litedram_core` + the harness on
  `user_clk`, `init_done`-gated, AXI user port wired.
- `rtl/filelists/litedram_char_harness.f`, `constraints/litedram_char.xdc`,
  `tcl/build_all.tcl`, `tcl/program_fpga.tcl`, `Makefile`, `regen.sh`,
  `litedram_hp.yml`, and a generated `build_board/gateware/litedram_core.v`.
- A `litedram_hp.yml` deliberately mapped onto a high-perf pumice preset, with
  the mapping table written out in its README.

**Progress 2026-09-10 (commit fdaa7db37):**
- ~~regen with BIOS~~ **DONE.** Core regenerated with a functional BIOS (63 KB
  ROM) and `litedram_hp.yml` moved to **75 MHz / 1:2 / 300 MT/s**, matching the
  point pumice is measured at. The stock 100 MHz / 1:4 would have voided the
  comparison.
- ~~XDC reconcile~~ **NOT NEEDED.** The regenerated core xdc has no ddram pins;
  the harness keeps its pin map.
- Five flow bugs fixed to get synthesis running: `REPO_ROOT` two levels short
  (the `../` count was correct at the pre-move path), `CONVERTERS_ROOT` not
  exported, the tcl filelist reader expanding only `$REPO_ROOT`, `.vlt` lint
  waivers handed to Vivado, and `VexRiscv.v` pinned to a path inside the LiteX
  venv. `regen.sh` no longer hardcodes a `/tmp` venv either.

**DONE 2026-09-10 — measured.** Timing-clean LiteDRAM bitstream (WNS +0.195, after
adding the core's CRG reset-strobe false path), `--char-profile matrix --char-scale 1000`,
14/14 integrity, saved as `docs/char_results/litedram_2026-09-10_matrix.csv` with the
write-up `FINDINGS_litedram_ab_2026-09-10.md`. Headline: LiteDRAM reads 564-579 MB/s
(94-97% of peak) through the identical harness where pumice reads 291.7; writes equal
(~554-569 vs 551-570). The read ceiling is pumice's, not the operating point's -- see
PUMICE-025. Ready to close (move the block to closed.md).

**Progress 2026-09-10 (later) — item 0 DONE, harness matches build-perf:**
Sean asked for the LiteDRAM harness to match the current one; the chosen
route was to extract a shared engine block. `char_engine_block.sv` (chargen
regs + generator array + crossbars + perf, one AXI4 master) is pulled out of
`ddr2_char_macro.sv`, which now wraps pumice around it; `char_engine_harness.sv`
is build-perf's `ddr2_char_harness` minus the controller (same UART bridge,
same `bridge_ddr2_char_axil` address map with `ddr2_apb` terminated, same
`harness_csr` with BUILD_ID "LDR2", same timer/LEDs). `make lint` clean;
Makefile on `make/fpga_flow.mk`; `host/host_litedram_char.py` is the pumice
host with the pumice-CSR surface as no-ops. `FPGA_CLK_HZ` in the top was still
100 MHz after the 75 MHz regen (UART divisor wrong) -- fixed. Bitstream build
in flight; then program, `--char-profile matrix --char-scale 1000`, save CSV.

**Was BLOCKING (now resolved as above).** Synthesis reached the harness and
stopped on **41 port mismatches**: `char_engine_harness.sv` is wired
to a `harness_csr` that no longer exists. The whole per-generator config
surface (`o_cfg_wr_*`, `o_cfg_rd_*`, the start pulses, the CRC readback) moved
out of `harness_csr` into `chargen_regs` when the char framework went to a
16-generator array; `harness_csr` is now 75 ports of global/PHY config only.

Rewire `char_engine_harness.sv` against the current framework — `harness_csr`
for the global surface, `chargen_regs` (`chargen_regs.rdl`) for per-generator
config, and the generator array instead of one wr + one rd engine. The pumice
flow's `ddr2_char_macro.sv` is the reference for how the array is driven today.

Then: host variant (copy `ddr2_char.py` + `pumice_master.py`, drop the
pumice-CSR `set_controller_cfg` writes since LiteDRAM self-configures, keep
engine cfg + perf/timer readout; `harness_csr` is at base 0 here), then
`make bitstream && make program && make characterize`.

**RESOLVED 2026-09-10:** `build-litedram/` was an empty duplicate scaffold
(the never-executed destination of a NEXYS-003 move). It cost this session a
rebuild-from-scratch of the LiteX tooling before the real flow surfaced. It is
now DELETED and every reference points at `flows-litedram-uart/`.

**Tooling notes that ARE new and worth keeping** are in
`flows-litedram-uart/2026-09-10_tooling_notes.md`, with two working scripts
beside it (`bin_nexys_bist_soc.py`, `bin_litedram_bist_run.py`): install LiteX
from git not PyPI (PyPI +
Python 3.12 breaks every target on a migen bytecode-inference bug); the RISC-V
toolchain is already at
`/tools/Xilinx/2025.1/gnu/riscv/lin/riscv64-unknown-elf/bin`; PyPI
`pythondata-software-picolibc` ships incomplete sources so the BIOS build
fails; and `--cpu-type=None` yields a clean timing-met bitstream whose BIST
returns garbage because LiteDRAM's DDR2 init and levelling live in the BIOS.
That last point is why item 1 above says `--bios`.

**Why it matters:** LiteDRAM's read is also ~47% of the raw ceiling while its
write reaches 88%; pumice is at 48.6% / 95.0%. Two independent controllers at
the same read fraction on the same board is the strongest evidence that the
read ceiling is a property of this operating point rather than a pumice defect
(PUMICE-025). Same-harness confirmation would redirect or justify that work.

---
