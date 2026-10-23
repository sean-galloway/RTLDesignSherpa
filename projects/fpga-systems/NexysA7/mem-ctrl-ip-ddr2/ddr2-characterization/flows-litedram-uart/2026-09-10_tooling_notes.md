# LiteDRAM A/B — status, working tooling recipe, and what is still missing

**Date:** 2026-09-10. **Board:** Nexys A7-100T `210292BFA3EE`, MT47H64M16,
75 MHz sys / 1:2 / 300 MT/s. Raw ceiling 600 MB/s (572 MiB/s).

## What the A/B is supposed to be

LiteDRAM dropped into **the pumice char harness** — same AXI pattern
generators, same perf counters, same host program — so the only variable is
the controller. That is what this directory (`FLOW := litedram_char`,
`TOP := litedram_char_top`,
`rtl/filelists/litedram_char_harness.f`) was scaffolded for.

**The scaffold is still empty.** Only `Makefile`, `.gitignore` and this
`results/` exist; there is no `regen.sh`, no `litedram_hp.yml`, no `gen/`, no
harness RTL and no host. Building the like-for-like A/B means writing them.

## Best LiteDRAM numbers we have (NOT like-for-like)

From the 2026-09-06 run, LiteDRAM's **own** BIST driving its **own** user port
— a different generator and a different measurement path from the pumice
harness, so treat it as a reference point and not an A/B:

| | bl8 | bl16 |
|---|---|---|
| LiteDRAM write | 504 MiB/s (528 MB/s) | 475 MiB/s |
| LiteDRAM read | 184 MiB/s (193 MB/s) | 270 MiB/s (283 MB/s) |

Against pumice on 2026-09-10 (its own harness, `open_page`, row_major BL8):
**write 570.0 MB/s, read 291.7 MB/s.** On those numbers pumice is ahead on
both, but the two were not measured through the same path, which is exactly
why the drop-in matters.

The more interesting observation is that **LiteDRAM's read is also about 47%
of the raw ceiling** (270 of 572 MiB/s) while its write reaches 88%. pumice
now sits at 48.6% read / 95.0% write. A mature, widely-deployed controller
hitting the same read fraction on this exact board and device is evidence that
the read ceiling is a property of this operating point rather than a pumice
defect — see pumice BUG-011 (was PUMICE-025).

## Working tooling recipe (2026-09-10) — the part worth keeping

This was re-derived from scratch twice because `/tmp` gets cleared. It now
lives here.

* **Install from GIT, not PyPI.** PyPI `litex`/`litedram` 2024.12 with
  `migen` 0.9.2 does **not** work on Python 3.12: migen's `ClockDomain()`
  infers its name by inspecting caller bytecode, that inference broke, and
  *every* target — including the stock `digilent_nexys4ddr` — dies with
  `Cannot extract clock domain name from code`. Install
  `migen`, `litex`, `litedram`, `litex-boards` from their git repos.
  Also needed: `liteeth`, `litescope`, `litespi`, `litesdcard`,
  `pythondata-cpu-vexriscv`, `meson`, `ninja`.
* **RISC-V toolchain is already on this machine**, no download needed:
  `/tools/Xilinx/2025.1/gnu/riscv/lin/riscv64-unknown-elf/bin`
  (it reports itself as `riscv32-xilinx-elf-gcc 13.3.0`).
* **The BIOS build currently fails**: `pythondata-software-picolibc` from PyPI
  ships an incomplete source tree, so libc compilation dies on a missing
  `libc/ctype/ctype_.c`. Install that package from git too.
* `bin/nexys_bist.py` — the litex-boards `digilent_nexys4ddr` BaseSoC verbatim
  with `with_bist=True` on `add_sdram`. Builds and **meets timing**.
* `bin/litedram_bist_run.py` — drives the BIST CSRs over `litex_server`.

## The trap: no CPU means no DRAM

Building with `--cpu-type=None --uart-name=uartbone` produces a clean,
timing-met bitstream and lets a host reach the BIST registers without any
software stack. **It does not work.** The BIST returns in 1-21 ticks with
rising error counts, because LiteDRAM's DDR2 bring-up — initialisation, write
levelling, read levelling — is done by its **BIOS**, and with no CPU it never
runs. The DRAM is simply uninitialised.

So a CPU-less LiteDRAM needs the standalone-core generator (`litedram_gen`),
whose core embeds its own init sequencer, rather than the SoC path. That is
also the right shape for the harness drop-in, since the harness wants a core
with a user port, not a SoC.

## Next step

`litedram_gen` a standalone DDR2 core (AXI or native user port, built-in init)
against this board's pin-out, wrap it as `litedram_char_top` behind the same
AXI the pumice harness drives, and reuse the existing generators, perf
counters and host program unchanged. Tracked as pumice TASK-027 (was PUMICE-026).

---

## Recipe corrections (2026-09-30, from standing up a DDR3 reference core)

The recipe above was re-derived once more, for
`projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/bin/regen_litedram_ddr3_ref.sh`
(a DDR3 core generated to be READ, as reference for the scoria HAS). Three
things it did not say, each of which cost an attempt:

* **The Python 3.10 pin is about PyPI, not about Python.** migen installed
  **from git** infers `ClockDomain` names correctly on Python 3.12 --
  verified directly: `ClockDomain().name == 'cd'`. Only PyPI migen 0.9.2 is
  broken. A 3.12 venv with git installs is sufficient, and the
  `litex-venv310` name is misleading about why it worked.

* **`--no-compile-software` does NOT avoid the software dependencies.**
  `litedram_gen` imports `pythondata-software-picolibc` *and*
  `pythondata-software-compiler_rt` at module load regardless of the flag, and
  dies on either being absent. Both must be installed (from git) even for a
  generate-only run that builds no BIOS. The note above mentions picolibc as a
  BIOS-build problem; it is actually an import-time problem.

* **Run the generator from a directory that does NOT contain the clones.**
  With the cwd inside the checkout tree, `import migen` / `import litex`
  resolve to the clone ROOTS as namespace packages rather than to the
  installed packages, and generation fails with
  `NameError: name 'Signal' is not defined` from inside
  `litex/gen/signal.py`. Nothing is wrong with the install, and the error
  points nowhere near the cause. `regen_litedram_ddr3_ref.sh` cds to a scratch
  directory for exactly this reason.

Generation is reproducible modulo the timestamp: two runs of the same config
differ in 12 lines, all of them the date header and build ids.


## 2026-10-22: the SIM core, with its BIOS, for the cocotb perf proxy

`ddr2_char_framework/dv/tests/test_litedram_char_perf.py` runs the same
injectors / observers / host program as the pumice and granite proxies
against `gen/sim/gateware/litedram_core_sim.v` (LiteDRAMCore +
SDRAMPHYModel). That core must carry the BIOS or it never raises
`init_done` (the VexRiscv runs nothing, the DFI stays under software
control). What it took, in order:

* `pip install meson ninja` into the LiteX venv (`/mnt/data/tools/litex-venv`
  today; `LITEX_VENV` overrides). The BIOS build calls meson.
* The RISC-V gcc is Xilinx's: `PATH=/tools/Xilinx/2025.1/gnu/riscv/lin/riscv64-unknown-elf/bin:$PATH`.
* **litex 2026.8 / litedram 2026.8 cannot compile the BIOS for a `--sim`
  core as shipped**: `liblitedram/sdram.c` uses `SDRAM_PHY_DELAYS`
  unguarded in the read-leveling scan, and `litedram/init.py` only emits
  that define from `phy_settings.delays`, which SDRAMPHYModel lacks. The
  venv's `sdram.c` carries a four-line guard (`#ifndef SDRAM_PHY_DELAYS
  / #define SDRAM_PHY_DELAYS 1`) after its includes, commented with this
  date. A fresh venv needs it again; upstream is the right place for it.
* Two more venv patches, both in `litedram/gen.py` and both gated on
  `isinstance(platform, SimPlatform)` so the board core is untouched:
  the BIOS console runs at `clk/2` baud in simulation (the BIOS blocks on
  its UART while printing; at 115200 the banner alone is ~100 ms of sim
  time), and `SDRAM_TEST_DISABLE` is added as a constant (the BIOS memtest
  and memspeed over 2 MiB of modelled DRAM through the CPU port are tens of
  millions of cycles; the first smoke ran 118 ms of sim time, 8.85 M cycles,
  without reaching `init_done`). Originals are beside the patched files'
  scratch copies of that session; a fresh venv needs both again.
* The generated verilog instantiates `VexRiscv` by name; `regen.sh` now
  copies `VexRiscv.v` (standard variant) from pythondata beside the sim
  core so a filelist can name it. The core's `$readmemh` paths are bare
  file names: the perf test copies both `.init` files into its sim build
  directory (the simulator's cwd).
* `litedram_gen ... --sim` exits 1 AFTER writing the ROM-initialised core:
  the last builder step imports `pythondata_misc_tapcfg` (the sim's JTAG
  tap), which the venv lacks and the proxy does not need. The artefacts are
  complete when `litedram_core_sim_rom.init` is non-empty (~57 KB) and the
  core's `rom[0:N]` depth matches it (both carry the same timestamp).
* `gen/` is not tracked: a fresh clone runs `regen.sh --bios` before the
  LiteDRAM proxy, and the test skips with that instruction otherwise.
