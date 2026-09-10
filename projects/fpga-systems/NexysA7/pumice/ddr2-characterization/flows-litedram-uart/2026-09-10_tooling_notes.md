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
defect — see PUMICE-025.

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
counters and host program unchanged. Tracked as PUMICE-026.
