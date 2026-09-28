# ISSUE-017: `make bitstream` silently builds the 66.67 MHz profile, not the board's 75 MHz design point

**Status:** open 2026-09-28  **Priority:** P2 -- it produces a board that looks
right, measures plausibly, and is not the design point.
**Owner:** TBD
**Found by:** running into it. Two bitstreams were built and programmed tonight
without noticing, and board results were reported from them.

## What happens

`projects/fpga-systems/NexysA7/pumice/build-perf` selects its frequency profile
from an environment variable:

    fpga/tcl/create_project.tcl:146
      if PUMICE_SYS_75 is set and non-zero -> +define+PUMICE_SYS_75  (75 MHz / DDR2-300)
      otherwise                            -> the 66.67 MHz profile

So a plain `make bitstream` builds **66.67 MHz**. The board's shipping design
point is **75 MHz**: `board_ddr2_300` in `dv/tbclasses/pumice_dram_configs.py`
carries `mc_clk_hz = 75000000`, the CSR reset-parity manifest declares 75 MHz,
every timing CSR reset is derived for 75 MHz, and the whole characterisation
campaign is at 75 MHz.

Nothing in the flow objects. The build succeeds, timing closes (easily -- it is
a slower clock), the board comes up, `init` passes, `write_read` passes with
`mismatched=0`, and the only visible sign is one field in one log line:

    [init] board: DDR2 v1 dfi_rate=2 gear=1 bl=4 ... clk=66.67MHz

## What it cost, concretely

1. **Board measurements were taken at the wrong operating point.** The BUG-020
   telemetry figures (32000 column ops, per-bank hit counts) came from a
   66.67 MHz board. Those particular conclusions are clock-independent -- the
   counters either count or they do not -- so they stand. Any BANDWIDTH number
   from such a build would not have.
2. **A WNS comparison was made across frequencies and read as a design result.**
   +0.358 ns and then +0.392 ns were reported against a +0.003 ns baseline as if
   comparable, and the ~0.36 ns "improvement" was flagged as unexplained. It was
   not a design change; it was a slower clock. Timing numbers from a build whose
   frequency was never stated are not comparable to anything.
3. The CSR resets on that board are derived for 75 MHz, so a 66.67 MHz build is
   running timing parameters for a clock it does not have.

## Why nothing caught it

TASK-015 layer 0 has a clock-parity check, and it passed. It compares the
manifest's declared clock against **the host file that sets it** -- two files
agreeing with each other. It has no way to see what the bitstream was compiled
for. "Both files say 75" and "the board runs 75" are different claims, and only
the second one matters.

## Mitigation already in place

`bin/seq_reset_parity.py` now reads `BUILD_CLK_HZ` off the board (an
elaboration-time constant, so it cannot drift from the hardware) and compares it
against the manifest, refusing to proceed on a mismatch:

    [reset_parity] board clock 66666667 Hz (manifest declares 75000000 Hz)
    AssertionError: CLOCK MISMATCH: ... If this is the 66.67 MHz profile,
    rebuild with PUMICE_SYS_75=1; do not measure against it.

That turns a silent wrong-frequency board into a hard stop at the first
sequence. It does not stop the wrong bitstream being BUILT.

## Done when

A decision, then the work:

1. **Default the build to the shipping profile** (`PUMICE_SYS_75` on unless
   explicitly disabled), so the common command produces the design point and the
   unusual frequency is the one you have to ask for; **or**
2. **Require the profile to be stated** -- no default, `make bitstream` fails
   without an explicit frequency selection. This is the handbook's usual answer:
   a missing configuration should fail loudly, not silently pick one.

Either way the frequency should be printed in the build banner and recorded next
to the bitstream, so "which clock is this .bit" is never inferred from a log line
two hundred lines into a board run.
