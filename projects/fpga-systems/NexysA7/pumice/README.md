# pumice on Nexys A7 -- directory map

Board-campaign area for the pumice DDR2/LPDDR2 controller. This file is a map
only. Method lives in the handbook: [[fpga/cmn-infra/boards]],
[[fpga/cmn-infra/host-stack]], [[fpga/cmn-infra/sequences]],
[[fpga/cmn-infra/uart-harness]], [[fpga/cmn-infra/build-flows]].

```
pumice/
  rtl/          board-level blocks shared by every build, FLAT
    filelists/  one .f per module, registered in bin/filelists.toml
  dv/           sim for THIS directory's rtl/ only
    tb/           tb_top wrappers
    tbclasses/    TB classes + generated regmaps
    tests/        cocotb/pytest
  bin/          test sequences + run_<test>.py  (transport-agnostic)

  build-perf/       BUILD 1 - pumice on real DDR2 (the subject)
    rtl/              whole harness: char top + wiring to the controller
      filelists/      this build's compile closure
    rtl-vivado/       vendor/Vivado-generated RTL (a7ddrphy)
    dv/tb/ dv/tests/  sim of the FULL harness
    host/             drivers / regmap accessors
    bin/              build-side tooling (PHY gen/elaboration)
    fpga/             bitstream flow: tcl/ constraints/ bitstream/ reports/
    results/          csv, plots, findings

  build-litedram/   BUILD 2 - LiteDRAM in pumice's place (the yardstick)
    rtl/ rtl/filelists/  board top wiring litedram_core to the same harness
    gen/              GENERATED cores from regen.sh (gitignored)
      board/            real A7DDRPHY, for silicon
      sim/              SDRAMPHYModel, verilatable
    dv/tb/ dv/tests/  sim against the sim core
    host/             perf host minus the pumice-CSR config calls
    fpga/             tcl/ constraints/ bitstream/ reports/
    results/          the A/B against build-perf
```

Further builds are `build-<variant>/` siblings with the same shape.

## Running it

You should never need a tcl script name, a Vivado command line or a pytest path.
All flow logic is in the global `make/fpga_flow.mk`; a build's Makefile is
variables only.

```
make                          # what this area offers
make -C build-perf help       # the full target list for one build

make lint                     # verilator, seconds, before you burn 30 min
make bitstream                # BUILD=perf by default
make bitstream BUILD=litedram
make program                  # board from the registry, BOARD=genesys2 to switch
make ports                    # which ttyUSB is this board on right now?
make seq-list                 # what sequences exist
make run SEQUENCES="init write_read"
make sim                      # this build's harness sim, no board
make blocks-sim               # the shared rtl/ blocks only
make ab                       # program+run BOTH builds, back to back
```

`build-litedram` adds `make regen` (regenerate the LiteDRAM cores into `gen/`);
`synth`/`bitstream` there refuse to start if no core has been generated, because
the alternative is an obscure Vivado failure a long way in.

## The two builds

They exist to be compared. `build-perf` measures pumice; `build-litedram` drops
LiteDRAM's DDR2 controller into the same socket so **the same pattern generator,
the same perf taps, the same timer and the same UART/CSR path** measure both --
an apples-to-apples benchmark rather than two numbers from two harnesses. That
only holds while the shared half really is shared, which is what `rtl/` below is
for.

LiteDRAM brings its own PLL, PHY and DDR2 init (BIOS), so it replaces
pumice + DFI + a7ddrphy wholesale and its host driver drops the pumice-CSR
config calls. Its core is *generated* into `gen/` and gitignored -- delete and
regenerate, never hand-edit (CRITICAL RULE #0).

## What goes where

**`rtl/` vs `build-*/rtl/`** -- a block reusable across builds belongs in
`rtl/`. The top that wires a specific harness together belongs to that build.
The DUT-agnostic `char_engine_harness` (engines + perf meters + bandwidth timer
+ harness_csr + UART bridge) is the clearest `rtl/` candidate: it is what makes
the two builds comparable, and today it sits inside the litedram flow.

**`dv/` vs `build-perf/dv/`** -- `dv/` tests the blocks in `rtl/`.
`build-perf/dv/` simulates the *whole* harness, real UART bridge included; per
[[fpga/cmn-infra/uart-harness]] wrapping the inner macro instead makes the two
flows "vaguely similar", not equivalent.

**`bin/` vs `build-perf/host/`** -- drivers (how to talk to registers) are build
collateral; sequences (what to do with them) are not, because they must run
unchanged against silicon and sim. Sequences take an injected bus, never a port.

**No `program_fpga.tcl` under `fpga/tcl/`.** Board programming is the global
`make/fpga_flow.mk` plus the `fpga/bin/boards/` registry.

## Status

Scaffold. The working collateral still lives at
`projects/NexysA7/ddr2-characterization/` (`ddr2_char_framework/` maps onto
`rtl/` + `dv/`; `flows-ours-uart/` maps onto `build-perf/`). That migration is
NEXYS-003 in `vault/Tasks/nexysa7/open.md`; NEXYS-002 moves the rest of
`projects/NexysA7/` under `projects/fpga-systems/` alongside it.

Populated today: `bin/` (init, write_read, memtest, run_smoke.py).
