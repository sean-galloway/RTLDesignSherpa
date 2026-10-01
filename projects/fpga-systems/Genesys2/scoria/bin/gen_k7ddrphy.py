#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Emit a STANDALONE k7ddrphy.v for the Genesys 2, from LiteDRAM.

Why this exists. scoria drives a DFI bus and nothing else; to reach real DDR3
it needs a PHY, and the Genesys 2 PHY is LiteDRAM's K7DDRPHY -- the same one
the board-proof core uses, which passes memtest on this hardware. That core is
NOT reusable as a PHY, though: litedram_gen emits ONE flat module
(`litedram_genesys2_ddr3`, 23542 lines, a single `module` statement) with the
controller and the PHY fused, so there is nothing to carve out. The PHY has to
be generated on its own.

pumice solved the same problem for DDR2 by generating `a7ddrphy_generated.v`
once, by hand, and committing it. Its `gen_a7ddrphy.py` is scaffolding that
prints the invocation and exits -- the generation was never automated. This
script does the generation.

THE CONFIGURATION IS NOT INVENTED. Every value matches
build-litedram/litedram_genesys2_ddr3.yml, which is the config that produced
the working board proof, and the platform pads come from litex_boards' own
digilent_genesys2 definition rather than a hand-written pin list.

WHAT THE PHY'S INTERFACE TELLS YOU, and it is worth reading before wiring:

  SDRAM_PHY_DATABITS      32   the DQ bus (2 x MT41J256M16, x16 each)
  SDRAM_PHY_DFI_DATABITS  64   DFI data PER PHASE

A DFI phase carries TWO device transfers because DDR3 is double data rate --
LiteDRAM's s7ddrphy sets `dfi_databits = 2*databits` and packs transfer n into
`phases[n//2]`, half `n%2`. So four phases carry eight transfers, which is BL8
in one sys cycle: 256 bits of DFI data. scoria must therefore be configured
with DRAM_BEAT_WIDTH=64 (the per-phase width) and DRAM_DEVICE_WIDTH=32, NOT
beat=32. Every scoria suite before 2026-10-01 ran beat=32, a shape this PHY
cannot drive.

ALSO: DDR3 on S7DDRPHY is 1:4 ONLY. litedram asserts
`not (memtype == "DDR3" and nphases == 2)`, so DFI_RATE=4 is forced, and
DFI_RATE must equal nphases or the DFI bus is silently misframed.

Needs the LiteX venv built FROM GIT (not PyPI). LITEX_VENV overrides the
location; the recipe is in the pumice flow's 2026-09-10_tooling_notes.md, and
the same traps apply as in build-litedram/regen.sh -- in particular, run from a
neutral directory or `import migen` resolves to a clone root.

    ./gen_k7ddrphy.py -o <dir>/k7ddrphy.v [--sys-clk-freq 80e6]
"""

import argparse
import os
import sys
import tempfile


# The proven config, from build-litedram/litedram_genesys2_ddr3.yml.
MEMTYPE          = "DDR3"
NPHASES          = 4          # 1:4; DDR3 on S7DDRPHY admits nothing else
IODELAY_CLK_FREQ = 200e6      # Genesys 2 system clock
DEFAULT_SYS_CLK  = 100e6


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("-o", "--output", required=True,
                    help="path to write k7ddrphy.v")
    ap.add_argument("--sys-clk-freq", type=float, default=DEFAULT_SYS_CLK,
                    help="controller clock in Hz (default 100e6). The PHY's CL "
                         "and CWL are chosen from tCK = 1/(nphases*sys_clk), "
                         "so this must match the build's actual clock.")
    ap.add_argument("--name", default="k7ddrphy", help="module name")
    args = ap.parse_args()

    # Trap 1 from regen.sh: a cwd containing the litex/migen clones makes
    # `import migen` resolve to the clone root as a namespace package, and
    # generation dies with a misleading NameError from inside litex.
    os.chdir(tempfile.mkdtemp(prefix="gen_k7ddrphy-"))

    try:
        from migen.fhdl.verilog import convert
        from litex_boards.platforms import digilent_genesys2
        from litedram.phy.s7ddrphy import K7DDRPHY
    except ImportError as e:
        print(f"ERROR: {e}\n\nRun under the LiteX venv built FROM GIT:\n"
              f"  $LITEX_VENV/bin/python {sys.argv[0]} ...\n"
              f"Recipe: projects/fpga-systems/NexysA7/pumice/"
              f"ddr2-characterization/flows-litedram-uart/"
              f"2026-09-10_tooling_notes.md", file=sys.stderr)
        return 1

    plat = digilent_genesys2.Platform()
    pads = plat.request("ddram")
    phy = K7DDRPHY(pads,
                   memtype          = MEMTYPE,
                   nphases          = NPHASES,
                   sys_clk_freq     = args.sys_clk_freq,
                   iodelay_clk_freq = IODELAY_CLK_FREQ)

    tck = 1.0 / (NPHASES * args.sys_clk_freq)
    # DDR3's DLL fixes a MINIMUM frequency: tCK(AVG) max is 3.3 ns
    # (JESD79-3F). Below ~303 MHz CK the part is out of spec even though
    # LiteDRAM will happily generate for it -- get_default_cl() has no lower
    # bound and returns CL=6 all the way down.
    if tck > 3.3e-9:
        print(f"WARNING: tCK = {tck*1e9:.3f} ns exceeds the DDR3 tCK(AVG) max "
              f"of 3.3 ns (JESD79-3F) -- CK is {1/tck/1e6:.1f} MHz, below the "
              f"~303 MHz the DLL requires. The PHY will generate; the part is "
              f"out of spec.", file=sys.stderr)

    # The DFI bus and the DRAM pads are the interface the board top wires, so
    # they must survive as ports rather than being optimised into the body.
    ios = set()
    for sig, _ in pads.iter_flat():
        ios.add(sig)
    for phase in phy.dfi.phases:
        for sig, _ in phase.iter_flat():
            ios.add(sig)

    out = os.path.abspath(args.output) if not os.path.isabs(args.output) \
        else args.output
    v = convert(phy, ios=ios, name=args.name)
    os.makedirs(os.path.dirname(out), exist_ok=True)
    with open(out, "w") as f:
        f.write(str(v))

    nlines = sum(1 for _ in open(out))
    print(f"wrote {out}  ({nlines} lines, "
          f"sys {args.sys_clk_freq/1e6:.0f} MHz, CK {1/tck/1e6:.0f} MHz, "
          f"tCK {tck*1e9:.3f} ns, {NPHASES} phases, "
          f"dfi_databits {2*len(pads.dq)})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
