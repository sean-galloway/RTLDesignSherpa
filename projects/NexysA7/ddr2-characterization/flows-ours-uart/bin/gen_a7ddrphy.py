#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""gen_a7ddrphy.py -- placeholder script to generate LiteDRAM's a7ddrphy.v.

Vivado's synthesis fileset needs the REAL a7ddrphy body (a large machine-
generated Verilog file, ~4000 lines) that instantiates OSERDESE2 /
ISERDESE2 / IDELAYE2 / IOBUFDS_DIFF_OUT for the Artix-7 IOB serdes stack.
This script's job: invoke LiteDRAM to produce that file at build time
and drop it into `rtl-vivado/a7ddrphy/`.

Current status: SCAFFOLDING ONLY. LiteDRAM co-simulation is currently
blocked on a LiteX version cocktail (see the DV-repo memory
`project_litedram_cosim_blockers.md`); until that resolves, this
script prints the invocation the user should run manually and exits.

Once the LiteX cocktail lands, wire this into the Makefile's
`bitstream:` prerequisite so `make bitstream` regenerates the PHY.

Expected shape (once wired):

    from litedram.phy import a7ddrphy
    from migen import *

    # sdram_module settings from the char macro's parameters
    phy = a7ddrphy.A7DDRPHY(
        pads          = ...,                   # from LiteX-Boards platform
        memtype       = "DDR2",
        cl            = 3,                     # CAS latency, mode reg
        cwl           = 4,
        sys_clk_freq  = 100e6,
        iodelay_clk_freq = 200e6,
    )

    from migen.build.xilinx import XilinxIse
    XilinxIse().generate(phy, "a7ddrphy", output_dir="rtl-vivado/a7ddrphy/")
"""

import sys
import textwrap


def main() -> int:
    msg = textwrap.dedent("""
        gen_a7ddrphy.py: SCAFFOLDING ONLY.

        The DDR2 char harness ships a7ddrphy_stub.sv (a black-box declaration
        with matching port shape) so verilator / cocotb lint the top cleanly.

        For Vivado bitstream generation, you need the LiteDRAM-generated
        a7ddrphy.v. Until the LiteX version cocktail is unblocked (see the
        RTLDesignSherpa-DV memory `project_litedram_cosim_blockers.md`),
        generate it manually:

          # In a working LiteX environment:
          python3 -m litedram.gen \\
              --output-dir=projects/NexysA7/ddr2-characterization/flows-ours-vex/rtl-vivado/a7ddrphy/ \\
              --board=digilent_nexys_a7 \\
              --memtype=DDR2 \\
              --gen-phy-only

        Then add the generated a7ddrphy.v to the Vivado fileset in place of
        (not alongside) a7ddrphy_stub.sv.
    """).strip()
    print(msg)
    return 0


if __name__ == "__main__":
    sys.exit(main())
