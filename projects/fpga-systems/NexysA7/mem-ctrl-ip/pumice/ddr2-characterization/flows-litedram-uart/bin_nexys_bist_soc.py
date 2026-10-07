#!/usr/bin/env python3
"""LiteDRAM DDR2 reference on the Nexys A7 -- hardware BIST, for the pumice A/B.

The litex_boards nexys4ddr BaseSoC VERBATIM, with one change: with_bist=True on
add_sdram. Same board, same MT47H64M16, same 75 MHz sys / 1:2 / 300 MT/s
operating point pumice runs, so the numbers are directly comparable. The BIST
generator/checker is hardware, so it measures DRAM bandwidth rather than a
CPU's ability to issue loads. Drive from the BIOS: `sdram_bist <bl> <random>`.
"""
from litex_boards.targets.digilent_nexys4ddr import BaseSoC
from litex_boards.platforms import digilent_nexys4ddr
from litex.soc.integration.builder import Builder


class BistSoC(BaseSoC):
    def add_sdram(self, *args, **kwargs):
        kwargs["with_bist"] = True
        return super().add_sdram(*args, **kwargs)


def main():
    from litex.build.parser import LiteXArgumentParser
    parser = LiteXArgumentParser(platform=digilent_nexys4ddr.Platform,
                                 description="LiteDRAM DDR2 BIST reference")
    parser.add_target_argument("--sys-clk-freq", default=75e6, type=float)
    args = parser.parse_args()
    soc = BistSoC(sys_clk_freq=args.sys_clk_freq, **parser.soc_argdict)
    builder = Builder(soc, **parser.builder_argdict)
    if args.build:
        builder.build(**parser.toolchain_argdict)


if __name__ == "__main__":
    main()
