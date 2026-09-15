#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: generate_xbars
# Purpose: Convenience script to generate all APB crossbar variants.
#
# Documentation: docs/markdown/rtl-amba/index.md
# Subsystem: amba
#
# Author: sean galloway
# Created: 2025-10-18

"""
Convenience script to generate all APB crossbar variants.

Usage:
    # Generate every registered variant (1:1, 2:1, 1:4, 2:4, 2:2_mixed into
    # rtl/, plus the RLB 1:10 into retro_legacy_blocks/):
    python generate_xbars.py

    # Generate specific variant:
    python generate_xbars.py --masters 3 --slaves 6

Author: RTL Design Sherpa
Date: 2025-10-14
"""

import sys
import os
from pathlib import Path

# Import generator from local bin directory
from apbx_xbar_generator import generate_apbx_xbar


def generate_all_standard():
    """Generate every registered crossbar variant.

    Six in total: four plain (1:1, 2:1, 1:4, 2:4) and one mixed-version
    (2:2) into this component's rtl/, plus the Retro Legacy Blocks 1:10,
    which is emitted into retro_legacy_blocks/ because that is where it
    is consumed. Keeping the RLB one here is what stops it drifting --
    see the comment on `external` below.
    """

    variants = [
        (1, 1),  # 1-to-1 passthrough
        (2, 1),  # 2-to-1 arbitration
        (1, 4),  # 1-to-4 address decode
        (2, 4),  # 2-to-4 full crossbar
    ]

    # Mixed-version variant (APBX-001): m0=APB4, m1=APB5, s0=APB5,
    # s1=APB4. The generator emits the final form (banner + reset
    # macros); rtl/*.sv are pure generator output — regenerate freely.
    mixed = [
        ((2, 2), ['apb4', 'apb5'], ['apb5', 'apb4'], '_mixed'),
    ]

    # Canonical outputs live in rtl/ — the generator emits the final
    # form (banner + reset macros), so this IS the checked-in file.
    output_dir = Path(__file__).parent.parent / 'rtl'

    for masters, slaves in variants:
        output_file = output_dir / f"apbx_xbar_{masters}to{slaves}.sv"

        print(f"Generating {masters}-to-{slaves} crossbar...")

        code = generate_apbx_xbar(
            num_masters=masters,
            num_slaves=slaves,
            base_addr=0x10000000,
            addr_width=32,
            data_width=32,
            output_file=str(output_file),
            slave_size=0x10000,   # 64KB windows, matching the rtl/ baseline
        )

        with open(output_file, 'w') as f:
            f.write(code)

        print(f"  ✅ {output_file}")

    for (masters, slaves), mv, sv, suffix in mixed:
        output_file = output_dir / f"apbx_xbar_{masters}to{slaves}{suffix}.sv"
        print(f"Generating {masters}-to-{slaves}{suffix} crossbar...")
        code = generate_apbx_xbar(
            num_masters=masters,
            num_slaves=slaves,
            base_addr=0x10000000,
            addr_width=32,
            data_width=32,
            output_file=str(output_file),
            slave_size=0x10000,
            master_versions=mv,
            slave_versions=sv,
            name_suffix=suffix,
        )
        with open(output_file, 'w') as f:
            f.write(code)
        print(f"  ✅ {output_file}")

    # Retro Legacy Blocks 1-to-10 (RLB-016). Unlike everything above, this
    # variant is CONSUMED BY ANOTHER COMPONENT, so it is emitted into that
    # component's tree rather than rtl/. It is registered here deliberately:
    # the RLB crossbar used to be hand-written, which meant it never received
    # the generator's decode-miss fix (an unmapped address completed with
    # PSLVERR instead of wedging the bus) and decoded on raw PADDR bits rather
    # than the offset. That divergence is what RLB-016 recorded. Generating it
    # with the family is what stops it drifting a second time.
    #
    # NOTE the address map differs from the rtl/ family on purpose: the RLB
    # subsystem is documented at 0xFEC00000 with 4KB windows, not 0x10000000
    # with 64KB. Both are passed explicitly for exactly the reason the
    # generate_custom() comment below gives.
    external = [
        dict(masters=1, slaves=10, base_addr=0xFEC00000, slave_size=0x1000,
             path=(Path(__file__).resolve().parents[2] / 'retro_legacy_blocks'
                   / 'rtl' / 'apbx_xbar' / 'apbx_xbar_1to10.sv')),
    ]

    for v in external:
        output_file = v['path']
        print(f"Generating {v['masters']}-to-{v['slaves']} crossbar -> {output_file}...")
        code = generate_apbx_xbar(
            num_masters=v['masters'],
            num_slaves=v['slaves'],
            base_addr=v['base_addr'],
            addr_width=32,
            data_width=32,
            output_file=str(output_file),
            slave_size=v['slave_size'],
        )
        with open(output_file, 'w') as f:
            f.write(code)
        print(f"  \u2705 {output_file}")

    print(f"\n\u2705 Generated {len(variants) + len(mixed) + len(external)} crossbar variants")


def generate_custom(masters, slaves, base_addr=0x10000000, slave_size=0x10000):
    """Generate a custom crossbar variant."""

    # Canonical outputs live in rtl/ — the generator emits the final
    # form (banner + reset macros), so this IS the checked-in file.
    output_dir = Path(__file__).parent.parent / 'rtl'
    output_file = output_dir / f"apbx_xbar_{masters}to{slaves}.sv"

    print(f"Generating {masters}-to-{slaves} crossbar...")

    code = generate_apbx_xbar(
        num_masters=masters,
        num_slaves=slaves,
        base_addr=base_addr,
        addr_width=32,
        data_width=32,
        output_file=str(output_file),
        # Must be passed explicitly. The generator's own default is 4KB, so
        # omitting it here gave a custom variant 4KB windows while every
        # shipped variant above got 64KB -- same family, two address maps,
        # and nothing said so.
        slave_size=slave_size,
    )

    with open(output_file, 'w') as f:
        f.write(code)

    print(f"✅ Generated {output_file}")


if __name__ == '__main__':
    import argparse

    parser = argparse.ArgumentParser(
        description='Generate APB crossbar variants',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  Generate every registered variant (1:1, 2:1, 1:4, 2:4, 2:2_mixed and the
  Retro Legacy Blocks 1:10):
    %(prog)s

  Generate custom 3-to-6 crossbar:
    %(prog)s --masters 3 --slaves 6

  Generate with custom base address:
    %(prog)s --masters 4 --slaves 8 --base-addr 0x80000000
        """
    )

    parser.add_argument('--masters', '-m', type=int,
                        help='Number of master interfaces (1-16)')
    parser.add_argument('--slaves', '-s', type=int,
                        help='Number of slave interfaces (1-16)')
    parser.add_argument('--base-addr', '-b', type=lambda x: int(x, 0),
                        default=0x10000000,
                        help='Base address for slave address map (default 0x10000000)')
    parser.add_argument('--slave-size', type=lambda x: int(x, 0),
                        default=0x10000,
                        help='Address space per slave: 0x1000=4KB, 0x10000=64KB '
                             '(default 0x10000, matching the shipped variants)')

    args = parser.parse_args()

    if args.masters and args.slaves:
        # Generate custom variant
        generate_custom(args.masters, args.slaves, args.base_addr, args.slave_size)
    elif args.masters or args.slaves:
        print("❌ Error: Must specify both --masters and --slaves", file=sys.stderr)
        sys.exit(1)
    else:
        # Generate all standard variants
        generate_all_standard()
