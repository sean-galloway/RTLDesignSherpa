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
# Documentation: rtl/amba/PRD.md
# Subsystem: amba
#
# Author: sean galloway
# Created: 2025-10-18

"""
Convenience script to generate all APB crossbar variants.

Usage:
    # Generate all standard variants (1:1, 2:1, 1:4, 2:4):
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
from apb_xbar_generator import generate_apb_xbar


def generate_all_standard():
    """Generate all standard crossbar variants."""

    variants = [
        (1, 1),  # 1-to-1 passthrough
        (2, 1),  # 2-to-1 arbitration
        (1, 4),  # 1-to-4 address decode
        (2, 4),  # 2-to-4 full crossbar
    ]

    output_dir = Path(__file__).parent

    for masters, slaves in variants:
        output_file = output_dir / f"apb_xbar_{masters}to{slaves}.sv"

        print(f"Generating {masters}-to-{slaves} crossbar...")

        code = generate_apb_xbar(
            num_masters=masters,
            num_slaves=slaves,
            base_addr=0x10000000,
            addr_width=32,
            data_width=32,
            output_file=str(output_file)
        )

        with open(output_file, 'w') as f:
            f.write(code)

        print(f"  ✅ {output_file}")

    print(f"\n✅ Generated {len(variants)} crossbar variants")


def generate_custom(masters, slaves, base_addr=0x10000000):
    """Generate a custom crossbar variant."""

    output_dir = Path(__file__).parent
    output_file = output_dir / f"apb_xbar_{masters}to{slaves}.sv"

    print(f"Generating {masters}-to-{slaves} crossbar...")

    code = generate_apb_xbar(
        num_masters=masters,
        num_slaves=slaves,
        base_addr=base_addr,
        addr_width=32,
        data_width=32,
        output_file=str(output_file)
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
  Generate all standard variants (1:1, 2:1, 1:4, 2:4):
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

    args = parser.parse_args()

    if args.masters and args.slaves:
        # Generate custom variant
        generate_custom(args.masters, args.slaves, args.base_addr)
    elif args.masters or args.slaves:
        print("❌ Error: Must specify both --masters and --slaves", file=sys.stderr)
        sys.exit(1)
    else:
        # Generate all standard variants
        generate_all_standard()
