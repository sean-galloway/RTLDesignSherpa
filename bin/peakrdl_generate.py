#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: peakrdl_generate
# Purpose: PeakRDL Register Generation Script
#
# Documentation: rtl/common/PRD.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2025-10-18

"""
PeakRDL Register Generation Script

Generic script to compile SystemRDL definitions and generate:
- SystemVerilog RTL for register blocks
- HTML/Markdown documentation
- Optional C/C++ headers

Usage:
    peakrdl_generate.py <input.rdl> [options]

Examples:
    # Basic usage - generates in ./generated/
    peakrdl_generate.py hpet_regs.rdl

    # Specify output directory
    peakrdl_generate.py hpet_regs.rdl -o ../output

    # Specify cpuif type
    peakrdl_generate.py hpet_regs.rdl --cpuif apb4

    # Just documentation, skip RTL
    peakrdl_generate.py hpet_regs.rdl --docs-only

Author: RTL Design Sherpa Project
License: MIT
"""

import os
import sys
import argparse
import shutil
from pathlib import Path

try:
    from systemrdl import RDLCompiler
    from peakrdl_regblock import RegblockExporter
    from peakrdl_regblock.udps import ALL_UDPS
    from peakrdl_regblock.cpuif.passthrough import PassthroughCpuif
    from peakrdl_regblock.cpuif.apb3 import APB3_Cpuif
    from peakrdl_regblock.cpuif.apb4 import APB4_Cpuif
    from peakrdl_regblock.cpuif.axi4lite import AXI4Lite_Cpuif
    from peakrdl_html import HTMLExporter
    from peakrdl_markdown import MarkdownExporter
except ImportError as e:
    print(f"ERROR: Missing PeakRDL dependencies: {e}")
    print("\nInstall with:")
    print("  pip install systemrdl-compiler")
    print("  pip install peakrdl-regblock")
    print("  pip install peakrdl-html")
    print("  pip install peakrdl-markdown")
    sys.exit(1)

# CPU Interface mappings
CPUIF_MAP = {
    "passthrough": PassthroughCpuif,
    "apb3": APB3_Cpuif,
    "apb4": APB4_Cpuif,
    "axi4lite": AXI4Lite_Cpuif,
}

def parse_args():
    """Parse command line arguments"""
    parser = argparse.ArgumentParser(
        description="Generate SystemVerilog and documentation from SystemRDL",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s hpet_regs.rdl
  %(prog)s hpet_regs.rdl -o ../output --cpuif apb4
  %(prog)s hpet_regs.rdl --docs-only
        """
    )

    parser.add_argument(
        "rdl_file",
        type=Path,
        help="Input SystemRDL file"
    )

    parser.add_argument(
        "-o", "--output",
        type=Path,
        default=None,
        help="Output directory (default: ./generated/ relative to RDL file)"
    )

    parser.add_argument(
        "--cpuif",
        choices=CPUIF_MAP.keys(),
        default="passthrough",
        help="CPU interface type (default: passthrough)"
    )

    parser.add_argument(
        "--docs-only",
        action="store_true",
        help="Generate only documentation, skip RTL"
    )

    parser.add_argument(
        "--rtl-only",
        action="store_true",
        help="Generate only RTL, skip documentation"
    )

    parser.add_argument(
        "--no-html",
        action="store_true",
        help="Skip HTML documentation generation"
    )

    parser.add_argument(
        "--no-markdown",
        action="store_true",
        help="Skip Markdown documentation generation"
    )

    parser.add_argument(
        "--copy-rtl",
        type=Path,
        default=None,
        help="Copy generated RTL to this directory after successful generation"
    )

    return parser.parse_args()

def main():
    """Main generation function"""
    args = parse_args()

    # Validate input file
    if not args.rdl_file.exists():
        print(f"ERROR: Input file not found: {args.rdl_file}")
        sys.exit(1)

    # Determine output directory
    if args.output:
        output_dir = args.output
    else:
        output_dir = args.rdl_file.parent / "generated"

    rtl_dir = output_dir / "rtl"
    docs_dir = output_dir / "docs"
    headers_dir = output_dir / "headers"

    print("=" * 80)
    print("PeakRDL Register Generation")
    print("=" * 80)
    print(f"Input:  {args.rdl_file}")
    print(f"Output: {output_dir}")
    print(f"CPUIF:  {args.cpuif}")
    print("=" * 80)

    # Create output directories
    for dir_path in [rtl_dir, docs_dir, headers_dir]:
        dir_path.mkdir(parents=True, exist_ok=True)
        print(f"✓ Created directory: {dir_path}")

    # Compile SystemRDL
    print(f"\n📖 Compiling SystemRDL: {args.rdl_file}")
    rdlc = RDLCompiler()

    # Register PeakRDL-regblock User Defined Properties
    print(f"  Registering PeakRDL UDPs...")
    for udp in ALL_UDPS:
        rdlc.register_udp(udp)

    try:
        rdlc.compile_file(str(args.rdl_file))
        root = rdlc.elaborate()
        print(f"✓ SystemRDL compilation successful")
        # Get the first addrmap child for address info
        top_node = root.top
        print(f"  Address map: {top_node.inst_name}")
        print(f"  Address range: 0x{top_node.absolute_address:X} - 0x{top_node.absolute_address + top_node.size - 1:X}")
    except Exception as e:
        print(f"✗ SystemRDL compilation failed: {e}")
        sys.exit(1)

    # Generate SystemVerilog RTL
    if not args.docs_only:
        print(f"\n🔨 Generating SystemVerilog RTL...")
        try:
            exporter = RegblockExporter()
            cpuif_cls = CPUIF_MAP[args.cpuif]

            # Output filename based on top-level name
            rtl_output = rtl_dir / f"{top_node.inst_name}.sv"

            exporter.export(
                root,
                str(rtl_output),
                cpuif_cls=cpuif_cls
            )
            print(f"✓ Generated: {rtl_output}")
            print(f"  CPU Interface: {args.cpuif}")

            # Note about adapters
            if args.cpuif == "passthrough":
                print(f"  NOTE: Use rtl/amba/adapters/peakrdl_to_cmdrsp.sv for cmd/rsp interface")
        except Exception as e:
            print(f"✗ RTL generation failed: {e}")
            import traceback
            traceback.print_exc()

    # Generate HTML Documentation
    if not args.rtl_only and not args.no_html:
        print(f"\n📚 Generating HTML documentation...")
        try:
            exporter = HTMLExporter()
            html_output = docs_dir / f"{top_node.inst_name}.html"
            exporter.export(root, str(html_output))
            print(f"✓ Generated: {html_output}")
        except Exception as e:
            print(f"✗ HTML generation failed: {e}")

    # Generate Markdown Documentation
    if not args.rtl_only and not args.no_markdown:
        print(f"\n📝 Generating Markdown documentation...")
        try:
            exporter = MarkdownExporter()
            md_output = docs_dir / f"{top_node.inst_name}.md"
            exporter.export(root, str(md_output))
            print(f"✓ Generated: {md_output}")
        except Exception as e:
            print(f"✗ Markdown generation failed: {e}")

    # Summary
    print("\n" + "=" * 80)
    print("Generation Complete!")
    print("=" * 80)
    print(f"\n📁 Output directory: {output_dir}")

    if not args.docs_only:
        print(f"\nGenerated RTL:")
        for f in sorted(rtl_dir.rglob("*.sv")):
            print(f"  • {f.relative_to(output_dir)}")

    if not args.rtl_only:
        print(f"\nGenerated Documentation:")
        for f in sorted(docs_dir.glob("*")):
            if f.is_file():
                print(f"  • {f.relative_to(output_dir)}")

    # Copy RTL to destination if requested
    if args.copy_rtl and not args.docs_only:
        print(f"\n📦 Copying RTL to {args.copy_rtl}...")
        try:
            # Create destination directory if needed
            args.copy_rtl.mkdir(parents=True, exist_ok=True)

            # Copy all generated RTL files (skip directories)
            copied_files = []
            for f in sorted(rtl_dir.rglob("*.sv")):
                if f.is_file():  # Only copy files, not directories
                    dest_file = args.copy_rtl / f.name
                    shutil.copy2(f, dest_file)
                    copied_files.append(f.name)
                    print(f"  ✓ Copied: {f.name}")

            # Also copy package files if they exist
            for f in sorted(rtl_dir.rglob("*.svh")):
                if f.is_file():
                    dest_file = args.copy_rtl / f.name
                    shutil.copy2(f, dest_file)
                    copied_files.append(f.name)
                    print(f"  ✓ Copied: {f.name}")

            print(f"\n✓ Successfully copied {len(copied_files)} file(s) to {args.copy_rtl}")

        except Exception as e:
            print(f"\n✗ Copy failed: {e}")
            return 1

    # Usage hints
    if not args.docs_only and args.cpuif == "passthrough":
        print(f"\n💡 Integration Hint:")
        print(f"  Use the generic adapter for cmd/rsp interface:")
        print(f"  rtl/amba/adapters/peakrdl_to_cmdrsp.sv")
        print(f"\n  See rtl/amba/adapters/README.md for usage example")

    return 0

if __name__ == "__main__":
    sys.exit(main())
