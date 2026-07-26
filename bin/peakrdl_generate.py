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
# Documentation: docs/markdown/rtl-common/index.md
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
    from systemrdl import node as rdlnode
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

# =============================================================================
# RegisterMap dictionary exporter
# =============================================================================
# Walks the elaborated SystemRDL model and emits a Python file containing a
# `top_block` dict in the exact format consumed by
# bin/TBClasses/apb/register_map.py (RegisterMap). This lets the DV reference
# registers BY NAME via RegisterMap.get_register_offset_map(): a register-map
# split/relocation needs no DV changes, only a regenerated description.
#
# Format (matches stream_regmap.py / hpet_regmap.py):
#   'REG_NAME': {
#       'type': 'reg', 'name': 'REG_NAME',
#       'offset': '0xNNN', 'address': '0xNNN',   # absolute within the block
#       'size': 4, 'default': '0xNNNNNNNN', 'sw': 'rw',
#       ['array_index': N, 'array_name': 'ARR',]  # for register-array elements
#       'FIELD': {'type':'field', 'offset':'hi:lo'|'n', 'default':'0xN', 'sw':'rw'},
#       ...
#   }
# Nested regfiles are flattened transparently (their instance name is NOT
# prefixed); array regfiles/registers ARE prefixed with '<NAME><idx>' so each
# element gets a unique key (e.g. CH_STATE0_STATE, TIMER0_TIMER_CONFIG).

def _rm_sw_access(node_obj) -> str:
    """Map a SystemRDL sw access property to the RegisterMap short form."""
    try:
        sw = node_obj.get_property('sw', default=None)
    except Exception:
        return 'rw'
    # AccessType enum member names: r, w, rw, na, rw1, w1
    name = getattr(sw, 'name', None)
    return {
        'r': 'r',
        'w': 'wo',
        'w1': 'wo',
        'na': 'na',
        'rw': 'rw',
        'rw1': 'rw',
    }.get(name, 'rw')


def _rm_field_offset(field_node) -> str:
    """'hi:lo' for multi-bit fields, 'n' for single-bit."""
    if field_node.low == field_node.high:
        return str(field_node.low)
    return f"{field_node.high}:{field_node.low}"


def _rm_field_default(field_node) -> str:
    """Field reset value as a hex string sized to the field width."""
    try:
        reset_val = field_node.get_property('reset', default=None)
    except Exception:
        reset_val = None
    if reset_val is None or not isinstance(reset_val, int):
        reset_val = 0
    hex_digits = max(1, (field_node.width + 3) // 4)
    return f"0x{reset_val:0{hex_digits}X}"


def _rm_reg_default(reg_node) -> str:
    """Aggregate register reset from its fields, as a size-wide hex string."""
    reg_reset = 0
    for field in reg_node.fields():
        try:
            fr = field.get_property('reset', default=0)
        except Exception:
            fr = 0
        if isinstance(fr, int) and fr:
            reg_reset |= (fr << field.low)
    hex_digits = max(1, reg_node.size * 2)
    return f"0x{reg_reset:0{hex_digits}X}"


def _rm_reg_key_and_array(reg_node, top_node):
    """Build the unique dict key for a (possibly unrolled) register.

    Non-array regfile ancestors are transparent (name not included). Array
    ancestors and array registers contribute a '<NAME><idx>' segment. Returns
    (key, array_index, array_name).
    """
    segs = []
    array_index = None
    array_name = None
    cur = reg_node
    while cur is not None and cur is not top_node and not isinstance(cur, rdlnode.AddrmapNode):
        idx = getattr(cur, 'current_idx', None)
        is_arr = bool(getattr(cur, 'is_array', False))
        if cur is reg_node:
            if is_arr and idx is not None:
                segs.append(f"{cur.inst_name}{idx[0]}")
                array_index = idx[0]
                array_name = cur.inst_name.upper()
            else:
                segs.append(cur.inst_name)
        elif is_arr and idx is not None:
            # Array regfile ancestor -> contributes an indexed prefix.
            segs.append(f"{cur.inst_name.upper()}{idx[0]}")
            if array_index is None:
                array_index = idx[0]
                array_name = cur.inst_name.upper()
        # Non-array regfile ancestors are flattened transparently (skip name).
        cur = cur.parent
    segs.reverse()
    return "_".join(segs), array_index, array_name


def build_regmap_dict(top_node):
    """Walk the elaborated model and return the RegisterMap-format dict."""
    regs = {}
    base = top_node.absolute_address
    for node_obj in top_node.descendants(unroll=True):
        if not isinstance(node_obj, rdlnode.RegNode):
            continue
        key, array_index, array_name = _rm_reg_key_and_array(node_obj, top_node)
        addr = node_obj.absolute_address - base
        addr_str = f"0x{addr:03X}"
        reg_dict = {
            'address': addr_str,
            'offset': addr_str,
            'default': _rm_reg_default(node_obj),
            'type': 'reg',
            'size': node_obj.size,
            'sw': _rm_sw_access(node_obj),
            # Use the unique dict key as the name so RegisterMap (which re-keys
            # its offset map by the 'name' field) resolves array elements
            # distinctly instead of collapsing them (matches stream_regmap.py).
            'name': key,
        }
        if array_index is not None:
            reg_dict['array_index'] = array_index
            reg_dict['array_name'] = array_name
        for field_node in node_obj.fields():
            reg_dict[field_node.inst_name] = {
                'offset': _rm_field_offset(field_node),
                'default': _rm_field_default(field_node),
                'sw': _rm_sw_access(field_node),
                'type': 'field',
            }
        regs[key] = reg_dict
    return regs


def export_regmap(top_node, output_file, rdl_file):
    """Emit <output_file> containing a `top_block` dict for RegisterMap."""
    import pprint
    reg_dict = build_regmap_dict(top_node)
    output_file = Path(output_file)
    output_file.parent.mkdir(parents=True, exist_ok=True)
    with open(output_file, 'w') as f:
        f.write(f"""# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Auto-generated register map from: {Path(rdl_file).name}
# Generated by: peakrdl_generate.py --regmap
# DO NOT EDIT MANUALLY - Regenerate from .rdl source
#
# Compatible with: bin/TBClasses/apb/register_map.py

\"\"\"
Register map dictionary for {Path(rdl_file).stem}

Auto-generated from the SystemRDL specification. `top_block` maps every
register name to its absolute offset/address, size, reset default, and fields
in the format consumed by the RegisterMap class (by-name register access).

Usage:
    from {output_file.stem} import top_block
    reg_map = RegisterMap('{output_file.name}', apb_data_width=32,
                          apb_addr_width=16, start_address=0x0, log=logger)
\"\"\"

""")
        f.write("top_block = ")
        f.write(pprint.pformat(reg_dict, width=100, compact=False, sort_dicts=True))
        f.write("\n")
    field_count = sum(
        1
        for r in reg_dict.values()
        for v in r.values()
        if isinstance(v, dict) and v.get('type') == 'field'
    )
    print(f"✓ Generated regmap: {output_file}")
    print(f"  Registers: {len(reg_dict)}, Fields: {field_count}")
    return output_file


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

    parser.add_argument(
        "--regmap",
        action="store_true",
        help="Explicitly emit a RegisterMap-format <top>_regmap.py "
             "(also emitted by default alongside RTL unless --no-regmap)"
    )

    parser.add_argument(
        "--no-regmap",
        action="store_true",
        help="Skip the RegisterMap-format <top>_regmap.py export"
    )

    parser.add_argument(
        "--regmap-output",
        type=Path,
        default=None,
        help="Output path for the RegisterMap dict file "
             "(default: <output>/<top>_regmap.py)"
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

            # peakrdl-regblock >= 1.x: export() takes the output DIRECTORY and
            # writes <top>.sv + <top>_pkg.sv into it (passing a file path makes
            # makedirs() fail against an existing file — the old silent-skip bug).
            exporter.export(
                root,
                str(rtl_dir),
                cpuif_cls=cpuif_cls
            )
            rtl_output = rtl_dir / f"{top_node.inst_name}.sv"
            if not rtl_output.exists():
                raise FileNotFoundError(f"expected output missing: {rtl_output}")
            print(f"✓ Generated: {rtl_output}")
            print(f"  CPU Interface: {args.cpuif}")

            # Note about adapters
            if args.cpuif == "passthrough":
                print(f"  NOTE: Use rtl/amba/adapters/peakrdl_to_cmdrsp.sv for cmd/rsp interface")
        except Exception as e:
            print(f"✗ RTL generation failed: {e}")
            import traceback
            traceback.print_exc()
            sys.exit(1)

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

    # Generate RegisterMap dictionary (by-name register access for DV)
    emit_regmap = args.regmap or (not args.no_regmap and not args.docs_only)
    if emit_regmap:
        print(f"\n🗺️  Generating RegisterMap dictionary...")
        regmap_output = args.regmap_output or (output_dir / f"{top_node.inst_name}_regmap.py")
        try:
            export_regmap(top_node, regmap_output, args.rdl_file)
        except Exception as e:
            print(f"✗ RegisterMap export failed: {e}")
            import traceback
            traceback.print_exc()

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
