#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: Bridge Generator (CSV/YAML)
# Purpose: Generate AXI4 crossbar bridges from CSV configuration
#
# Author: sean galloway
# Created: 2025-10-31

"""
Bridge Generator (CSV/YAML) - Main Entry Point

Generates AXI4 crossbar bridges from CSV configuration files with:
- Custom port prefixes per port
- Channel-specific masters (wr/rd/rw)
- Intelligent width-aware routing (per-master multi-width paths)
- Automatic converter insertion (width and protocol)
- Partial connectivity support

Usage:
    # Single bridge generation
    python3 bridge_generator.py --ports ports.csv --connectivity connectivity.csv

    # Bulk generation from batch file
    python3 bridge_generator.py --bulk bridge_batch.csv

See bridge_pkg/ for implementation details.
"""

import argparse
import sys
import os
import shutil
import csv
import re
from pathlib import Path
from jinja2 import Environment, FileSystemLoader

from bridge_pkg import (BridgeConfig, parse_ports_csv, parse_connectivity_csv, load_config,
                        BridgeModuleGenerator, MasterConfig, SlaveInfo)


# ==============================================================================
# Test Generation Helper Functions
# ==============================================================================

def get_repo_root_for_path(path: Path) -> Path:
    """Walk up from `path` to find the nearest git repo root.

    Used by the test-file template to compute the importable module path
    of the generated TB regardless of where --output-tb wrote it.
    """
    p = Path(path).resolve()
    for candidate in (p, *p.parents):
        if (candidate / '.git').exists():
            return candidate
    raise RuntimeError(f"No .git ancestor for {path}")


def _normalize_prefix(prefix: str) -> str:
    """Ensure a port prefix from the .toml has a trailing `_` separator.

    Downstream emitters build signal names as ``f"{prefix}{signal}"``
    (e.g. ``f"{prefix}awvalid"``). Configs that set ``prefix="cpu_m_axi"``
    without a trailing underscore would otherwise produce ``cpu_m_axiawvalid``.
    Normalising at the boundary means every downstream consumer can rely on
    the well-formed prefix without re-implementing this.
    """
    if not prefix:
        return prefix
    return prefix if prefix.endswith("_") else prefix + "_"


def determine_channel_type(masters):
    """Determine overall channel type based on masters."""
    has_write = any(m.has_write_channels() for m in masters)
    has_read = any(m.has_read_channels() for m in masters)

    if has_write and has_read:
        return "rw"
    elif has_write:
        return "wr"
    elif has_read:
        return "rd"
    else:
        raise ValueError("No valid channels found in masters")


def build_tb_class_name(name, channel_type):
    """Build testbench class name from bridge name."""
    # Remove "bridge_" prefix if present
    if name.startswith("bridge_"):
        name = name[7:]

    # Split on underscores and capitalize each part
    parts = name.split('_')
    pascal_parts = [p.capitalize() for p in parts]

    # Add "TB" suffix
    return f"Bridge{''.join(pascal_parts)}TB"


def build_tb_module_name(tb_class_name):
    """Build Python module name from TB class name."""
    # Convert PascalCase to snake_case
    s1 = re.sub('(.)([A-Z][a-z]+)', r'\1_\2', tb_class_name)
    return re.sub('([a-z0-9])([A-Z])', r'\1_\2', s1).lower()


def generate_tests(ports_file, connectivity_file, bridge_name, output_tb_dir, output_test_dir, enable_ooo=True, output_rtl_dir=None):
    """Generate testbench class and test file from CSV or YAML configuration.

    Args:
        ports_file: Path to ports.csv or ports.yaml
        connectivity_file: Path to connectivity.csv (or None for YAML auto-detect)
        bridge_name: Bridge module name
        output_tb_dir: Output directory for TB class
        output_test_dir: Output directory for test file
        enable_ooo: Enable out-of-order support
        output_rtl_dir: Directory the bridge RTL was written to. Used to
            derive the filelist path for the test runner; if omitted the
            template falls back to the legacy bridge-component path.

    Returns:
        True if successful, False otherwise
    """
    try:
        # Detect file format
        ports_ext = Path(ports_file).suffix.lower()
        is_config_file = ports_ext in ['.yaml', '.yml', '.toml']

        if is_config_file:
            # YAML format - use load_config
            conn_path = connectivity_file if connectivity_file else None
            config = load_config(ports_file, conn_path)
        else:
            # CSV format - use old parsers
            masters, slaves = parse_ports_csv(ports_file)
            connectivity = parse_connectivity_csv(connectivity_file, masters, slaves)
            config = BridgeConfig(
                masters=masters,
                slaves=slaves,
                connectivity=connectivity
            )

        # Determine channel type
        channel_type = determine_channel_type(config.masters)

        # Build class names
        tb_class_name = build_tb_class_name(bridge_name, channel_type)
        tb_class_module = build_tb_module_name(tb_class_name)

        # Build template context
        master_names = ', '.join(m.port_name for m in config.masters)
        slave_names = ', '.join(s.port_name for s in config.slaves)

        data_width = max(
            max((m.data_width for m in config.masters), default=32),
            max((s.data_width for s in config.slaves), default=32)
        )

        # HARD LIMIT: All agents use 64-bit address width
        # Address width converters are not needed - all masters/slaves use same width
        addr_width = 64

        # HARD LIMIT: All agents use 8-bit ID width
        # ID width conversion is not supported - uniform width simplifies routing
        id_width = 8

        # Derive the importable module path for the TB class from the
        # actual output directory. The old template hardcoded
        # `projects.components.bridge.dv.tbclasses.<tb>`, which broke when
        # the user routed --output-tb to any other location (e.g. the
        # stream_char_framework bridge).
        try:
            tb_dir_abs = Path(output_tb_dir).resolve()
            repo_root_abs = Path(get_repo_root_for_path(tb_dir_abs))
            tb_dir_rel = tb_dir_abs.relative_to(repo_root_abs)
            tb_import_pkg = '.'.join(tb_dir_rel.parts)
        except (ValueError, RuntimeError):
            tb_import_pkg = 'projects.components.bridge.dv.tbclasses'

        # Derive filelist path the same way generate_bridge writes it:
        # bridge_dir is `<output_rtl_dir>/<bridge_name>` and the filelist
        # lives at `<output_rtl_dir>/../filelists/<bridge_name>.f`.
        # Pre-Bug-C this was hardcoded to the bridge-component path.
        if output_rtl_dir:
            try:
                bridge_dir_abs = (Path(output_rtl_dir).resolve() / bridge_name)
                repo_root_abs = Path(get_repo_root_for_path(bridge_dir_abs))
                rtl_root = bridge_dir_abs.parent.parent  # `<rtl>` dir
                filelist_abs = rtl_root / 'filelists' / f'{bridge_name}.f'
                filelist_rel = filelist_abs.relative_to(repo_root_abs)
                filelist_path = str(filelist_rel)
            except (ValueError, RuntimeError):
                filelist_path = f'projects/components/bridge/rtl/filelists/{bridge_name}.f'
        else:
            filelist_path = f'projects/components/bridge/rtl/filelists/{bridge_name}.f'

        context = {
            'rtl_module_name': bridge_name,
            'tb_class_name': tb_class_name,
            'tb_class_module': tb_class_module,
            'tb_import_pkg': tb_import_pkg,
            'num_masters': len(config.masters),
            'num_slaves': len(config.slaves),
            'channel_type': channel_type,
            'enable_ooo': enable_ooo,
            'masters': config.masters,
            'slaves': config.slaves,
            'master_names': master_names,
            'slave_names': slave_names,
            'connectivity': config.connectivity,
            'data_width': data_width,
            'addr_width': addr_width,
            'id_width': id_width,
            'rtl_relative_path': '../../../../rtl/bridge',
            'filelist_path': filelist_path
        }

        # Setup Jinja2 environment
        script_dir = Path(__file__).resolve().parent
        template_dir = script_dir / 'bridge_pkg' / 'jinja_templates'
        env = Environment(
            loader=FileSystemLoader(str(template_dir)),
            trim_blocks=True,
            lstrip_blocks=True
        )
        # Expose `min` / `max` as Jinja globals so templates can pick safe
        # offsets that depend on the slave's address range (e.g. avoiding
        # decode gaps when ranges are < 256 B). Jinja's default expression
        # language has no global builtins and silently fails on `&`/`~`,
        # which made earlier template attempts go through the generic
        # except-Exception in generate_tests() and produce a stale file.
        env.globals['min'] = min
        env.globals['max'] = max

        # Render templates
        tb_template = env.get_template('bridge_tb_class.py.j2')
        test_template = env.get_template('bridge_test_file.py.j2')

        tb_content = tb_template.render(context)
        test_content = test_template.render(context)

        # Create output directories
        output_tb_path = Path(output_tb_dir)
        output_test_path = Path(output_test_dir)
        output_tb_path.mkdir(parents=True, exist_ok=True)
        output_test_path.mkdir(parents=True, exist_ok=True)

        # Write TB class file
        tb_filename = f"{tb_class_module}.py"
        tb_file_path = output_tb_path / tb_filename
        with open(tb_file_path, 'w') as f:
            f.write(tb_content)

        # Write test file
        test_filename = f"test_{bridge_name}.py"
        test_file_path = output_test_path / test_filename
        with open(test_file_path, 'w') as f:
            f.write(test_content)

        print(f"  ✓ Generated TB class: {tb_file_path}")
        print(f"  ✓ Generated test file: {test_file_path}")

        return True

    except Exception as e:
        print(f"  ✗ Test generation failed: {e}")
        import traceback
        traceback.print_exc()
        return False


# ==============================================================================
# RTL Generation Functions
# ==============================================================================

def generate_bridge(ports_file, connectivity_file, name=None, output_dir="../rtl/generated", expose_arbiter=False):
    """Generate a single bridge from configuration files.

    Args:
        ports_file: Path to ports.csv or ports.yaml
        connectivity_file: Path to connectivity.csv (optional for YAML, auto-detected)
        name: Optional output module name (auto-generated if None)
        output_dir: Output directory for generated RTL (default: ../rtl/generated)
        expose_arbiter: Whether to expose arbiter grant signals (currently ignored in V2)

    Returns:
        tuple: (success: bool, bridge_name: str or None)
    """
    try:
        # Validate ports file exists
        if not os.path.exists(ports_file):
            print(f"  ERROR: Ports file not found: {ports_file}")
            return (False, None)

        # Detect format: YAML or CSV
        ports_ext = Path(ports_file).suffix.lower()
        is_config_file = ports_ext in ['.yaml', '.yml', '.toml']

        if is_config_file:
            # YAML format: Load ports and connectivity together
            print(f"\n  Using YAML configuration: {ports_file}")
            # For YAML, connectivity_file can be None or empty string (auto-detect)
            conn_path = connectivity_file if connectivity_file else None
            config = load_config(ports_file, conn_path)
            masters = config.masters
            slaves = config.slaves
            connectivity = config.connectivity
            # Auto-detect connectivity file path for copying (if not provided)
            if not connectivity_file:
                from bridge_pkg.config_loader import find_connectivity_csv
                connectivity_file = find_connectivity_csv(ports_file)
        else:
            # CSV format: Load ports and connectivity separately
            print(f"\n  Using CSV configuration: {ports_file}")
            if not os.path.exists(connectivity_file):
                print(f"  ERROR: Connectivity file not found: {connectivity_file}")
                return (False, None)

            # Parse CSV files
            masters, slaves = parse_ports_csv(ports_file)
            connectivity = parse_connectivity_csv(connectivity_file, masters, slaves)

            # Create bridge configuration
            config = BridgeConfig(
                masters=masters,
                slaves=slaves,
                connectivity=connectivity
            )

        # Generate output module name. Precedence:
        #   1. --name CLI override / bulk-mode `name` column
        #   2. [bridge].name from the TOML/YAML config (set on BridgeConfig)
        #   3. Auto-generated topology fallback: bridge_<M>x<S>_<channels>
        if name:
            output_name = name
        elif is_config_file and getattr(config, 'name', '').strip():
            output_name = config.name.strip()
        else:
            channel_types = set(m.channels for m in masters)
            if len(channel_types) == 1:
                channel_suffix = list(channel_types)[0]  # 'rd', 'wr', or 'rw'
            elif 'rw' in channel_types:
                channel_suffix = 'rw'
            elif 'wr' in channel_types and 'rd' in channel_types:
                channel_suffix = 'rw'
            else:
                channel_suffix = 'rw'
            output_name = f"bridge_{len(masters)}x{len(slaves)}_{channel_suffix}"

        # Create bridge-specific subdirectory (clean first if exists)
        bridge_dir = os.path.join(output_dir, output_name)

        # CRITICAL: Remove existing bridge directory to ensure clean regeneration
        if os.path.exists(bridge_dir):
            print(f"  Removing existing bridge directory: {bridge_dir}")
            shutil.rmtree(bridge_dir)

        os.makedirs(bridge_dir, exist_ok=True)

        # Convert PortSpec to MasterConfig/SlaveInfo format
        master_configs = []
        slave_infos = []

        for master_spec in masters:
            # Build slave connection list (indices of slaves this master connects to)
            slave_connections = []
            # Get list of slaves this master connects to
            connected_slave_names = connectivity.get(master_spec.port_name, [])
            for slave_idx, slave_spec in enumerate(slaves):
                # Check if this slave is in the master's connection list
                if slave_spec.port_name in connected_slave_names:
                    slave_connections.append(slave_idx)

            # Normalise prefix at the boundary: many downstream emitters
            # build signal names as `f"{prefix}{signal}"` and break if the
            # config forgot the trailing underscore (e.g. "cpu_m_axi" →
            # "cpu_m_axiawid"). Doing it here means every consumer sees the
            # well-formed prefix without having to remember to normalise.
            master_prefix = _normalize_prefix(master_spec.prefix)
            master_config = MasterConfig(
                name=master_spec.port_name,
                prefix=master_prefix,
                data_width=master_spec.data_width,
                addr_width=master_spec.addr_width,
                id_width=master_spec.id_width,
                channels=master_spec.channels,
                slave_connections=slave_connections
            )
            master_configs.append(master_config)

        for slave_spec in slaves:
            slave_prefix = _normalize_prefix(slave_spec.prefix)
            slave_info = SlaveInfo(
                name=slave_spec.port_name,
                prefix=slave_prefix,  # Pass slave prefix from config
                base_addr=slave_spec.base_addr,
                addr_range=slave_spec.addr_range,
                data_width=slave_spec.data_width,
                addr_width=slave_spec.addr_width,
                protocol=slave_spec.protocol
            )
            slave_infos.append(slave_info)

        # Create BridgeModuleGenerator with new adapter architecture
        gen = BridgeModuleGenerator(bridge_name=output_name, enable_monitoring=False)

        for master in master_configs:
            gen.add_master(master)
        for slave in slave_infos:
            gen.add_slave(slave)

        # Generate all files (package + adapters + bridge)
        generated_files = gen.generate_all(bridge_dir)

        print(f"  ✓ Generated bridge package: {generated_files['package']}")
        for master in master_configs:
            adapter_key = f"adapter_{master.name}"
            if adapter_key in generated_files:
                print(f"  ✓ Generated adapter: {generated_files[adapter_key]}")
        print(f"  ✓ Generated bridge: {generated_files['bridge']}")

        # Copy configuration files to bridge directory for reference
        if ports_file:
            config_copy = os.path.join(bridge_dir, os.path.basename(ports_file))
            shutil.copy2(ports_file, config_copy)
            print(f"  ✓ Copied config: {config_copy}")

        if connectivity_file:
            conn_copy = os.path.join(bridge_dir, os.path.basename(connectivity_file))
            shutil.copy2(connectivity_file, conn_copy)
            print(f"  ✓ Copied connectivity: {conn_copy}")

        # Generate filelist with dependencies
        #
        # Directory structure:
        #   rtl/
        #     generated/
        #       bridge_1x2_wr/  <- bridge_dir
        #         bridge_1x2_wr_pkg.sv
        #         cpu_adapter.sv
        #         bridge_1x2_wr.sv
        #     filelists/  <- filelist_dir (two levels up from bridge_dir, then into filelists/)
        #       bridge_1x2_wr.f
        #
        # Filelist paths use $REPO_ROOT environment variable for robustness
        # Set in env_python before running tools
        #
        filelist_lines = []

        # Add include directory first
        filelist_lines.append("# Include directories")
        filelist_lines.append("+incdir+$REPO_ROOT/rtl/amba/includes")
        filelist_lines.append("")

        filelist_lines.append("# Bridge RTL files (generated)")

        # Compute filelist directory: two levels up from bridge_dir, then into filelists/
        # bridge_dir = rtl/generated/bridge_1x2_wr
        # parent of bridge_dir = rtl/generated
        # parent of parent = rtl
        # filelist_dir = rtl/filelists
        rtl_dir = os.path.dirname(os.path.dirname(bridge_dir))  # Go up 2 levels to rtl/
        filelist_dir = os.path.join(rtl_dir, "filelists")

        # Anchor every emitted bridge-file path on $REPO_ROOT (when we can
        # find a git root above the output dir). Bare relative paths break
        # whenever the bridge filelist is `-f`-included from another
        # filelist whose base dir is somewhere else — both consumers
        # (Vivado's tcl/filelist_utils.tcl and TBClasses/shared/
        # filelist_utils.py via FileListProcessor) flatten nested filelists
        # against the outer filelist's base, so a nested `generated/...`
        # path resolves wrong. Using $REPO_ROOT-anchored paths matches
        # every other entry in the filelist (axi4_slave_*, gaxi_*, ...).
        try:
            repo_root_for_bridge = str(get_repo_root_for_path(Path(bridge_dir)))
        except (RuntimeError, OSError):
            repo_root_for_bridge = None

        def _bridge_file_path(fp: str) -> str:
            if repo_root_for_bridge:
                try:
                    rel = Path(fp).resolve().relative_to(repo_root_for_bridge)
                    return f"$REPO_ROOT/{rel.as_posix()}"
                except ValueError:
                    pass  # bridge_dir lives outside the repo for some reason
            return os.path.relpath(fp, rtl_dir)

        # Package must be first for compile order
        if 'package' in generated_files:
            filelist_lines.append(_bridge_file_path(generated_files['package']))

        # Then other files (adapters, bridge)
        for file_key in sorted(generated_files.keys()):
            if file_key != 'package':  # Skip package (already added)
                filelist_lines.append(_bridge_file_path(generated_files[file_key]))

        filelist_lines.append("")
        filelist_lines.append("# AXI4 Wrapper modules (timing isolation)")
        filelist_lines.append("# Master adapters use axi4_slave_* (act as AXI slave to external master)")
        filelist_lines.append("$REPO_ROOT/rtl/amba/axi4/axi4_slave_wr.sv")
        filelist_lines.append("$REPO_ROOT/rtl/amba/axi4/axi4_slave_rd.sv")
        filelist_lines.append("# Slave adapters use axi4_master_* (act as AXI master to external slave)")
        filelist_lines.append("$REPO_ROOT/rtl/amba/axi4/axi4_master_wr.sv")
        filelist_lines.append("$REPO_ROOT/rtl/amba/axi4/axi4_master_rd.sv")

        filelist_lines.append("")
        filelist_lines.append("# GAXI skid buffers (used by wrappers and converters)")
        filelist_lines.append("$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv")

        filelist_lines.append("")
        filelist_lines.append("# Width converters (for data width adaptation)")
        filelist_lines.append("$REPO_ROOT/projects/components/converters/rtl/axi4_dwidth_converter_rd.sv")
        filelist_lines.append("$REPO_ROOT/projects/components/converters/rtl/axi4_dwidth_converter_wr.sv")

        # Check if any slaves use APB protocol
        has_apb = any(slave.protocol.lower() == 'apb' for slave in config.slaves)
        if has_apb:
            filelist_lines.append("")
            filelist_lines.append("# APB protocol converter dependencies (in dependency order)")
            filelist_lines.append("# Common dependencies first")
            filelist_lines.append("$REPO_ROOT/rtl/common/counter_bin.sv")
            filelist_lines.append("$REPO_ROOT/rtl/common/fifo_control.sv")
            filelist_lines.append("")
            filelist_lines.append("# AMBA shared modules")
            filelist_lines.append("$REPO_ROOT/rtl/amba/shared/axi_gen_addr.sv")
            filelist_lines.append("$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv")
            filelist_lines.append("")
            filelist_lines.append("# AXI4 stubs")
            filelist_lines.append("$REPO_ROOT/rtl/amba/axi4/stubs/axi4_slave_wr_stub.sv")
            filelist_lines.append("$REPO_ROOT/rtl/amba/axi4/stubs/axi4_slave_rd_stub.sv")
            filelist_lines.append("$REPO_ROOT/rtl/amba/axi4/stubs/axi4_slave_stub.sv")
            filelist_lines.append("")
            filelist_lines.append("# APB modules")
            filelist_lines.append("$REPO_ROOT/rtl/amba/apb/apb_master.sv")
            filelist_lines.append("$REPO_ROOT/rtl/amba/shared/cdc_2_phase_handshake.sv")
            filelist_lines.append("$REPO_ROOT/rtl/amba/shared/cdc_4_phase_handshake.sv")
            filelist_lines.append("$REPO_ROOT/projects/components/converters/rtl/axi4_to_apb_convert.sv")
            filelist_lines.append("$REPO_ROOT/rtl/amba/apb/apb_master_stub.sv")
            filelist_lines.append("")
            filelist_lines.append("# APB protocol converter (AXI4 to APB)")
            filelist_lines.append("$REPO_ROOT/projects/components/converters/rtl/axi4_to_apb_shim.sv")

        # Check if any slaves use AXI4-Lite protocol
        has_axil = any(slave.protocol.lower() == 'axil' for slave in config.slaves)
        if has_axil:
            filelist_lines.append("")
            filelist_lines.append("# AXI4-Lite protocol converter dependencies")
            filelist_lines.append("$REPO_ROOT/projects/components/converters/rtl/axi4_to_axil4_rd.sv")
            filelist_lines.append("$REPO_ROOT/projects/components/converters/rtl/axi4_to_axil4_wr.sv")

        # Note: Width converters are included even if not used in this specific bridge
        # because they're needed when master/slave data widths differ.
        # The synthesizer will optimize away unused instances.

        filelist_content = '\n'.join(filelist_lines)
        os.makedirs(filelist_dir, exist_ok=True)

        filelist_path = os.path.join(filelist_dir, f"{output_name}.f")
        with open(filelist_path, 'w') as f:
            f.write(filelist_content)

        print(f"  ✓ Generated filelist: {filelist_path}")

        return (True, output_name)

    except Exception as e:
        print(f"  ✗ Bridge generation failed: {e}")
        import traceback
        traceback.print_exc()
        return (False, None)


def parse_bulk_csv(bulk_file):
    """Parse bulk generation CSV file.

    Unified CSV format (supports RTL + optional test generation):
        name,ports,connectivity,output_dir,output_tb,output_test,expose_arbiter_signals
        # Lines starting with # are comments
        bridge_name,path/to/ports.csv,path/to/conn.csv,../rtl,../dv/tbclasses,../dv/tests,false

    Args:
        bulk_file: Path to bulk CSV file

    Returns:
        List of dicts with generation parameters
    """
    configs = []

    with open(bulk_file, 'r') as f:
        reader = csv.DictReader(f)
        for line_num, row in enumerate(reader, start=2):  # Start at 2 (after header)
            # Skip comment lines (check first field)
            first_field = list(row.values())[0] if row else ""
            if first_field.strip().startswith('#'):
                continue

            # Parse row
            config = {
                'name': row.get('name', '').strip() or None,
                'ports': row.get('ports', '').strip(),
                'connectivity': row.get('connectivity', '').strip(),
                'output_dir': row.get('output_dir', '').strip() or '../rtl/generated',
                'output_tb': row.get('output_tb', '').strip() or '../dv/tbclasses',
                'output_test': row.get('output_test', '').strip() or '../dv/tests',
                'expose_arbiter': row.get('expose_arbiter_signals', 'false').strip().lower() in ('true', '1', 'yes')
            }

            # Validate required fields
            if not config['ports']:
                print(f"WARNING: Line {line_num}: Missing 'ports' field, skipping")
                continue

            # Connectivity is optional for YAML files (auto-detected)
            ports_ext = Path(config['ports']).suffix.lower()
            is_config_file = ports_ext in ['.yaml', '.yml', '.toml']
            if not is_config_file and not config['connectivity']:
                print(f"WARNING: Line {line_num}: Missing 'connectivity' field for CSV ports file, skipping")
                continue

            configs.append(config)

    return configs


def main():
    parser = argparse.ArgumentParser(
        description="CSV-Based Bridge Generator with Protocol and Width Converters",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Single bridge generation
  python bridge_generator.py --ports example_ports.csv --connectivity example_connectivity.csv --output ../rtl/

  # Bulk generation from batch file
  python bridge_generator.py --bulk bridge_batch.csv

Configuration Files:
  ports.csv        - Defines each master/slave port (protocol, widths, address ranges, prefixes)
  connectivity.csv - Defines which masters connect to which slaves (partial connectivity)

Bulk Generation CSV Format:
  name,ports,connectivity,output_dir,expose_arbiter_signals
  # Lines starting with # are comments
  bridge_2x2_rw,test_configs/bridge_2x2_rw.yaml,,../rtl/generated,false
  bridge_4x4_rw,test_configs/bridge_4x4_rw.yaml,,../rtl/generated,true
        """
    )

    # Create mutually exclusive group for single vs bulk mode
    mode_group = parser.add_mutually_exclusive_group(required=True)
    mode_group.add_argument("--bulk", type=str, metavar="BULK_CSV",
                           help="Path to bulk generation CSV file (see format above)")
    mode_group.add_argument("--ports", type=str,
                           help="Path to ports.csv configuration file (single mode)")

    # Single mode arguments (only used when --ports specified)
    parser.add_argument("--connectivity", type=str,
                       help="Path to connectivity.csv configuration file (required with --ports)")
    parser.add_argument("--name", type=str, default=None,
                       help="Output module name (default: auto-generated)")
    parser.add_argument("--output-dir", type=str, default="../rtl/generated",
                       help="Output directory for generated RTL (default: ../rtl/generated)")
    parser.add_argument("--expose-arbiter-signals", action="store_true",
                       help="Expose arbiter grant signals as outputs for testing/debugging")

    # Test generation arguments
    parser.add_argument("--generate-tests", action="store_true",
                       help="Also generate testbench classes and test files")
    parser.add_argument("--output-tb", type=str, default="../dv/tbclasses",
                       help="Output directory for testbench classes (default: ../dv/tbclasses)")
    parser.add_argument("--output-test", type=str, default="../dv/tests",
                       help="Output directory for test files (default: ../dv/tests)")

    args = parser.parse_args()

    print("="*70)
    print("Bridge Generator (CSV/YAML)")
    print("="*70)

    if args.bulk:
        # Bulk generation mode
        if not os.path.exists(args.bulk):
            print(f"ERROR: Bulk file not found: {args.bulk}")
            sys.exit(1)

        print(f"Bulk generation mode: {args.bulk}")
        print("")

        configs = parse_bulk_csv(args.bulk)

        if not configs:
            print("ERROR: No valid configurations found in bulk file")
            sys.exit(1)

        print(f"Found {len(configs)} bridge configuration(s) to generate")
        print("")

        success_count = 0
        fail_count = 0

        for i, config in enumerate(configs, start=1):
            print(f"[{i}/{len(configs)}] Generating bridge: {config.get('name', 'auto-named')}")
            print(f"  Ports: {config['ports']}")
            print(f"  Connectivity: {config['connectivity']}")

            # Generate RTL
            success, bridge_name = generate_bridge(
                ports_file=config['ports'],
                connectivity_file=config['connectivity'],
                name=config['name'],
                output_dir=config['output_dir'],
                expose_arbiter=config['expose_arbiter']
            )

            if success:
                success_count += 1

                # Generate tests if requested
                if args.generate_tests and bridge_name:
                    print(f"  Generating tests for {bridge_name}...")
                    test_success = generate_tests(
                        ports_file=config['ports'],
                        connectivity_file=config['connectivity'],
                        bridge_name=bridge_name,
                        output_tb_dir=config['output_tb'],
                        output_test_dir=config['output_test'],
                        enable_ooo=True,
                        output_rtl_dir=config['output_dir']
                    )
                    if not test_success:
                        print(f"  ⚠ Test generation failed for {bridge_name}")
            else:
                fail_count += 1

            print("")

        print("="*70)
        print(f"Bulk generation complete: {success_count} succeeded, {fail_count} failed")
        print("="*70)

        if fail_count > 0:
            sys.exit(1)

    else:
        # Single generation mode
        # Check if connectivity is required (only for CSV ports files)
        ports_ext = Path(args.ports).suffix.lower()
        is_config_file = ports_ext in ['.yaml', '.yml', '.toml']

        if not is_config_file and not args.connectivity:
            print("ERROR: --connectivity required when using CSV ports file (single mode)")
            parser.print_help()
            sys.exit(1)

        print("Single generation mode")
        print("")

        # Generate RTL
        success, bridge_name = generate_bridge(
            ports_file=args.ports,
            connectivity_file=args.connectivity,  # Can be None for YAML
            name=args.name,
            output_dir=args.output_dir,
            expose_arbiter=args.expose_arbiter_signals
        )

        if not success:
            print("")
            print("="*70)
            print("✗ Bridge generation failed!")
            print("="*70)
            sys.exit(1)

        # Generate tests if requested
        if args.generate_tests and bridge_name:
            print("")
            print(f"Generating tests for {bridge_name}...")
            test_success = generate_tests(
                ports_file=args.ports,
                connectivity_file=args.connectivity,
                bridge_name=bridge_name,
                output_tb_dir=args.output_tb,
                output_test_dir=args.output_test,
                enable_ooo=True,
                output_rtl_dir=args.output_dir
            )
            if not test_success:
                print("  ⚠ Test generation failed")

        print("")
        print("="*70)
        print("✓ Bridge generation complete!")
        if args.generate_tests:
            print("✓ Test generation complete!")
        print("="*70)


if __name__ == "__main__":
    main()
