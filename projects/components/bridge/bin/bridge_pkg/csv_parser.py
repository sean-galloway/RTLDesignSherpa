#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# CSV Parsing for Bridge Configuration

import csv
from typing import List, Dict, Tuple
from .config import PortSpec, BridgeConfig


def parse_csv_value(value: str, field_name: str):
    """Parse CSV value, handling N/A, hex, and integers"""
    value = value.strip()

    if value.upper() in ['N/A', 'NA', '']:
        return None

    # Handle hex values
    if value.startswith('0x') or value.startswith('0X'):
        return int(value, 16)

    # Try parsing as hex without prefix
    try:
        return int(value, 16)
    except ValueError:
        pass

    # Parse as decimal
    try:
        return int(value)
    except ValueError:
        # Return as string for non-numeric fields
        return value
def parse_ports_csv(csv_path: str) -> Tuple[List[PortSpec], List[PortSpec]]:
    """
    Parse ports.csv file to extract master and slave port specifications

    Returns:
        (masters, slaves) - Lists of PortSpec objects
    """
    masters = []
    slaves = []

    print(f"Parsing ports configuration: {csv_path}")

    with open(csv_path, 'r') as f:
        # Skip leading comment lines, but keep everything after the header
        lines = []
        header_found = False
        for line in f:
            stripped = line.strip()
            # Skip empty lines
            if not stripped:
                continue
            # Skip comment lines ONLY before header
            if not header_found and stripped.startswith('#'):
                continue
            else:
                # Found header or data
                header_found = True
                lines.append(line)

        if not lines:
            print(f"  WARNING: No data found in {csv_path}")
            return [], []

        print(f"  Read {len(lines)} lines from CSV (including header)")

        reader = csv.DictReader(lines)
        for row in reader:
            # Skip empty rows
            if not row.get('port_name') or row['port_name'].strip() == '':
                continue

            # Parse CSV fields
            port_name = row['port_name'].strip()
            direction = row['direction'].strip().lower()
            protocol = row['protocol'].strip().lower()
            # channels column is optional, default to 'rw' for backward compatibility
            channels = row.get('channels', 'rw').strip().lower() if row.get('channels') else 'rw'
            prefix = row['prefix'].strip()
            data_width = int(row['data_width'])
            addr_width = int(row['addr_width'])
            id_width_val = parse_csv_value(row['id_width'], 'id_width')
            base_addr_val = parse_csv_value(row['base_addr'], 'base_addr')
            addr_range_val = parse_csv_value(row['addr_range'], 'addr_range')

            # Parse ooo column (backward compatible)
            ooo_val = False
            if 'ooo' in row and row['ooo']:
                ooo_str = row['ooo'].strip().lower()
                if ooo_str not in ['n/a', 'na', '']:
                    try:
                        ooo_val = int(ooo_str) == 1
                    except ValueError:
                        print(f"  WARNING: Invalid ooo value '{ooo_str}' for {port_name}, defaulting to 0")
                        ooo_val = False

            # Validate channels value
            if channels not in ['rw', 'rd', 'wr']:
                print(f"  WARNING: Invalid channels '{channels}' for {port_name}, defaulting to 'rw'")
                channels = 'rw'

            # Create PortSpec
            port = PortSpec(
                port_name=port_name,
                direction=direction,
                protocol=protocol,
                channels=channels,
                prefix=prefix,
                data_width=data_width,
                addr_width=addr_width,
                id_width=id_width_val if id_width_val is not None else 0,
                base_addr=base_addr_val if base_addr_val is not None else 0,
                addr_range=addr_range_val if addr_range_val is not None else 0,
                enable_ooo=ooo_val
            )

            # Add to appropriate list
            if direction == 'master':
                masters.append(port)
                channels_str = f"[{channels.upper()}]" if channels != 'rw' else ""
                print(f"  Master: {port_name} ({protocol.upper()}, {data_width}b data, {channels.upper()}, prefix: {prefix})")
            elif direction == 'slave':
                slaves.append(port)
                ooo_str = " [OOO]" if port.enable_ooo else ""
                print(f"  Slave:  {port_name} ({protocol.upper()}, {data_width}b data, 0x{base_addr_val:08X}-0x{base_addr_val+addr_range_val-1:08X}, prefix: {prefix}){ooo_str}")
            else:
                raise ValueError(f"Invalid direction '{direction}' for port {port_name}")

    print(f"  Total: {len(masters)} masters, {len(slaves)} slaves")
    return masters, slaves


def parse_connectivity_csv(csv_path: str, masters: List[PortSpec], slaves: List[PortSpec]) -> Dict[str, List[str]]:
    """
    Parse connectivity.csv file to extract master-to-slave connectivity matrix

    Args:
        csv_path: Path to connectivity CSV file
        masters: List of master port specs (for validation)
        slaves: List of slave port specs (for validation)

    Returns:
        Dictionary: master_name -> [list of connected slave names]
    """
    connectivity = {}

    print(f"\nParsing connectivity matrix: {csv_path}")

    with open(csv_path, 'r') as f:
        # Skip leading comment lines, but keep everything after the header
        lines = []
        header_found = False
        for line in f:
            stripped = line.strip()
            # Skip empty lines
            if not stripped:
                continue
            # Skip comment lines ONLY before header
            if not header_found and stripped.startswith('#'):
                continue
            else:
                # Found header or data
                header_found = True
                lines.append(line)

        if not lines:
            print(f"  WARNING: No data found in {csv_path}")
            return {}

        print(f"  Read {len(lines)} lines from CSV (including header)")

        reader = csv.DictReader(lines)

        # Extract slave names from header (all columns except first)
        if not reader.fieldnames:
            print(f"  ERROR: No header found in {csv_path}")
            return {}

        first_col_name = reader.fieldnames[0]  # Get actual first column name
        slave_names = [col for col in reader.fieldnames if col != first_col_name]
        print(f"  Connectivity matrix: {len(slave_names)} slaves")

        # Validate slave names match ports.csv
        port_slave_names = {s.port_name for s in slaves}
        for sname in slave_names:
            if sname not in port_slave_names:
                raise ValueError(f"Slave '{sname}' in connectivity.csv not found in ports.csv")

        # Parse each row (one per master)
        for row in reader:
            master_name = row[first_col_name].strip()

            # Skip empty rows
            if not master_name:
                continue

            # Validate master name
            port_master_names = {m.port_name for m in masters}
            if master_name not in port_master_names:
                raise ValueError(f"Master '{master_name}' in connectivity.csv not found in ports.csv")

            # Extract connected slaves
            connected_slaves = []
            for slave_name in slave_names:
                value = row[slave_name].strip()
                if value == '1':
                    connected_slaves.append(slave_name)
                elif value != '0':
                    raise ValueError(f"Invalid connectivity value '{value}' for {master_name}->{slave_name} (must be 0 or 1)")

            connectivity[master_name] = connected_slaves
            print(f"  {master_name} -> {', '.join(connected_slaves) if connected_slaves else 'NONE'}")

    # Validate all masters have at least one connection
    for master_name, slaves_list in connectivity.items():
        if not slaves_list:
            print(f"  WARNING: Master '{master_name}' has no slave connections!")

    return connectivity


def determine_crossbar_config(config: BridgeConfig):
    """
    Determine internal crossbar configuration (widths)

    NOTE: With intelligent routing architecture, there is no single "crossbar width".
    Each master-slave connection operates at the appropriate width (direct or converted).
    These parameters are kept for backward compatibility and test infrastructure.

    Strategy:
    - Data width: Mode (most common) slave width - NOT used for routing decisions
    - Address width: Maximum address width among all ports
    - ID width: Maximum ID width among all AXI4 masters
    """
    # Find most common slave data width (mode) - for parameter compatibility only
    # Actual routing uses per-path widths via intelligent routing table
    axi4_slaves = [s for s in config.slaves if s.protocol == 'axi4']
    if axi4_slaves:
        from collections import Counter
        width_counts = Counter(s.data_width for s in axi4_slaves)
        config.crossbar_data_width = width_counts.most_common(1)[0][0]
    else:
        config.crossbar_data_width = 32  # Default fallback

    # Address width: HARD LIMIT to 64-bit for all agents
    # OLD: config.crossbar_addr_width = max(p.addr_width for p in config.masters + config.slaves)
    config.crossbar_addr_width = 64  # HARD LIMIT: 64-bit address for all agents

    # ID width: HARD LIMIT to 8-bit for all agents
    # OLD: config.crossbar_id_width = max(m.id_width for m in axi4_masters) if axi4_masters else 4
    config.crossbar_id_width = 8  # HARD LIMIT: 8-bit ID for all agents

    print(f"\nInternal crossbar configuration:")
    print(f"  Data width: {config.crossbar_data_width} bits")
    print(f"  Address width: {config.crossbar_addr_width} bits")
    print(f"  ID width: {config.crossbar_id_width} bits")


def identify_converters(config: BridgeConfig):
    """
    Identify which ports need protocol or width converters

    Updates PortSpec objects with converter requirements
    """
    print(f"\nIdentifying required converters:")

    # Check slaves for APB protocol (need AXI2APB)
    for slave in config.slaves:
        if slave.protocol == 'apb':
            slave.needs_axi2apb = True
            slave.converter_name = f"u_axi2apb_{slave.port_name}"
            print(f"  {slave.port_name}: Needs AXI2APB converter (APB slave)")

        # Check for width mismatch (even AXI4 slaves)
        if slave.data_width != config.crossbar_data_width:
            slave.needs_width_conv = True
            if slave.data_width < config.crossbar_data_width:
                print(f"  {slave.port_name}: Needs width downsize ({config.crossbar_data_width}b -> {slave.data_width}b)")
            else:
                print(f"  {slave.port_name}: Needs width upsize ({config.crossbar_data_width}b -> {slave.data_width}b)")

    # Check masters for width mismatch
    for master in config.masters:
        if master.data_width != config.crossbar_data_width:
            master.needs_width_conv = True
            if master.data_width < config.crossbar_data_width:
                print(f"  {master.port_name}: Needs width upsize ({master.data_width}b -> {config.crossbar_data_width}b)")
            else:
                print(f"  {master.port_name}: Needs width downsize ({master.data_width}b -> {config.crossbar_data_width}b)")

