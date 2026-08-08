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

    # Hex requires the 0x prefix. There is deliberately NO bare-hex
    # fallback: trying int(value, 16) before decimal made every
    # all-digit field base-16 ('16' -> 22, '1000' -> 4096) with no
    # warning, and made the decimal branch unreachable.
    if value.startswith('0x') or value.startswith('0X'):
        return int(value, 16)

    # Parse as decimal
    try:
        return int(value)
    except ValueError:
        # Return as string for non-numeric fields
        return value
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
