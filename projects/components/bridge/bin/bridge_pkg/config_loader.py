#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Configuration Loader - TOML/YAML ports + CSV connectivity

"""
Configuration Loader for Bridge Generator

Loads bridge configuration from:
- TOML/YAML file: Port definitions (masters/slaves) with optional interface config
- CSV file: Connectivity matrix (master-to-slave address routing)

Hybrid approach:
- TOML/YAML provides hierarchical structure for port config and interface modules
- CSV provides reviewable table format for connectivity matrix

Usage:
    from bridge_pkg.config_loader import load_config

    config = load_config('bridge_2x2_rw.toml')  # Auto-finds connectivity CSV
    # or
    config = load_config('bridge_2x2_rw.yaml')  # Still supports YAML
    # or
    config = load_config('bridge_2x2_rw.toml', 'custom_connectivity.csv')
"""

import yaml
import sys
from pathlib import Path
from typing import List, Dict, Tuple, Optional
from .config import PortSpec, BridgeConfig
from .csv_parser import parse_connectivity_csv
from .config_validator import validate_config, ValidationError

# Try importing tomllib (Python 3.11+) or fallback to tomli
try:
    import tomllib
except ImportError:
    try:
        import tomli as tomllib
    except ImportError:
        tomllib = None
        print("WARNING: Neither tomllib nor tomli available. TOML support disabled.")
        print("  Install with: pip install tomli")


def load_toml_ports(toml_path: str) -> Tuple[List[PortSpec], List[PortSpec], Optional[Dict], Optional[Dict]]:
    """
    Load port configuration from TOML file.

    Args:
        toml_path: Path to TOML configuration file

    Returns:
        (masters, slaves, defaults, connectivity) - Lists of PortSpec, optional defaults dict, optional connectivity dict
    """
    if tomllib is None:
        raise RuntimeError("TOML support not available. Install with: pip install tomli")

    masters = []
    slaves = []
    defaults = None

    print(f"Loading TOML configuration: {toml_path}")

    with open(toml_path, 'rb') as f:
        data = tomllib.load(f)

    return _parse_port_data(data, toml_path)


def load_yaml_ports(yaml_path: str) -> Tuple[List[PortSpec], List[PortSpec], Optional[Dict], Optional[Dict]]:
    """
    Load port configuration from YAML file.

    Args:
        yaml_path: Path to YAML configuration file

    Returns:
        (masters, slaves, defaults) - Lists of PortSpec and optional defaults dict
    """
    print(f"Loading YAML configuration: {yaml_path}")

    with open(yaml_path, 'r') as f:
        data = yaml.safe_load(f)

    return _parse_port_data(data, yaml_path)


def _parse_port_data(data: Dict, config_path: str) -> Tuple[List[PortSpec], List[PortSpec], Optional[Dict], Optional[Dict]]:
    """
    Parse port data from loaded config (YAML or TOML).

    Args:
        data: Loaded configuration dictionary
        config_path: Path to config file (for error messages)

    Returns:
        (masters, slaves, defaults, connectivity) - Lists of PortSpec, optional defaults dict, optional connectivity dict
    """
    masters = []
    slaves = []
    defaults = None
    connectivity_data = None

    bridge_data = data.get('bridge')
    if not bridge_data:
        raise ValueError("Config file must contain 'bridge' key")

    bridge_name = bridge_data.get('name', 'unnamed_bridge')
    print(f"  Bridge: {bridge_name}")

    # Get defaults (for future interface module usage)
    defaults = bridge_data.get('defaults')

    # Parse masters
    for m in bridge_data.get('masters', []):
        port_name = m['name']
        prefix = m['prefix']
        id_width = m.get('id_width', 0)
        addr_width = m['addr_width']
        data_width = m['data_width']
        user_width = m.get('user_width', 1)
        protocol = m.get('protocol', 'axi4')
        channels = m.get('channels', 'rw')

        # Interface config (store for Phase 2, don't use yet)
        interface_config = m.get('interface')

        # Validate channels
        if channels not in ['rw', 'rd', 'wr']:
            print(f"  WARNING: Invalid channels '{channels}' for {port_name}, defaulting to 'rw'")
            channels = 'rw'

        port = PortSpec(
            port_name=port_name,
            direction='master',
            protocol=protocol,
            channels=channels,
            prefix=prefix,
            data_width=data_width,
            addr_width=addr_width,
            id_width=id_width,
            enable_ooo=False  # Masters don't use OOO flag
        )

        masters.append(port)
        channels_str = f"[{channels.upper()}]" if channels != 'rw' else ""
        interface_str = f" [IF: {interface_config['type']}]" if interface_config else ""
        print(f"  Master: {port_name} ({protocol.upper()}, {data_width}b data, {channels.upper()}, prefix: {prefix}){interface_str}")

    # Parse slaves
    for s in bridge_data.get('slaves', []):
        port_name = s['name']
        prefix = s['prefix']
        id_width = s.get('id_width', 0)
        addr_width = s['addr_width']
        data_width = s['data_width']
        user_width = s.get('user_width', 1)
        protocol = s.get('protocol', 'axi4')
        channels = s.get('channels', 'rw')
        enable_ooo = s.get('enable_ooo', False)

        # Get address mapping from YAML (may be hex string or int)
        base_addr_raw = s.get('base_addr', 0)
        addr_range_raw = s.get('addr_range', 0)

        # Convert to int if string (handles "0x..." format)
        if isinstance(base_addr_raw, str):
            base_addr = int(base_addr_raw, 0)
        else:
            base_addr = base_addr_raw

        if isinstance(addr_range_raw, str):
            addr_range = int(addr_range_raw, 0)
        else:
            addr_range = addr_range_raw

        # Interface config (store for Phase 2, don't use yet)
        interface_config = s.get('interface')

        # Validate channels
        if channels not in ['rw', 'rd', 'wr']:
            print(f"  WARNING: Invalid channels '{channels}' for {port_name}, defaulting to 'rw'")
            channels = 'rw'

        port = PortSpec(
            port_name=port_name,
            direction='slave',
            protocol=protocol,
            channels=channels,
            prefix=prefix,
            data_width=data_width,
            addr_width=addr_width,
            id_width=id_width,
            base_addr=base_addr,
            addr_range=addr_range,
            enable_ooo=enable_ooo
        )

        slaves.append(port)
        ooo_str = " [OOO]" if enable_ooo else ""
        interface_str = f" [IF: {interface_config['type']}]" if interface_config else ""
        addr_str = f" [0x{base_addr:08X}+0x{addr_range:X}]" if addr_range > 0 else ""
        print(f"  Slave:  {port_name} ({protocol.upper()}, {data_width}b data, prefix: {prefix}){addr_str}{ooo_str}{interface_str}")

    # Parse connectivity section if present (TOML embedded connectivity)
    connectivity_data = data.get('connectivity')
    if connectivity_data:
        print(f"  Found embedded connectivity in config file")

    print(f"  Total: {len(masters)} masters, {len(slaves)} slaves")
    return masters, slaves, defaults, connectivity_data


def find_connectivity_csv(yaml_path: str) -> Optional[str]:
    """
    Find companion connectivity CSV file for YAML config.

    Looks for:
    1. {yaml_name}_connectivity.csv (e.g., bridge_2x2_rw_connectivity.csv)
    2. {yaml_name}.csv (e.g., bridge_2x2_rw.csv)

    Args:
        yaml_path: Path to YAML file

    Returns:
        Path to connectivity CSV or None if not found
    """
    yaml_file = Path(yaml_path)
    yaml_dir = yaml_file.parent
    yaml_stem = yaml_file.stem  # e.g., "bridge_2x2_rw"

    # Try pattern 1: {name}_connectivity.csv
    pattern1 = yaml_dir / f"{yaml_stem}_connectivity.csv"
    if pattern1.exists():
        return str(pattern1)

    # Try pattern 2: {name}.csv
    pattern2 = yaml_dir / f"{yaml_stem}.csv"
    if pattern2.exists():
        return str(pattern2)

    return None


def _convert_embedded_connectivity(conn_dict: Dict, masters: List[PortSpec], slaves: List[PortSpec]) -> Dict[str, List[str]]:
    """
    Convert embedded TOML/YAML connectivity dictionary to internal format.

    TOML format:
        [connectivity]
        m0 = ["s0", "s1"]
        m1 = ["s0", "s1"]

    Internal format:
        {"m0": ["s0", "s1"], "m1": ["s0", "s1"]}

    Args:
        conn_dict: Raw connectivity dictionary from TOML/YAML
        masters: List of master PortSpec objects
        slaves: List of slave PortSpec objects

    Returns:
        Connectivity dictionary in internal format
    """
    connectivity = {}
    master_names = {m.port_name for m in masters}
    slave_names = {s.port_name for s in slaves}

    for master_name, slave_list in conn_dict.items():
        # Validate master name
        if master_name not in master_names:
            print(f"  WARNING: Connectivity references unknown master '{master_name}', skipping")
            continue

        # Validate slave names
        valid_slaves = []
        for slave_name in slave_list:
            if slave_name not in slave_names:
                print(f"  WARNING: Connectivity for {master_name} references unknown slave '{slave_name}', skipping")
                continue
            valid_slaves.append(slave_name)

        if valid_slaves:
            connectivity[master_name] = valid_slaves
            print(f"  Master {master_name} → Slaves {valid_slaves}")

    return connectivity


def load_config(config_path: str, connectivity_csv: Optional[str] = None) -> BridgeConfig:
    """
    Load complete bridge configuration from TOML/YAML + CSV.

    Args:
        config_path: Path to TOML or YAML port configuration
        connectivity_csv: Optional path to connectivity CSV
                         (auto-detected if not provided)

    Returns:
        BridgeConfig object with all configuration
    """
    # Auto-detect format based on file extension
    config_file = Path(config_path)
    if config_file.suffix == '.toml':
        masters, slaves, defaults, embedded_connectivity = load_toml_ports(config_path)
    elif config_file.suffix in ['.yaml', '.yml']:
        masters, slaves, defaults, embedded_connectivity = load_yaml_ports(config_path)
    else:
        raise ValueError(f"Unsupported config format: {config_file.suffix}. Use .toml, .yaml, or .yml")

    # Handle connectivity - use embedded if available, otherwise CSV
    if embedded_connectivity:
        # Convert embedded connectivity dict to matrix format
        print(f"  Using embedded connectivity from config file")
        connectivity = _convert_embedded_connectivity(embedded_connectivity, masters, slaves)
    else:
        # Find connectivity CSV if not provided
        if connectivity_csv is None:
            connectivity_csv = find_connectivity_csv(config_path)
            if connectivity_csv is None:
                raise ValueError(f"Could not find connectivity CSV for {config_path}")
            print(f"  Auto-detected connectivity: {connectivity_csv}")

        # Parse connectivity CSV (reuse existing parser)
        # This parser expects matrix format with 1/0 for connections
        connectivity = parse_connectivity_csv(connectivity_csv, masters, slaves)

    # Create BridgeConfig
    # Note: Slave addresses now come from YAML, not connectivity CSV
    config = BridgeConfig(
        masters=masters,
        slaves=slaves,
        connectivity=connectivity
    )

    # Validate configuration
    print("\nValidating configuration...")
    try:
        validate_config(masters, slaves, connectivity)
    except ValidationError as e:
        print(f"\n❌ Configuration validation FAILED:")
        print(f"   {e}")
        raise

    return config
