#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: Bridge CSV Generator
# Purpose: Generate custom AXI4 bridges with protocol and width converters from CSV configuration
#
# Documentation: projects/components/bridge/PRD.md
# Subsystem: bridge
#
# Author: sean galloway
# Created: 2025-10-25

"""
Bridge CSV Generator

Generates custom AXI4 crossbar bridges with:
- Mixed AXI4 and APB slave ports (AXI2APB converters inserted automatically)
- Width converters for data width mismatches
- Partial connectivity (not all masters connected to all slaves)
- Custom port prefixes from CSV configuration

CSV Configuration Files:
1. ports.csv - Define each master/slave port with protocol, widths, address ranges
2. connectivity.csv - Define which masters can access which slaves

Author: RTL Design Sherpa
Project: Bridge (CSV-based Bridge Generator)
Version: 2.0 (CSV-driven with converters)
"""

import argparse
import sys
import os
import csv
from dataclasses import dataclass, field
from typing import Dict, List, Tuple
from pathlib import Path

# Import the framework
sys.path.insert(0, str(Path(__file__).resolve().parents[4] / 'bin'))
from rtl_generators.verilog.module import Module


@dataclass
class PortSpec:
    """Specification for a single port (master or slave)"""
    port_name: str          # Unique port identifier
    direction: str          # 'master' or 'slave'
    protocol: str           # 'axi4' or 'apb'
    channels: str = 'rw'    # 'rw' (read+write), 'rd' (read-only), 'wr' (write-only)
    prefix: str = ''        # Signal prefix (e.g., 'rapids_m_axi_')
    data_width: int = 0     # Data width in bits
    addr_width: int = 0     # Address width in bits
    id_width: int = 0       # ID width (0 for APB)
    base_addr: int = 0      # Base address for slave (N/A for master)
    addr_range: int = 0     # Address range for slave (N/A for master)

    # Internal fields (filled during generation)
    needs_axi2apb: bool = False      # True if APB slave (needs AXI2APB converter)
    needs_width_conv: bool = False   # True if width doesn't match crossbar
    converter_name: str = ''         # Name of converter instance

    def has_write_channels(self) -> bool:
        """True if this port has write channels (AW, W, B)"""
        return self.channels in ['rw', 'wr']

    def has_read_channels(self) -> bool:
        """True if this port has read channels (AR, R)"""
        return self.channels in ['rw', 'rd']


@dataclass
class BridgeCSVConfig:
    """Complete bridge configuration from CSV files"""
    masters: List[PortSpec] = field(default_factory=list)
    slaves: List[PortSpec] = field(default_factory=list)
    connectivity: Dict[str, List[str]] = field(default_factory=dict)  # master_name -> [slave_names]

    # Crossbar configuration (derived from ports)
    crossbar_data_width: int = 0    # Common data width for internal crossbar
    crossbar_addr_width: int = 0    # Common address width for internal crossbar
    crossbar_id_width: int = 0      # Common ID width for internal crossbar


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
                addr_range=addr_range_val if addr_range_val is not None else 0
            )

            # Add to appropriate list
            if direction == 'master':
                masters.append(port)
                channels_str = f"[{channels.upper()}]" if channels != 'rw' else ""
                print(f"  Master: {port_name} ({protocol.upper()}, {data_width}b data, {channels.upper()}, prefix: {prefix})")
            elif direction == 'slave':
                slaves.append(port)
                print(f"  Slave:  {port_name} ({protocol.upper()}, {data_width}b data, 0x{base_addr_val:08X}-0x{base_addr_val+addr_range_val-1:08X}, prefix: {prefix})")
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


def determine_crossbar_config(config: BridgeCSVConfig):
    """
    Determine internal crossbar configuration (widths)

    Strategy:
    - Data width: Maximum data width among all AXI4 ports
    - Address width: Maximum address width among all ports
    - ID width: Maximum ID width among all AXI4 masters
    """
    # Find max data width (only AXI4 ports count)
    axi4_ports = [p for p in config.masters + config.slaves if p.protocol == 'axi4']
    config.crossbar_data_width = max(p.data_width for p in axi4_ports) if axi4_ports else 32

    # Find max address width
    config.crossbar_addr_width = max(p.addr_width for p in config.masters + config.slaves)

    # Find max ID width (only masters)
    axi4_masters = [m for m in config.masters if m.protocol == 'axi4']
    config.crossbar_id_width = max(m.id_width for m in axi4_masters) if axi4_masters else 4

    print(f"\nInternal crossbar configuration:")
    print(f"  Data width: {config.crossbar_data_width} bits")
    print(f"  Address width: {config.crossbar_addr_width} bits")
    print(f"  ID width: {config.crossbar_id_width} bits")


def identify_converters(config: BridgeCSVConfig):
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


class BridgeCSVGenerator(Module):
    """
    CSV-based Bridge Generator

    Generates custom AXI4 crossbar with:
    - Mixed AXI4 and APB slave ports (with AXI2APB converters)
    - Width converters for mismatched data widths
    - Partial connectivity matrix (not full crossbar)
    - Custom port prefixes and names from CSV
    """

    def __init__(self, config: BridgeCSVConfig, output_name: str):
        self.cfg = config
        self.module_str = output_name

        # Initialize Module base class
        Module.__init__(self, module_name=self.module_str)

        # TODO: This is a large generator - will be implemented in phases
        # For now, create a placeholder that demonstrates the structure

        print(f"\nGenerating bridge module: {self.module_str}")

    def generate_module_params(self):
        """Generate module parameters"""
        param_str = f'''
            parameter int NUM_MASTERS = {len(self.cfg.masters)},
            parameter int NUM_SLAVES  = {len(self.cfg.slaves)},
            parameter int XBAR_DATA_WIDTH = {self.cfg.crossbar_data_width},
            parameter int XBAR_ADDR_WIDTH = {self.cfg.crossbar_addr_width},
            parameter int XBAR_ID_WIDTH   = {self.cfg.crossbar_id_width},
            parameter int XBAR_STRB_WIDTH = {self.cfg.crossbar_data_width // 8}
        '''
        self.params.add_param_string(param_str)

    def generate_axi4_master_ports(self, port: PortSpec, port_idx: int):
        """Generate AXI4 master port signals with custom prefix (channel-specific)"""
        prefix = port.prefix
        dw = port.data_width
        aw = port.addr_width
        iw = port.id_width
        sw = dw // 8
        channels_desc = f"[{port.channels.upper()}]" if port.channels != 'rw' else ""

        # Note: Master port on bridge = slave interface signals (s_axi_*)
        port_str = f"// Master port: {port.port_name} ({dw}b AXI4 {channels_desc}, prefix: {prefix})\n"

        # Generate write channels if needed
        if port.has_write_channels():
            port_str += f'''            // Write Address Channel
            input  logic [{aw-1}:0]   {prefix}awaddr,
            input  logic [{iw-1}:0]   {prefix}awid,
            input  logic [7:0]        {prefix}awlen,
            input  logic [2:0]        {prefix}awsize,
            input  logic [1:0]        {prefix}awburst,
            input  logic              {prefix}awlock,
            input  logic [3:0]        {prefix}awcache,
            input  logic [2:0]        {prefix}awprot,
            input  logic              {prefix}awvalid,
            output logic              {prefix}awready,
            // Write Data Channel
            input  logic [{dw-1}:0]   {prefix}wdata,
            input  logic [{sw-1}:0]   {prefix}wstrb,
            input  logic              {prefix}wlast,
            input  logic              {prefix}wvalid,
            output logic              {prefix}wready,
            // Write Response Channel
            output logic [{iw-1}:0]   {prefix}bid,
            output logic [1:0]        {prefix}bresp,
            output logic              {prefix}bvalid,
            input  logic              {prefix}bready'''
            # Add comma if we're generating read channels too
            if port.has_read_channels():
                port_str += ','
            port_str += '\n'

        # Generate read channels if needed
        if port.has_read_channels():
            port_str += f'''            // Read Address Channel
            input  logic [{aw-1}:0]   {prefix}araddr,
            input  logic [{iw-1}:0]   {prefix}arid,
            input  logic [7:0]        {prefix}arlen,
            input  logic [2:0]        {prefix}arsize,
            input  logic [1:0]        {prefix}arburst,
            input  logic              {prefix}arlock,
            input  logic [3:0]        {prefix}arcache,
            input  logic [2:0]        {prefix}arprot,
            input  logic              {prefix}arvalid,
            output logic              {prefix}arready,
            // Read Data Channel
            output logic [{dw-1}:0]   {prefix}rdata,
            output logic [{iw-1}:0]   {prefix}rid,
            output logic [1:0]        {prefix}rresp,
            output logic              {prefix}rlast,
            output logic              {prefix}rvalid,
            input  logic              {prefix}rready
'''

        self.ports.add_port_string(port_str.rstrip())

    def generate_axi4_slave_ports(self, port: PortSpec, port_idx: int):
        """Generate AXI4 slave port signals with custom prefix"""
        prefix = port.prefix
        dw = port.data_width
        aw = port.addr_width
        iw = port.id_width if port.id_width > 0 else self.cfg.crossbar_id_width
        sw = dw // 8

        # Note: Slave port on bridge = master interface signals (m_axi_*)
        port_str = f'''
            // Slave port: {port.port_name} ({dw}b AXI4, prefix: {prefix})
            // Write Address Channel
            output logic [{aw-1}:0]   {prefix}awaddr,
            output logic [{iw-1}:0]   {prefix}awid,
            output logic [7:0]        {prefix}awlen,
            output logic [2:0]        {prefix}awsize,
            output logic [1:0]        {prefix}awburst,
            output logic              {prefix}awlock,
            output logic [3:0]        {prefix}awcache,
            output logic [2:0]        {prefix}awprot,
            output logic              {prefix}awvalid,
            input  logic              {prefix}awready,
            // Write Data Channel
            output logic [{dw-1}:0]   {prefix}wdata,
            output logic [{sw-1}:0]   {prefix}wstrb,
            output logic              {prefix}wlast,
            output logic              {prefix}wvalid,
            input  logic              {prefix}wready,
            // Write Response Channel
            input  logic [{iw-1}:0]   {prefix}bid,
            input  logic [1:0]        {prefix}bresp,
            input  logic              {prefix}bvalid,
            output logic              {prefix}bready,
            // Read Address Channel
            output logic [{aw-1}:0]   {prefix}araddr,
            output logic [{iw-1}:0]   {prefix}arid,
            output logic [7:0]        {prefix}arlen,
            output logic [2:0]        {prefix}arsize,
            output logic [1:0]        {prefix}arburst,
            output logic              {prefix}arlock,
            output logic [3:0]        {prefix}arcache,
            output logic [2:0]        {prefix}arprot,
            output logic              {prefix}arvalid,
            input  logic              {prefix}arready,
            // Read Data Channel
            input  logic [{dw-1}:0]   {prefix}rdata,
            input  logic [{iw-1}:0]   {prefix}rid,
            input  logic [1:0]        {prefix}rresp,
            input  logic              {prefix}rlast,
            input  logic              {prefix}rvalid,
            output logic              {prefix}rready
        '''
        self.ports.add_port_string(port_str.rstrip())

    def generate_apb_slave_ports(self, port: PortSpec, port_idx: int):
        """Generate APB slave port signals with custom prefix"""
        prefix = port.prefix
        dw = port.data_width
        aw = port.addr_width
        sw = dw // 8

        # APB slave port
        port_str = f'''
            // Slave port: {port.port_name} ({dw}b APB, prefix: {prefix})
            output logic              {prefix}psel,
            output logic              {prefix}penable,
            output logic [{aw-1}:0]   {prefix}paddr,
            output logic              {prefix}pwrite,
            output logic [{dw-1}:0]   {prefix}pwdata,
            output logic [{sw-1}:0]   {prefix}pstrb,
            output logic [2:0]        {prefix}pprot,
            input  logic              {prefix}pready,
            input  logic [{dw-1}:0]   {prefix}prdata,
            input  logic              {prefix}pslverr
        '''
        self.ports.add_port_string(port_str.rstrip())

    def generate_all_ports(self):
        """Generate all port declarations"""
        # Clock and reset
        clock_reset_str = '''
            input  logic aclk,
            input  logic aresetn
        '''
        self.ports.add_port_string(clock_reset_str.rstrip())

        # Master ports
        for idx, master in enumerate(self.cfg.masters):
            if master.protocol == 'axi4':
                self.generate_axi4_master_ports(master, idx)
            else:
                raise ValueError(f"Unsupported master protocol: {master.protocol}")

        # Slave ports
        for idx, slave in enumerate(self.cfg.slaves):
            if slave.protocol == 'axi4':
                self.generate_axi4_slave_ports(slave, idx)
            elif slave.protocol == 'apb':
                self.generate_apb_slave_ports(slave, idx)
            else:
                raise ValueError(f"Unsupported slave protocol: {slave.protocol}")

    def generate_internal_signals(self):
        """Generate internal signal declarations for crossbar connections"""
        xbar_dw = self.cfg.crossbar_data_width
        xbar_aw = self.cfg.crossbar_addr_width
        xbar_iw = self.cfg.crossbar_id_width
        xbar_sw = xbar_dw // 8

        nm = len(self.cfg.masters)
        ns = len(self.cfg.slaves)

        self.comment("="*78)
        self.comment("Internal Signals - Crossbar Connections")
        self.comment("="*78)
        self.comment(f"Internal crossbar: {nm} masters × {ns} slaves at {xbar_dw}b data width")
        self.instruction("")

        # Crossbar master-side signals (from external masters, potentially through width converters)
        self.comment("Crossbar master-side interfaces (after width conversion if needed)")
        sig_str = f'''
            logic [{xbar_aw-1}:0] xbar_m_awaddr  [NUM_MASTERS];
            logic [{xbar_iw-1}:0] xbar_m_awid    [NUM_MASTERS];
            logic [7:0]           xbar_m_awlen   [NUM_MASTERS];
            logic [2:0]           xbar_m_awsize  [NUM_MASTERS];
            logic [1:0]           xbar_m_awburst [NUM_MASTERS];
            logic                 xbar_m_awlock  [NUM_MASTERS];
            logic [3:0]           xbar_m_awcache [NUM_MASTERS];
            logic [2:0]           xbar_m_awprot  [NUM_MASTERS];
            logic                 xbar_m_awvalid [NUM_MASTERS];
            logic                 xbar_m_awready [NUM_MASTERS];

            logic [{xbar_dw-1}:0] xbar_m_wdata  [NUM_MASTERS];
            logic [{xbar_sw-1}:0] xbar_m_wstrb  [NUM_MASTERS];
            logic                 xbar_m_wlast  [NUM_MASTERS];
            logic                 xbar_m_wvalid [NUM_MASTERS];
            logic                 xbar_m_wready [NUM_MASTERS];

            logic [{xbar_iw-1}:0] xbar_m_bid    [NUM_MASTERS];
            logic [1:0]           xbar_m_bresp  [NUM_MASTERS];
            logic                 xbar_m_bvalid [NUM_MASTERS];
            logic                 xbar_m_bready [NUM_MASTERS];

            logic [{xbar_aw-1}:0] xbar_m_araddr  [NUM_MASTERS];
            logic [{xbar_iw-1}:0] xbar_m_arid    [NUM_MASTERS];
            logic [7:0]           xbar_m_arlen   [NUM_MASTERS];
            logic [2:0]           xbar_m_arsize  [NUM_MASTERS];
            logic [1:0]           xbar_m_arburst [NUM_MASTERS];
            logic                 xbar_m_arlock  [NUM_MASTERS];
            logic [3:0]           xbar_m_arcache [NUM_MASTERS];
            logic [2:0]           xbar_m_arprot  [NUM_MASTERS];
            logic                 xbar_m_arvalid [NUM_MASTERS];
            logic                 xbar_m_arready [NUM_MASTERS];

            logic [{xbar_dw-1}:0] xbar_m_rdata  [NUM_MASTERS];
            logic [{xbar_iw-1}:0] xbar_m_rid    [NUM_MASTERS];
            logic [1:0]           xbar_m_rresp  [NUM_MASTERS];
            logic                 xbar_m_rlast  [NUM_MASTERS];
            logic                 xbar_m_rvalid [NUM_MASTERS];
            logic                 xbar_m_rready [NUM_MASTERS];
        '''
        self.instruction(sig_str)
        self.instruction("")

        # Crossbar slave-side signals (to external slaves, potentially through converters)
        self.comment("Crossbar slave-side interfaces (before width/protocol conversion if needed)")
        sig_str = f'''
            logic [{xbar_aw-1}:0] xbar_s_awaddr  [NUM_SLAVES];
            logic [{xbar_iw-1}:0] xbar_s_awid    [NUM_SLAVES];
            logic [7:0]           xbar_s_awlen   [NUM_SLAVES];
            logic [2:0]           xbar_s_awsize  [NUM_SLAVES];
            logic [1:0]           xbar_s_awburst [NUM_SLAVES];
            logic                 xbar_s_awlock  [NUM_SLAVES];
            logic [3:0]           xbar_s_awcache [NUM_SLAVES];
            logic [2:0]           xbar_s_awprot  [NUM_SLAVES];
            logic                 xbar_s_awvalid [NUM_SLAVES];
            logic                 xbar_s_awready [NUM_SLAVES];

            logic [{xbar_dw-1}:0] xbar_s_wdata  [NUM_SLAVES];
            logic [{xbar_sw-1}:0] xbar_s_wstrb  [NUM_SLAVES];
            logic                 xbar_s_wlast  [NUM_SLAVES];
            logic                 xbar_s_wvalid [NUM_SLAVES];
            logic                 xbar_s_wready [NUM_SLAVES];

            logic [{xbar_iw-1}:0] xbar_s_bid    [NUM_SLAVES];
            logic [1:0]           xbar_s_bresp  [NUM_SLAVES];
            logic                 xbar_s_bvalid [NUM_SLAVES];
            logic                 xbar_s_bready [NUM_SLAVES];

            logic [{xbar_aw-1}:0] xbar_s_araddr  [NUM_SLAVES];
            logic [{xbar_iw-1}:0] xbar_s_arid    [NUM_SLAVES];
            logic [7:0]           xbar_s_arlen   [NUM_SLAVES];
            logic [2:0]           xbar_s_arsize  [NUM_SLAVES];
            logic [1:0]           xbar_s_arburst [NUM_SLAVES];
            logic                 xbar_s_arlock  [NUM_SLAVES];
            logic [3:0]           xbar_s_arcache [NUM_SLAVES];
            logic [2:0]           xbar_s_arprot  [NUM_SLAVES];
            logic                 xbar_s_arvalid [NUM_SLAVES];
            logic                 xbar_s_arready [NUM_SLAVES];

            logic [{xbar_dw-1}:0] xbar_s_rdata  [NUM_SLAVES];
            logic [{xbar_iw-1}:0] xbar_s_rid    [NUM_SLAVES];
            logic [1:0]           xbar_s_rresp  [NUM_SLAVES];
            logic                 xbar_s_rlast  [NUM_SLAVES];
            logic                 xbar_s_rvalid [NUM_SLAVES];
            logic                 xbar_s_rready [NUM_SLAVES];
        '''
        self.instruction(sig_str)
        self.instruction("")

    def generate_width_converter_master(self, idx, master):
        """Generate width converter instance for master-side (upsize, channel-specific)"""
        prefix = master.prefix
        s_width = master.data_width
        m_width = self.cfg.crossbar_data_width

        self.comment(f"Width Converter for Master {idx}: {master.port_name} [{master.channels.upper()}]")
        self.comment(f"  Upsize: {s_width}b → {m_width}b")

        inst_str = ''

        # Generate write converter only if master has write channels
        if master.has_write_channels():
            inst_str += f'''
        // Width Converter (WRITE) - Master {idx}: {master.port_name}
        axi4_dwidth_converter_wr #(
            .S_AXI_DATA_WIDTH({s_width}),
            .M_AXI_DATA_WIDTH({m_width}),
            .AXI_ID_WIDTH({master.id_width}),
            .AXI_ADDR_WIDTH({master.addr_width}),
            .AXI_USER_WIDTH(1)
        ) u_wconv_m{idx}_wr (
            .aclk         (aclk),
            .aresetn      (aresetn),
            // Slave interface (external master port)
            .s_axi_awid   ({prefix}awid),
            .s_axi_awaddr ({prefix}awaddr),
            .s_axi_awlen  ({prefix}awlen),
            .s_axi_awsize ({prefix}awsize),
            .s_axi_awburst({prefix}awburst),
            .s_axi_awlock ({prefix}awlock),
            .s_axi_awcache({prefix}awcache),
            .s_axi_awprot ({prefix}awprot),
            .s_axi_awqos  (4'b0),
            .s_axi_awregion(4'b0),
            .s_axi_awuser (1'b0),
            .s_axi_awvalid({prefix}awvalid),
            .s_axi_awready({prefix}awready),
            .s_axi_wdata  ({prefix}wdata),
            .s_axi_wstrb  ({prefix}wstrb),
            .s_axi_wlast  ({prefix}wlast),
            .s_axi_wuser  (1'b0),
            .s_axi_wvalid ({prefix}wvalid),
            .s_axi_wready ({prefix}wready),
            .s_axi_bid    ({prefix}bid),
            .s_axi_bresp  ({prefix}bresp),
            .s_axi_buser  (/* unused */),
            .s_axi_bvalid ({prefix}bvalid),
            .s_axi_bready ({prefix}bready),
            // Master interface (to crossbar)
            .m_axi_awid   (xbar_m_awid[{idx}]),
            .m_axi_awaddr (xbar_m_awaddr[{idx}]),
            .m_axi_awlen  (xbar_m_awlen[{idx}]),
            .m_axi_awsize (xbar_m_awsize[{idx}]),
            .m_axi_awburst(xbar_m_awburst[{idx}]),
            .m_axi_awlock (xbar_m_awlock[{idx}]),
            .m_axi_awcache(xbar_m_awcache[{idx}]),
            .m_axi_awprot (xbar_m_awprot[{idx}]),
            .m_axi_awqos  (/* unused */),
            .m_axi_awregion(/* unused */),
            .m_axi_awuser (/* unused */),
            .m_axi_awvalid(xbar_m_awvalid[{idx}]),
            .m_axi_awready(xbar_m_awready[{idx}]),
            .m_axi_wdata  (xbar_m_wdata[{idx}]),
            .m_axi_wstrb  (xbar_m_wstrb[{idx}]),
            .m_axi_wlast  (xbar_m_wlast[{idx}]),
            .m_axi_wuser  (/* unused */),
            .m_axi_wvalid (xbar_m_wvalid[{idx}]),
            .m_axi_wready (xbar_m_wready[{idx}]),
            .m_axi_bid    (xbar_m_bid[{idx}]),
            .m_axi_bresp  (xbar_m_bresp[{idx}]),
            .m_axi_buser  (1'b0),
            .m_axi_bvalid (xbar_m_bvalid[{idx}]),
            .m_axi_bready (xbar_m_bready[{idx}])
        );
'''

        # Generate read converter only if master has read channels
        if master.has_read_channels():
            inst_str += f'''
        // Width Converter (READ) - Master {idx}: {master.port_name}
        axi4_dwidth_converter_rd #(
            .S_AXI_DATA_WIDTH({s_width}),
            .M_AXI_DATA_WIDTH({m_width}),
            .AXI_ID_WIDTH({master.id_width}),
            .AXI_ADDR_WIDTH({master.addr_width}),
            .AXI_USER_WIDTH(1)
        ) u_wconv_m{idx}_rd (
            .aclk         (aclk),
            .aresetn      (aresetn),
            // Slave interface (external master port)
            .s_axi_arid   ({prefix}arid),
            .s_axi_araddr ({prefix}araddr),
            .s_axi_arlen  ({prefix}arlen),
            .s_axi_arsize ({prefix}arsize),
            .s_axi_arburst({prefix}arburst),
            .s_axi_arlock ({prefix}arlock),
            .s_axi_arcache({prefix}arcache),
            .s_axi_arprot ({prefix}arprot),
            .s_axi_arqos  (4'b0),
            .s_axi_arregion(4'b0),
            .s_axi_aruser (1'b0),
            .s_axi_arvalid({prefix}arvalid),
            .s_axi_arready({prefix}arready),
            .s_axi_rid    ({prefix}rid),
            .s_axi_rdata  ({prefix}rdata),
            .s_axi_rresp  ({prefix}rresp),
            .s_axi_rlast  ({prefix}rlast),
            .s_axi_ruser  (/* unused */),
            .s_axi_rvalid ({prefix}rvalid),
            .s_axi_rready ({prefix}rready),
            // Master interface (to crossbar)
            .m_axi_arid   (xbar_m_arid[{idx}]),
            .m_axi_araddr (xbar_m_araddr[{idx}]),
            .m_axi_arlen  (xbar_m_arlen[{idx}]),
            .m_axi_arsize (xbar_m_arsize[{idx}]),
            .m_axi_arburst(xbar_m_arburst[{idx}]),
            .m_axi_arlock (xbar_m_arlock[{idx}]),
            .m_axi_arcache(xbar_m_arcache[{idx}]),
            .m_axi_arprot (xbar_m_arprot[{idx}]),
            .m_axi_arqos  (/* unused */),
            .m_axi_arregion(/* unused */),
            .m_axi_aruser (/* unused */),
            .m_axi_arvalid(xbar_m_arvalid[{idx}]),
            .m_axi_arready(xbar_m_arready[{idx}]),
            .m_axi_rid    (xbar_m_rid[{idx}]),
            .m_axi_rdata  (xbar_m_rdata[{idx}]),
            .m_axi_rresp  (xbar_m_rresp[{idx}]),
            .m_axi_rlast  (xbar_m_rlast[{idx}]),
            .m_axi_ruser  (1'b0),
            .m_axi_rvalid (xbar_m_rvalid[{idx}]),
            .m_axi_rready (xbar_m_rready[{idx}])
        );
        '''
        self.instruction(inst_str)

    def generate_master_connections(self):
        """Generate connections from external master ports to crossbar (with width converters if needed)"""
        self.comment("="*78)
        self.comment("Master Port Connections to Crossbar")
        self.comment("="*78)
        self.instruction("")

        for idx, master in enumerate(self.cfg.masters):
            prefix = master.prefix

            if master.needs_width_conv:
                # Instantiate width converter (upsize)
                self.generate_width_converter_master(idx, master)
                self.instruction("")
            else:
                # Direct connection - no width conversion needed
                channels_desc = f"[{master.channels.upper()}]" if master.channels != 'rw' else ""
                self.comment(f"Master {idx}: {master.port_name} {channels_desc} - Direct connection (no width conversion)")

                # Generate direct assignments (channel-specific)
                self.instruction(f"// Master {idx}: {master.port_name} {channels_desc} (direct connection)")
                assign_str = ''

                # Write channels
                if master.has_write_channels():
                    assign_str += f'''
                assign xbar_m_awaddr[{idx}]  = {prefix}awaddr;
                assign xbar_m_awid[{idx}]    = {prefix}awid;
                assign xbar_m_awlen[{idx}]   = {prefix}awlen;
                assign xbar_m_awsize[{idx}]  = {prefix}awsize;
                assign xbar_m_awburst[{idx}] = {prefix}awburst;
                assign xbar_m_awlock[{idx}]  = {prefix}awlock;
                assign xbar_m_awcache[{idx}] = {prefix}awcache;
                assign xbar_m_awprot[{idx}]  = {prefix}awprot;
                assign xbar_m_awvalid[{idx}] = {prefix}awvalid;
                assign {prefix}awready = xbar_m_awready[{idx}];

                assign xbar_m_wdata[{idx}]  = {prefix}wdata;
                assign xbar_m_wstrb[{idx}]  = {prefix}wstrb;
                assign xbar_m_wlast[{idx}]  = {prefix}wlast;
                assign xbar_m_wvalid[{idx}] = {prefix}wvalid;
                assign {prefix}wready = xbar_m_wready[{idx}];

                assign {prefix}bid    = xbar_m_bid[{idx}];
                assign {prefix}bresp  = xbar_m_bresp[{idx}];
                assign {prefix}bvalid = xbar_m_bvalid[{idx}];
                assign xbar_m_bready[{idx}] = {prefix}bready;
'''

                # Read channels
                if master.has_read_channels():
                    assign_str += f'''
                assign xbar_m_araddr[{idx}]  = {prefix}araddr;
                assign xbar_m_arid[{idx}]    = {prefix}arid;
                assign xbar_m_arlen[{idx}]   = {prefix}arlen;
                assign xbar_m_arsize[{idx}]  = {prefix}arsize;
                assign xbar_m_arburst[{idx}] = {prefix}arburst;
                assign xbar_m_arlock[{idx}]  = {prefix}arlock;
                assign xbar_m_arcache[{idx}] = {prefix}arcache;
                assign xbar_m_arprot[{idx}]  = {prefix}arprot;
                assign xbar_m_arvalid[{idx}] = {prefix}arvalid;
                assign {prefix}arready = xbar_m_arready[{idx}];

                assign {prefix}rdata  = xbar_m_rdata[{idx}];
                assign {prefix}rid    = xbar_m_rid[{idx}];
                assign {prefix}rresp  = xbar_m_rresp[{idx}];
                assign {prefix}rlast  = xbar_m_rlast[{idx}];
                assign {prefix}rvalid = xbar_m_rvalid[{idx}];
                assign xbar_m_rready[{idx}] = {prefix}rready;
'''

                self.instruction(assign_str)
                self.instruction("")

    def generate_apb_converter_slave(self, idx, slave):
        """Generate AXI2APB converter for APB slave ports"""
        prefix = slave.prefix

        self.comment(f"AXI2APB Converter for Slave {idx}: {slave.port_name}")
        self.comment(f"  Crossbar: {self.cfg.crossbar_data_width}b AXI4 → APB: {slave.data_width}b")
        self.comment("")
        self.comment("NOTE: The axi4_to_apb_convert module uses packed signals.")
        self.comment("      A wrapper module or signal packing logic is required.")
        self.comment("      For CSV-generated bridges, consider using axi4_to_apb_shim")
        self.comment("      or creating a wrapper that converts unpacked → packed.")
        self.comment("")

        # Generate intermediate AXI4 signals for the APB converter input
        inst_str = f'''
        // TODO: AXI2APB Converter - Slave {idx}: {slave.port_name}
        //
        // Recommended approach:
        // 1. Create intermediate 32b AXI4 signals between crossbar and APB converter
        // 2. Instantiate width downsize converter (512b → 32b) if needed
        // 3. Instantiate axi4_to_apb_convert or create unpacked-signal wrapper
        // 4. Connect APB output signals to external port
        //
        // Example structure:
        //
        // logic [{self.cfg.crossbar_addr_width}-1:0] s{idx}_axi_awaddr;
        // logic [7:0] s{idx}_axi_awid;
        // ... (all AXI4 signals)
        //
        // axi4_to_apb_convert #(
        //     .AXI_ADDR_WIDTH({self.cfg.crossbar_addr_width}),
        //     .AXI_DATA_WIDTH({slave.data_width}),
        //     .AXI_ID_WIDTH({self.cfg.crossbar_id_width}),
        //     .APB_ADDR_WIDTH({slave.addr_width}),
        //     .APB_DATA_WIDTH({slave.data_width})
        // ) u_axi2apb_s{idx} (
        //     .aclk    (aclk),
        //     .aresetn (aresetn),
        //     // AXI4 slave interface (from crossbar, packed signals)
        //     // ... packed signal connections
        //     // APB master interface
        //     .psel    ({prefix}psel),
        //     .penable ({prefix}penable),
        //     .paddr   ({prefix}paddr),
        //     .pwrite  ({prefix}pwrite),
        //     .pwdata  ({prefix}pwdata),
        //     .pstrb   ({prefix}pstrb),
        //     .pprot   ({prefix}pprot),
        //     .pready  ({prefix}pready),
        //     .prdata  ({prefix}prdata),
        //     .pslverr ({prefix}pslverr)
        // );
        '''
        self.instruction(inst_str)

    def generate_slave_connections(self):
        """Generate connections from crossbar to external slave ports (with converters if needed)"""
        self.comment("="*78)
        self.comment("Slave Port Connections from Crossbar")
        self.comment("="*78)
        self.instruction("")

        for idx, slave in enumerate(self.cfg.slaves):
            prefix = slave.prefix

            if slave.needs_axi2apb:
                # APB slave - needs AXI2APB converter (and possibly width converter)
                self.generate_apb_converter_slave(idx, slave)
                self.instruction("")
            elif slave.needs_width_conv:
                # AXI4 slave with width mismatch
                self.comment(f"Slave {idx}: {slave.port_name} - Needs width converter ({self.cfg.crossbar_data_width}b -> {slave.data_width}b)")
                self.comment("TODO: Width converter instance (slave-side downsize)")
                self.comment("      Use axi4_dwidth_converter_wr and axi4_dwidth_converter_rd")
                self.comment(f"      with S_AXI_DATA_WIDTH={self.cfg.crossbar_data_width}, M_AXI_DATA_WIDTH={slave.data_width}")
                self.instruction("")
            else:
                # Direct connection - AXI4 slave with matching width
                self.comment(f"Slave {idx}: {slave.port_name} - Direct connection (no conversion)")

                # Generate direct assignments
                self.instruction(f"// Slave {idx}: {slave.port_name} (direct connection)")
                assign_str = f'''
                assign {prefix}awaddr  = xbar_s_awaddr[{idx}];
                assign {prefix}awid    = xbar_s_awid[{idx}];
                assign {prefix}awlen   = xbar_s_awlen[{idx}];
                assign {prefix}awsize  = xbar_s_awsize[{idx}];
                assign {prefix}awburst = xbar_s_awburst[{idx}];
                assign {prefix}awlock  = xbar_s_awlock[{idx}];
                assign {prefix}awcache = xbar_s_awcache[{idx}];
                assign {prefix}awprot  = xbar_s_awprot[{idx}];
                assign {prefix}awvalid = xbar_s_awvalid[{idx}];
                assign xbar_s_awready[{idx}] = {prefix}awready;

                assign {prefix}wdata  = xbar_s_wdata[{idx}];
                assign {prefix}wstrb  = xbar_s_wstrb[{idx}];
                assign {prefix}wlast  = xbar_s_wlast[{idx}];
                assign {prefix}wvalid = xbar_s_wvalid[{idx}];
                assign xbar_s_wready[{idx}] = {prefix}wready;

                assign xbar_s_bid[{idx}]    = {prefix}bid;
                assign xbar_s_bresp[{idx}]  = {prefix}bresp;
                assign xbar_s_bvalid[{idx}] = {prefix}bvalid;
                assign {prefix}bready = xbar_s_bready[{idx}];

                assign {prefix}araddr  = xbar_s_araddr[{idx}];
                assign {prefix}arid    = xbar_s_arid[{idx}];
                assign {prefix}arlen   = xbar_s_arlen[{idx}];
                assign {prefix}arsize  = xbar_s_arsize[{idx}];
                assign {prefix}arburst = xbar_s_arburst[{idx}];
                assign {prefix}arlock  = xbar_s_arlock[{idx}];
                assign {prefix}arcache = xbar_s_arcache[{idx}];
                assign {prefix}arprot  = xbar_s_arprot[{idx}];
                assign {prefix}arvalid = xbar_s_arvalid[{idx}];
                assign xbar_s_arready[{idx}] = {prefix}arready;

                assign xbar_s_rdata[{idx}]  = {prefix}rdata;
                assign xbar_s_rid[{idx}]    = {prefix}rid;
                assign xbar_s_rresp[{idx}]  = {prefix}rresp;
                assign xbar_s_rlast[{idx}]  = {prefix}rlast;
                assign xbar_s_rvalid[{idx}] = {prefix}rvalid;
                assign {prefix}rready = xbar_s_rready[{idx}];
                '''
                self.instruction(assign_str)
                self.instruction("")

    def generate_crossbar_instance(self):
        """Generate internal AXI4 crossbar instance"""
        self.comment("="*78)
        self.comment("Internal AXI4 Crossbar Instance")
        self.comment("="*78)
        self.comment(f"Configuration: {len(self.cfg.masters)}x{len(self.cfg.slaves)} crossbar")
        self.comment(f"Data width: {self.cfg.crossbar_data_width}b")
        self.comment(f"Address width: {self.cfg.crossbar_addr_width}b")
        self.comment(f"ID width: {self.cfg.crossbar_id_width}b")
        self.instruction("")

        # Build address map for crossbar
        self.comment("Address map for crossbar routing:")
        for idx, slave in enumerate(self.cfg.slaves):
            addr_end = slave.base_addr + slave.addr_range - 1
            self.comment(f"  Slave {idx} ({slave.port_name}): 0x{slave.base_addr:08X} - 0x{addr_end:08X}")
        self.instruction("")

        # Generate crossbar instance
        nm = len(self.cfg.masters)
        ns = len(self.cfg.slaves)

        inst_str = f'''
        bridge_axi4_flat_{nm}x{ns} #(
            .NUM_MASTERS  (NUM_MASTERS),
            .NUM_SLAVES   (NUM_SLAVES),
            .DATA_WIDTH   (XBAR_DATA_WIDTH),
            .ADDR_WIDTH   (XBAR_ADDR_WIDTH),
            .ID_WIDTH     (XBAR_ID_WIDTH)
        ) u_crossbar (
            .aclk    (aclk),
            .aresetn (aresetn),

            // Master-side connections (from external masters)
            .s_axi_awaddr  (xbar_m_awaddr),
            .s_axi_awid    (xbar_m_awid),
            .s_axi_awlen   (xbar_m_awlen),
            .s_axi_awsize  (xbar_m_awsize),
            .s_axi_awburst (xbar_m_awburst),
            .s_axi_awlock  (xbar_m_awlock),
            .s_axi_awcache (xbar_m_awcache),
            .s_axi_awprot  (xbar_m_awprot),
            .s_axi_awvalid (xbar_m_awvalid),
            .s_axi_awready (xbar_m_awready),

            .s_axi_wdata  (xbar_m_wdata),
            .s_axi_wstrb  (xbar_m_wstrb),
            .s_axi_wlast  (xbar_m_wlast),
            .s_axi_wvalid (xbar_m_wvalid),
            .s_axi_wready (xbar_m_wready),

            .s_axi_bid    (xbar_m_bid),
            .s_axi_bresp  (xbar_m_bresp),
            .s_axi_bvalid (xbar_m_bvalid),
            .s_axi_bready (xbar_m_bready),

            .s_axi_araddr  (xbar_m_araddr),
            .s_axi_arid    (xbar_m_arid),
            .s_axi_arlen   (xbar_m_arlen),
            .s_axi_arsize  (xbar_m_arsize),
            .s_axi_arburst (xbar_m_arburst),
            .s_axi_arlock  (xbar_m_arlock),
            .s_axi_arcache (xbar_m_arcache),
            .s_axi_arprot  (xbar_m_arprot),
            .s_axi_arvalid (xbar_m_arvalid),
            .s_axi_arready (xbar_m_arready),

            .s_axi_rdata  (xbar_m_rdata),
            .s_axi_rid    (xbar_m_rid),
            .s_axi_rresp  (xbar_m_rresp),
            .s_axi_rlast  (xbar_m_rlast),
            .s_axi_rvalid (xbar_m_rvalid),
            .s_axi_rready (xbar_m_rready),

            // Slave-side connections (to external slaves)
            .m_axi_awaddr  (xbar_s_awaddr),
            .m_axi_awid    (xbar_s_awid),
            .m_axi_awlen   (xbar_s_awlen),
            .m_axi_awsize  (xbar_s_awsize),
            .m_axi_awburst (xbar_s_awburst),
            .m_axi_awlock  (xbar_s_awlock),
            .m_axi_awcache (xbar_s_awcache),
            .m_axi_awprot  (xbar_s_awprot),
            .m_axi_awvalid (xbar_s_awvalid),
            .m_axi_awready (xbar_s_awready),

            .m_axi_wdata  (xbar_s_wdata),
            .m_axi_wstrb  (xbar_s_wstrb),
            .m_axi_wlast  (xbar_s_wlast),
            .m_axi_wvalid (xbar_s_wvalid),
            .m_axi_wready (xbar_s_wready),

            .m_axi_bid    (xbar_s_bid),
            .m_axi_bresp  (xbar_s_bresp),
            .m_axi_bvalid (xbar_s_bvalid),
            .m_axi_bready (xbar_s_bready),

            .m_axi_araddr  (xbar_s_araddr),
            .m_axi_arid    (xbar_s_arid),
            .m_axi_arlen   (xbar_s_arlen),
            .m_axi_arsize  (xbar_s_arsize),
            .m_axi_arburst (xbar_s_arburst),
            .m_axi_arlock  (xbar_s_arlock),
            .m_axi_arcache (xbar_s_arcache),
            .m_axi_arprot  (xbar_s_arprot),
            .m_axi_arvalid (xbar_s_arvalid),
            .m_axi_arready (xbar_s_arready),

            .m_axi_rdata  (xbar_s_rdata),
            .m_axi_rid    (xbar_s_rid),
            .m_axi_rresp  (xbar_s_rresp),
            .m_axi_rlast  (xbar_s_rlast),
            .m_axi_rvalid (xbar_s_rvalid),
            .m_axi_rready (xbar_s_rready)
        );
        '''
        self.instruction(inst_str)
        self.instruction("")

    def generate_converter_instances(self):
        """Generate AXI2APB and width converter instances"""
        # Width converters and AXI2APB converters will be added in separate methods
        # Called from generate_master_connections() and generate_slave_connections()
        pass

    def verilog(self, file_path):
        """Generate complete RTL (main entry point)"""
        # Generate header comment
        self.comment("="*78)
        self.comment(f"Module: {self.module_str}")
        self.comment("CSV-Based Bridge Generator - Phase 2")
        self.comment("="*78)
        self.comment("")
        self.comment("Configuration:")
        self.comment(f"  Masters: {len(self.cfg.masters)}")
        for m in self.cfg.masters:
            self.comment(f"    - {m.port_name} ({m.protocol.upper()}, {m.data_width}b, prefix: {m.prefix})")
        self.comment(f"  Slaves: {len(self.cfg.slaves)}")
        for s in self.cfg.slaves:
            conv_str = ""
            if s.needs_axi2apb:
                conv_str += " +AXI2APB"
            if s.needs_width_conv:
                conv_str += f" +WIDTH({s.data_width}b)"
            self.comment(f"    - {s.port_name} ({s.protocol.upper()}, {s.data_width}b, prefix: {s.prefix}){conv_str}")
        self.comment("")
        self.comment(f"Internal Crossbar: {self.cfg.crossbar_data_width}b data, {self.cfg.crossbar_addr_width}b addr, {self.cfg.crossbar_id_width}b ID")
        self.comment("")
        self.comment("Generated from CSV configuration:")
        self.comment("  - Custom port prefixes from ports.csv")
        self.comment("  - Partial connectivity from connectivity.csv")
        self.comment("  - Automatic converter insertion (AXI2APB, width converters)")
        self.comment("")
        self.comment("Architecture:")
        self.comment("  External Masters -> [Width Conv] -> Internal Crossbar")
        self.comment("                                     -> [Width Conv] -> [AXI2APB] -> External Slaves")
        self.comment("="*78)
        self.instruction("")

        # Generate module structure
        self.generate_module_params()
        self.generate_all_ports()

        # Start module body
        self.start()

        # Generate internal signals
        self.generate_internal_signals()

        # Generate crossbar instance
        self.generate_crossbar_instance()

        # Generate master-side connections (external masters -> crossbar)
        self.generate_master_connections()

        # Generate slave-side connections (crossbar -> external slaves)
        self.generate_slave_connections()

        # End module
        self.end()

        # Write to file
        self.write(file_path, f'{self.module_name}.sv')


def main():
    parser = argparse.ArgumentParser(
        description="CSV-Based Bridge Generator with Protocol and Width Converters",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Generate bridge from CSV configuration
  python bridge_csv_generator.py --ports example_ports.csv --connectivity example_connectivity.csv --output ../rtl/

  # Specify custom output module name
  python bridge_csv_generator.py --ports my_ports.csv --connectivity my_connectivity.csv --name my_custom_bridge --output ../rtl/

Configuration Files:
  ports.csv        - Defines each master/slave port (protocol, widths, address ranges, prefixes)
  connectivity.csv - Defines which masters connect to which slaves (partial connectivity)
        """
    )

    parser.add_argument("--ports", type=str, required=True, help="Path to ports.csv configuration file")
    parser.add_argument("--connectivity", type=str, required=True, help="Path to connectivity.csv configuration file")
    parser.add_argument("--name", type=str, default=None, help="Output module name (default: auto-generated)")
    parser.add_argument("--output-dir", type=str, default="../rtl", help="Output directory for generated RTL")

    args = parser.parse_args()

    # Validate input files exist
    if not os.path.exists(args.ports):
        print(f"ERROR: Ports file not found: {args.ports}")
        sys.exit(1)

    if not os.path.exists(args.connectivity):
        print(f"ERROR: Connectivity file not found: {args.connectivity}")
        sys.exit(1)

    print("="*70)
    print("Bridge CSV Generator")
    print("="*70)

    # Parse CSV files
    masters, slaves = parse_ports_csv(args.ports)
    connectivity = parse_connectivity_csv(args.connectivity, masters, slaves)

    # Build configuration
    config = BridgeCSVConfig(
        masters=masters,
        slaves=slaves,
        connectivity=connectivity
    )

    # Determine crossbar configuration
    determine_crossbar_config(config)

    # Identify required converters
    identify_converters(config)

    # Generate output module name
    if args.name:
        output_name = args.name
    else:
        # Auto-generate name from configuration
        output_name = f"bridge_custom_{len(masters)}m_{len(slaves)}s"

    # Create output directory
    os.makedirs(args.output_dir, exist_ok=True)

    # Generate RTL
    generator = BridgeCSVGenerator(config, output_name)
    generator.verilog(args.output_dir)

    print(f"\n✓ Generated RTL: {args.output_dir}/{output_name}.sv")
    print(f"")
    print(f"⚠ NOTE: This is a PHASE 1 implementation (CSV parsing and structure)")
    print(f"  Phase 2 will add:")
    print(f"  - Complete port declarations with custom prefixes")
    print(f"  - Internal crossbar instantiation with partial connectivity")
    print(f"  - AXI2APB converter instances for APB slaves")
    print(f"  - Width converter instances for data width mismatches")
    print(f"")
    print(f"{'='*70}")
    print(f"✓ CSV-based bridge generation Phase 1 complete!")
    print(f"{'='*70}")


if __name__ == "__main__":
    main()
