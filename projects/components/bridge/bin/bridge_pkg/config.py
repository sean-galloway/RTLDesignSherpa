#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Configuration Data Structures for Bridge Generator

from dataclasses import dataclass, field
from typing import List, Dict

@dataclass
class PortSpec:
    """Specification for a single AXI4 port (master or slave)"""
    port_name: str          # Unique identifier (e.g., "cpu_master", "ddr_slave")
    direction: str          # "master" or "slave"
    protocol: str           # "axi4" or "apb"
    channels: str           # "rw" (read/write), "wr" (write-only), "rd" (read-only)
    prefix: str             # Signal prefix (e.g., "cpu_m_axi_", "ddr_s_axi_")
    data_width: int         # Data width in bits
    addr_width: int         # Address width in bits
    id_width: int = 0       # AXI ID width (0 for APB)
    base_addr: int = 0      # Slave base address (masters don't use)
    addr_range: int = 0     # Slave address range (masters don't use)
    enable_ooo: bool = False  # Slave supports out-of-order responses

    def has_write_channels(self) -> bool:
        """Returns True if this port has write channels (AW, W, B)"""
        return self.channels in ('wr', 'rw')

    def has_read_channels(self) -> bool:
        """Returns True if this port has read channels (AR, R)"""
        return self.channels in ('rd', 'rw')


@dataclass
class BridgeConfig:
    """Complete bridge configuration"""
    masters: List[PortSpec] = field(default_factory=list)
    slaves: List[PortSpec] = field(default_factory=list)
    connectivity: Dict[str, List[str]] = field(default_factory=dict)

    # Crossbar configuration (derived)
    crossbar_data_width: int = 0
    crossbar_addr_width: int = 0
    crossbar_id_width: int = 0        # Master-side ID width
    crossbar_slave_id_width: int = 0  # Slave-side ID width (master ID + routing bits)

    # Optional features
    expose_arbiter_signals: bool = False

    # Interface wrapper configuration
    enable_interface_wrappers: bool = True   # Use axi4_master/slave wrappers (timing)
    enable_monitoring: bool = False          # Use *_mon versions (debugging)

    # Skid buffer depths (per wrapper)
    skid_depth_ar: int = 2    # AR channel buffer depth
    skid_depth_aw: int = 2    # AW channel buffer depth
    skid_depth_w: int = 4     # W channel buffer depth (deeper for data)
    skid_depth_r: int = 2     # R channel buffer depth
    skid_depth_b: int = 2     # B channel buffer depth

    # Monitor configuration (only used if enable_monitoring=True)
    mon_error_enable: bool = True
    mon_compl_enable: bool = True
    mon_timeout_enable: bool = True
    mon_perf_enable: bool = False  # Avoid packet congestion

    def num_masters(self) -> int:
        return len(self.masters)

    def num_slaves(self) -> int:
        return len(self.slaves)

    def get_master_by_name(self, name: str) -> PortSpec:
        """Get master port by name"""
        for m in self.masters:
            if m.port_name == name:
                return m
        raise ValueError(f"Master '{name}' not found")

    def get_slave_by_name(self, name: str) -> PortSpec:
        """Get slave port by name"""
        for s in self.slaves:
            if s.port_name == name:
                return s
        raise ValueError(f"Slave '{name}' not found")
