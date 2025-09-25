"""
AXIS Components Package - AXI4-Stream Protocol Implementation

This package provides complete AXI4-Stream protocol support using the GAXI
infrastructure for consistent APIs and functionality.

Components:
- AXISMaster: Stream data transmission with flow control
- AXISSlave: Stream data reception with backpressure
- AXISMonitor: Stream transaction monitoring and analysis
- AXISPacket: Stream data packet representation

Factory Functions:
- create_axis_master()
- create_axis_slave() 
- create_axis_monitor()
- create_axis_testbench()

Field Configurations:
- AXISFieldConfigs: Stream field configuration factory

The API is designed to be similar to AXI4 components for consistency
while being optimized for stream protocol characteristics.
"""

from .axis_field_configs import AXISFieldConfigs
from .axis_packet import AXISPacket, create_axis_packet
from .axis_master import AXISMaster
from .axis_slave import AXISSlave
from .axis_monitor import AXISMonitor

from .axis_factories import (
    create_axis_master,
    create_axis_slave,
    create_axis_monitor,
    create_axis_master_interface,
    create_axis_slave_interface,
    create_axis_testbench,
    create_simple_axis_master,
    create_simple_axis_slave,
    get_axis_signal_map,
    print_axis_stats_to_log,
    get_axis_stats_summary
)

# Version information
__version__ = "1.0.0"
__author__ = "AXIS Framework Team"

# Export all public components
__all__ = [
    # Core classes
    'AXISMaster',
    'AXISSlave', 
    'AXISMonitor',
    'AXISPacket',
    'AXISFieldConfigs',
    
    # Factory functions
    'create_axis_master',
    'create_axis_slave',
    'create_axis_monitor',
    'create_axis_master_interface',
    'create_axis_slave_interface',
    'create_axis_testbench',
    'create_simple_axis_master',
    'create_simple_axis_slave',
    
    # Packet creation
    'create_axis_packet',
    
    # Utility functions
    'get_axis_signal_map',
    'print_axis_stats_to_log',
    'get_axis_stats_summary'
]
