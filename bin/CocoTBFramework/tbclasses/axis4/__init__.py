"""
AXIS4 Testbench Classes

Testbench classes for AXI4-Stream protocol modules.
Includes both regular and clock-gated variants.
Follows the same patterns as AXI4 and AXIL4 testbenches.
"""

from .axis_master_tb import AXISMasterTB
from .axis_slave_tb import AXISSlaveTB
from .axis_master_cg_tb import AXISMasterCGTB
from .axis_slave_cg_tb import AXISSlaveCGTB

__all__ = [
    'AXISMasterTB',
    'AXISSlaveTB',
    'AXISMasterCGTB',
    'AXISSlaveCGTB'
]