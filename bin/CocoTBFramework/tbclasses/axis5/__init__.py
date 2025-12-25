# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXIS5 Testbench Classes
# Purpose: Testbench classes for AXI5-Stream protocol modules
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-21

"""
AXIS5 Testbench Classes

Testbench classes for AXI5-Stream protocol modules with AMBA5 extensions.
Includes both regular and clock-gated variants.
Follows the same patterns as AXIS4 testbenches but with TWAKEUP and TPARITY support.
"""

from .axis5_master_tb import AXIS5MasterTB
from .axis5_slave_tb import AXIS5SlaveTB
from .axis5_master_cg_tb import AXIS5MasterCGTB
from .axis5_slave_cg_tb import AXIS5SlaveCGTB

__all__ = [
    'AXIS5MasterTB',
    'AXIS5SlaveTB',
    'AXIS5MasterCGTB',
    'AXIS5SlaveCGTB'
]
