# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXI5 Monitor Testbench Package
# Purpose: Monitor testbench classes for AXI5 protocol verification
#
# Author: sean galloway
# Created: 2025-12-20

"""
AXI5 Monitor Testbench Classes Package

This package provides testbench classes for AXI5 monitor verification.
"""

from .axi5_master_monitor_tb import AXI5MasterMonitorTB
from .axi5_slave_monitor_tb import AXI5SlaveMonitorTB

__all__ = [
    'AXI5MasterMonitorTB',
    'AXI5SlaveMonitorTB',
]
