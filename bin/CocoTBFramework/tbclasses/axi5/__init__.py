# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXI5 Testbench Classes Package
# Purpose: AXI5 testbench classes for CocoTB verification.
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-16

"""
AXI5 Testbench Classes Package

This package provides testbench classes for AXI5 protocol verification.
"""

from .axi5_master_read_tb import AXI5MasterReadTB
from .axi5_master_write_tb import AXI5MasterWriteTB
from .axi5_slave_read_tb import AXI5SlaveReadTB
from .axi5_slave_write_tb import AXI5SlaveWriteTB

__all__ = [
    'AXI5MasterReadTB',
    'AXI5MasterWriteTB',
    'AXI5SlaveReadTB',
    'AXI5SlaveWriteTB',
]
