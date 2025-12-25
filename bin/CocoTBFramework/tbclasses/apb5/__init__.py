# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: APB5 Testbench Classes Package
# Purpose: APB5 testbench classes for CocoTB verification.
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-21

"""
APB5 Testbench Classes Package

This package provides testbench classes for APB5 protocol verification.
Includes support for AMBA5 extensions:
- User signals (PAUSER, PWUSER, PRUSER, PBUSER)
- Wake-up signaling (PWAKEUP)
- Parity protection (optional)
- Clock gating for power management
"""

from .apb5_master_tb import APB5MasterTB
from .apb5_slave_tb import APB5SlaveTB
from .apb5_command_handler import APB5CommandHandler
from .apb5_master_cg_tb import APB5MasterCGTB
from .apb5_slave_cg_tb import APB5SlaveCGTB

__all__ = [
    'APB5MasterTB',
    'APB5SlaveTB',
    'APB5CommandHandler',
    'APB5MasterCGTB',
    'APB5SlaveCGTB',
]
