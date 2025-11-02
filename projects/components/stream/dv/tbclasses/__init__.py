# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: __init__
# Purpose: STREAM Testbench Classes Package
#
# Documentation: projects/components/stream/PRD.md
# Subsystem: stream

"""
STREAM Testbench Classes

Provides reusable testbench classes for STREAM (Scatter-gather Transfer
Rapid Engine for AXI Memory) verification.

Available testbench classes:
- DescriptorEngineTB: Descriptor fetch and parsing testbench
- SchedulerTB: Transfer coordinator testbench (simplified from RAPIDS)
- MonbusAxilGroupTB: MonBus aggregation and AXIL interface testbench

These classes are PROJECT-SPECIFIC, not framework components.
"""

__all__ = [
    'DescriptorEngineTB',
    'SchedulerTB',
    'MonbusAxilGroupTB',
]
