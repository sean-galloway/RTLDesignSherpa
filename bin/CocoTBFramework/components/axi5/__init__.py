# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXI5 Components Package
# Purpose: AXI5 Protocol BFM components for CocoTB verification.
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-15

"""
AXI5 Protocol Components Package

This package provides Bus Functional Models (BFMs) for AXI5 protocol verification.
It includes master and slave interfaces for both read and write operations with
full support for AXI5-specific features.

AXI5 Features Supported:
- Atomic operations (ATOP)
- Memory Tagging Extension (MTE) - TAG, TAGOP, TAGUPDATE, TAGMATCH
- Memory Partitioning and Monitoring (MPAM)
- Memory Encryption Context (MECID)
- Non-secure Access ID (NSAID)
- Transaction Tracing (TRACE)
- Chunked transfers (CHUNKEN, CHUNKV, CHUNKNUM, CHUNKSTRB)
- Poison indicators (POISON)
- Unique/Exclusive access (UNIQUE)

Key Differences from AXI4:
- Removed: ARREGION, AWREGION
- Added: All signals listed above

Usage:
    from CocoTBFramework.components.axi5 import (
        # Factory functions
        create_axi5_master_rd,
        create_axi5_master_wr,
        create_axi5_slave_rd,
        create_axi5_slave_wr,
        # Packets
        AXI5Packet,
        create_simple_write_packets,
        create_atomic_transaction_packets,
        # Randomization
        AXI5RandomizationConfig,
        AXI5RandomizationManager,
        create_unified_randomization,
        # Compliance checking
        AXI5ComplianceChecker,
    )

    # Create master read interface
    master_rd = create_axi5_master_rd(dut, clock, prefix="m_axi_",
                                       data_width=64, id_width=4)

    # Perform read with AXI5 features
    responses = await master_rd['interface'].read_transaction(
        address=0x1000,
        burst_len=4,
        nsaid=1,
        trace=1,
        tagop=1,
    )
"""

# Field configuration helpers
from .axi5_field_configs import (
    AXI5FieldConfigHelper,
    get_axi5_field_configs,
    create_channel_field_config,
)

# Interface classes
from .axi5_interfaces import (
    AXI5MasterRead,
    AXI5MasterWrite,
    AXI5SlaveRead,
    AXI5SlaveWrite,
)

# Factory functions
from .axi5_factories import (
    create_axi5_master_rd,
    create_axi5_master_wr,
    create_axi5_slave_rd,
    create_axi5_slave_wr,
    create_axi5_master_interface,
    create_axi5_slave_interface,
    create_complete_axi5_testbench_components,
    create_axi5_with_mte,
    create_axi5_with_atomic,
    create_axi5_with_security,
)

# Transaction tracking
from .axi5_transaction import (
    AXI5Transaction,
    AXI5TransactionTracker,
)

# Packet classes and utilities
from .axi5_packet import (
    AXI5Packet,
    create_simple_write_packets,
    create_simple_read_packet,
    create_atomic_write_packets,
    create_tagged_write_packets,
)

# Packet utility functions
from .axi5_packet_utils import (
    create_simple_read_packet as create_ar_packet,
    create_simple_write_address_packet,
    create_simple_write_data_packet,
    create_simple_read_response_packet,
    create_simple_write_response_packet,
    create_burst_write_packets,
    create_burst_read_response_packets,
    create_atomic_transaction_packets,
    create_tagged_write_packets as create_mte_write_packets,
    create_tagged_read_packet,
    create_chunked_read_packet,
    create_secure_write_packets,
    create_traced_write_packets,
)

# Randomization configuration
from .axi5_randomization_config import (
    AXI5RandomizationProfile,
    AXI5ProtocolMode,
    AXI5ConstraintSet,
    AXI5RandomizationConfig,
    create_atomic_randomization_config,
    create_mte_randomization_config,
    create_security_randomization_config,
    create_compliance_randomization_config,
)

# Randomization manager
from .axi5_randomization_manager import (
    AXI5TimingConfig,
    create_axi5_timing_config,
    AXI5RandomizationManager,
    create_unified_randomization,
    create_compliance_randomization,
    create_performance_randomization,
    create_atomic_randomization,
    create_mte_randomization,
    create_security_randomization,
    create_error_injection_randomization,
)

# Timing configuration
from .axi5_timing_config import (
    create_axi5_timing_from_profile,
    get_axi5_timing_profiles,
    create_axi5_randomizer_configs,
    get_timing_for_axi5_feature,
)

# Compliance checking
from .axi5_compliance_checker import (
    AXI5ViolationType,
    AXI5Violation,
    AXI5ComplianceChecker,
    add_axi5_compliance_checking,
)

__all__ = [
    # Field configs
    'AXI5FieldConfigHelper',
    'get_axi5_field_configs',
    'create_channel_field_config',

    # Interfaces
    'AXI5MasterRead',
    'AXI5MasterWrite',
    'AXI5SlaveRead',
    'AXI5SlaveWrite',

    # Factories
    'create_axi5_master_rd',
    'create_axi5_master_wr',
    'create_axi5_slave_rd',
    'create_axi5_slave_wr',
    'create_axi5_master_interface',
    'create_axi5_slave_interface',
    'create_complete_axi5_testbench_components',
    'create_axi5_with_mte',
    'create_axi5_with_atomic',
    'create_axi5_with_security',

    # Transactions
    'AXI5Transaction',
    'AXI5TransactionTracker',

    # Packets
    'AXI5Packet',
    'create_simple_write_packets',
    'create_simple_read_packet',
    'create_atomic_write_packets',
    'create_tagged_write_packets',

    # Packet utilities
    'create_ar_packet',
    'create_simple_write_address_packet',
    'create_simple_write_data_packet',
    'create_simple_read_response_packet',
    'create_simple_write_response_packet',
    'create_burst_write_packets',
    'create_burst_read_response_packets',
    'create_atomic_transaction_packets',
    'create_mte_write_packets',
    'create_tagged_read_packet',
    'create_chunked_read_packet',
    'create_secure_write_packets',
    'create_traced_write_packets',

    # Randomization config
    'AXI5RandomizationProfile',
    'AXI5ProtocolMode',
    'AXI5ConstraintSet',
    'AXI5RandomizationConfig',
    'create_atomic_randomization_config',
    'create_mte_randomization_config',
    'create_security_randomization_config',
    'create_compliance_randomization_config',

    # Randomization manager
    'AXI5TimingConfig',
    'create_axi5_timing_config',
    'AXI5RandomizationManager',
    'create_unified_randomization',
    'create_compliance_randomization',
    'create_performance_randomization',
    'create_atomic_randomization',
    'create_mte_randomization',
    'create_security_randomization',
    'create_error_injection_randomization',

    # Timing config
    'create_axi5_timing_from_profile',
    'get_axi5_timing_profiles',
    'create_axi5_randomizer_configs',
    'get_timing_for_axi5_feature',

    # Compliance checking
    'AXI5ViolationType',
    'AXI5Violation',
    'AXI5ComplianceChecker',
    'add_axi5_compliance_checking',
]
