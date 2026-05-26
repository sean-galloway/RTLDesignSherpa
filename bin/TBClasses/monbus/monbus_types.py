# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ProtocolType
# Purpose: Monitor Bus Type Definitions - Updated for 3-bit Protocol Field
#
# Documentation: cocotb-framework PyPI package
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Monitor Bus Type Definitions - Updated for 3-bit Protocol Field

This module provides synchronized type definitions that match monitor_pkg.sv.
All packet parsing and field extraction functions have been updated for the new format.

UPDATED PACKET FORMAT (64 bits total):
- [63:60] - packet_type: 4 bits (error, timeout, completion, etc.)
- [59:57] - protocol:    3 bits (AXI/AXIS/APB/ARB/CORE) - ✅ INCREASED from 2 to 3 bits
- [56:53] - event_code:  4 bits (specific error or event code) - ✅ MOVED from [57:54]
- [52:47] - channel_id:  6 bits (channel ID and AXI ID) - ✅ UNCHANGED
- [46:43] - unit_id:     4 bits (subsystem identifier) - ✅ UNCHANGED
- [42:35] - agent_id:    8 bits (module identifier) - ✅ UNCHANGED
- [34:0]  - event_data:  35 bits (event-specific data) - ✅ REDUCED from 36 to 35 bits

Key Changes from Previous Version:
1. Protocol field expanded to 3 bits to support more protocols
2. Event data field reduced by 1 bit to accommodate protocol expansion
3. All field extraction functions updated for new bit positions
"""

from enum import IntEnum
from typing import List, Optional, Union, Dict, Any
from dataclasses import dataclass


# =============================================================================
# PROTOCOL DEFINITIONS - SYNCHRONIZED WITH monitor_pkg.sv
# =============================================================================

class ProtocolType(IntEnum):
    """Protocol types - synchronized with monitor_pkg.sv protocol_type_t"""
    PROTOCOL_AXI  = 0b000  # 0x0
    PROTOCOL_AXIS = 0b001  # 0x1
    PROTOCOL_APB  = 0b010  # 0x2
    PROTOCOL_ARB  = 0b011  # 0x3
    PROTOCOL_CORE = 0b100  # 0x4
    # 0b101-0b111 reserved for future use


# =============================================================================
# PACKET TYPE DEFINITIONS - SYNCHRONIZED WITH monitor_pkg.sv
# =============================================================================

class PktType(IntEnum):
    """Packet types - synchronized with monitor_pkg.sv"""
    PktTypeError      = 0x0  # Error event
    PktTypeCompletion = 0x1  # Transaction completion
    PktTypeThreshold  = 0x2  # Threshold crossed
    PktTypeTimeout    = 0x3  # Timeout event
    PktTypePerf       = 0x4  # Performance metric event
    PktTypeCredit     = 0x5  # Credit status (AXIS)
    PktTypeChannel    = 0x6  # Channel status (AXIS)
    PktTypeStream     = 0x7  # Stream event (AXIS)
    PktTypeAddrMatch  = 0x8  # Address match event (AXI)
    PktTypeAPB        = 0x9  # APB-specific event
    PktTypeReservedA  = 0xA  # Reserved
    PktTypeReservedB  = 0xB  # Reserved
    PktTypeReservedC  = 0xC  # Reserved
    PktTypeReservedD  = 0xD  # Reserved
    PktTypeReservedE  = 0xE  # Reserved
    PktTypeDebug      = 0xF  # Debug/trace event

    @classmethod
    def get_mask(cls, *packet_types) -> int:
        """Create a bitmask from multiple packet types"""
        mask = 0
        for pkt_type in packet_types:
            if isinstance(pkt_type, cls):
                mask |= (1 << pkt_type.value)
            elif isinstance(pkt_type, int):
                mask |= (1 << pkt_type)
        return mask


# =============================================================================
# ARB PROTOCOL EVENT CODES - SYNCHRONIZED WITH monitor_pkg.sv
# =============================================================================

class ARBErrorCode(IntEnum):
    """ARB Error Event Codes - synchronized with monitor_pkg.sv arb_error_code_t"""
    ARB_ERR_STARVATION         = 0x0  # Client request starvation
    ARB_ERR_ACK_TIMEOUT        = 0x1  # Grant ACK timeout  
    ARB_ERR_PROTOCOL_VIOLATION = 0x2  # ACK protocol violation
    ARB_ERR_CREDIT_VIOLATION   = 0x3  # Credit system violation
    ARB_ERR_FAIRNESS_VIOLATION = 0x4  # Weighted fairness violation
    ARB_ERR_WEIGHT_UNDERFLOW   = 0x5  # Weight credit underflow
    ARB_ERR_CONCURRENT_GRANTS  = 0x6  # Multiple simultaneous grants
    ARB_ERR_INVALID_GRANT_ID   = 0x7  # Invalid grant ID detected
    ARB_ERR_ORPHAN_ACK         = 0x8  # ACK without pending grant
    ARB_ERR_GRANT_OVERLAP      = 0x9  # Overlapping grant periods
    ARB_ERR_MASK_ERROR         = 0xA  # Round-robin mask error
    ARB_ERR_STATE_MACHINE      = 0xB  # FSM state error
    ARB_ERR_CONFIGURATION      = 0xC  # Invalid configuration
    ARB_ERR_RESERVED_D         = 0xD  # Reserved
    ARB_ERR_RESERVED_E         = 0xE  # Reserved
    ARB_ERR_USER_DEFINED       = 0xF  # User-defined error


class ARBTimeoutCode(IntEnum):
    """ARB Timeout Event Codes - synchronized with monitor_pkg.sv arb_timeout_code_t"""
    ARB_TIMEOUT_GRANT_ACK     = 0x0  # Grant ACK timeout
    ARB_TIMEOUT_REQUEST_HOLD  = 0x1  # Request held too long
    ARB_TIMEOUT_WEIGHT_UPDATE = 0x2  # Weight update timeout
    ARB_TIMEOUT_BLOCK_RELEASE = 0x3  # Block release timeout
    ARB_TIMEOUT_CREDIT_UPDATE = 0x4  # Credit update timeout
    ARB_TIMEOUT_STATE_CHANGE  = 0x5  # State machine timeout
    ARB_TIMEOUT_RESERVED_6    = 0x6  # Reserved
    ARB_TIMEOUT_RESERVED_7    = 0x7  # Reserved
    ARB_TIMEOUT_RESERVED_8    = 0x8  # Reserved
    ARB_TIMEOUT_RESERVED_9    = 0x9  # Reserved
    ARB_TIMEOUT_RESERVED_A    = 0xA  # Reserved
    ARB_TIMEOUT_RESERVED_B    = 0xB  # Reserved
    ARB_TIMEOUT_RESERVED_C    = 0xC  # Reserved
    ARB_TIMEOUT_RESERVED_D    = 0xD  # Reserved
    ARB_TIMEOUT_RESERVED_E    = 0xE  # Reserved
    ARB_TIMEOUT_USER_DEFINED  = 0xF  # User-defined timeout


class ARBCompletionCode(IntEnum):
    """ARB Completion Event Codes - synchronized with monitor_pkg.sv arb_completion_code_t"""
    ARB_COMPL_GRANT_ISSUED    = 0x0  # Grant successfully issued
    ARB_COMPL_ACK_RECEIVED    = 0x1  # ACK successfully received
    ARB_COMPL_TRANSACTION     = 0x2  # Complete transaction (grant+ack)
    ARB_COMPL_WEIGHT_UPDATE   = 0x3  # Weight update completed
    ARB_COMPL_CREDIT_CYCLE    = 0x4  # Credit cycle completed
    ARB_COMPL_FAIRNESS_PERIOD = 0x5  # Fairness analysis period
    ARB_COMPL_BLOCK_PERIOD    = 0x6  # Block period completed
    ARB_COMPL_RESERVED_7      = 0x7  # Reserved
    ARB_COMPL_RESERVED_8      = 0x8  # Reserved
    ARB_COMPL_RESERVED_9      = 0x9  # Reserved
    ARB_COMPL_RESERVED_A      = 0xA  # Reserved
    ARB_COMPL_RESERVED_B      = 0xB  # Reserved
    ARB_COMPL_RESERVED_C      = 0xC  # Reserved
    ARB_COMPL_RESERVED_D      = 0xD  # Reserved
    ARB_COMPL_RESERVED_E      = 0xE  # Reserved
    ARB_COMPL_USER_DEFINED    = 0xF  # User-defined completion


class ARBThresholdCode(IntEnum):
    """ARB Threshold Event Codes - synchronized with monitor_pkg.sv arb_threshold_code_t"""
    ARB_THRESH_REQUEST_LATENCY  = 0x0  # Request-to-grant latency threshold
    ARB_THRESH_ACK_LATENCY      = 0x1  # Grant-to-ACK latency threshold
    ARB_THRESH_FAIRNESS_DEV     = 0x2  # Fairness deviation threshold
    ARB_THRESH_ACTIVE_REQUESTS  = 0x3  # Active request count threshold
    ARB_THRESH_GRANT_RATE       = 0x4  # Grant rate threshold
    ARB_THRESH_EFFICIENCY       = 0x5  # Grant efficiency threshold
    ARB_THRESH_CREDIT_LOW       = 0x6  # Low credit threshold
    ARB_THRESH_WEIGHT_IMBALANCE = 0x7  # Weight imbalance threshold
    ARB_THRESH_STARVATION_TIME  = 0x8  # Starvation time threshold
    ARB_THRESH_RESERVED_9       = 0x9  # Reserved
    ARB_THRESH_RESERVED_A       = 0xA  # Reserved
    ARB_THRESH_RESERVED_B       = 0xB  # Reserved
    ARB_THRESH_RESERVED_C       = 0xC  # Reserved
    ARB_THRESH_RESERVED_D       = 0xD  # Reserved
    ARB_THRESH_RESERVED_E       = 0xE  # Reserved
    ARB_THRESH_USER_DEFINED     = 0xF  # User-defined threshold


class ARBPerformanceCode(IntEnum):
    """ARB Performance Event Codes - synchronized with monitor_pkg.sv arb_performance_code_t"""
    ARB_PERF_GRANT_ISSUED       = 0x0  # Grant issued event
    ARB_PERF_ACK_RECEIVED       = 0x1  # ACK received event
    ARB_PERF_GRANT_EFFICIENCY   = 0x2  # Grant completion efficiency
    ARB_PERF_FAIRNESS_METRIC    = 0x3  # Fairness compliance metric
    ARB_PERF_THROUGHPUT         = 0x4  # Arbitration throughput
    ARB_PERF_LATENCY_AVG        = 0x5  # Average latency measurement
    ARB_PERF_WEIGHT_COMPLIANCE  = 0x6  # Weight compliance metric
    ARB_PERF_CREDIT_UTILIZATION = 0x7  # Credit utilization efficiency
    ARB_PERF_CLIENT_ACTIVITY    = 0x8  # Per-client activity metric
    ARB_PERF_STARVATION_COUNT   = 0x9  # Starvation event count
    ARB_PERF_BLOCK_EFFICIENCY   = 0xA  # Block/unblock efficiency
    ARB_PERF_RESERVED_B         = 0xB  # Reserved
    ARB_PERF_RESERVED_C         = 0xC  # Reserved
    ARB_PERF_RESERVED_D         = 0xD  # Reserved
    ARB_PERF_RESERVED_E         = 0xE  # Reserved
    ARB_PERF_USER_DEFINED       = 0xF  # User-defined performance


class ARBDebugCode(IntEnum):
    """ARB Debug Event Codes - synchronized with monitor_pkg.sv arb_debug_code_t"""
    ARB_DEBUG_STATE_CHANGE     = 0x0  # Arbiter state machine change
    ARB_DEBUG_MASK_UPDATE      = 0x1  # Round-robin mask update
    ARB_DEBUG_WEIGHT_CHANGE    = 0x2  # Weight configuration change
    ARB_DEBUG_CREDIT_UPDATE    = 0x3  # Credit level update
    ARB_DEBUG_CLIENT_MASK      = 0x4  # Client enable/disable mask
    ARB_DEBUG_PRIORITY_CHANGE  = 0x5  # Priority level change
    ARB_DEBUG_BLOCK_EVENT      = 0x6  # Block/unblock event
    ARB_DEBUG_QUEUE_STATUS     = 0x7  # Request queue status
    ARB_DEBUG_COUNTER_SNAPSHOT = 0x8  # Counter values snapshot
    ARB_DEBUG_FIFO_STATUS      = 0x9  # FIFO status change
    ARB_DEBUG_FAIRNESS_STATE   = 0xA  # Fairness tracking state
    ARB_DEBUG_ACK_STATE        = 0xB  # ACK protocol state
    ARB_DEBUG_RESERVED_C       = 0xC  # Reserved
    ARB_DEBUG_RESERVED_D       = 0xD  # Reserved
    ARB_DEBUG_RESERVED_E       = 0xE  # Reserved
    ARB_DEBUG_USER_DEFINED     = 0xF  # User-defined debug


# =============================================================================
# AXI PROTOCOL EVENT CODES (Partial - for reference)
# =============================================================================

# =============================================================================
# AXI PROTOCOL EVENT CODES - FULL 16-ENTRY COVERAGE
# Auto-extracted from monitor_amba4_pkg.sv. If the SV adds entries,
# re-run the extractor at the bottom of this file and replace below.
# =============================================================================

class AXIErrorCode(IntEnum):
    """Auto-extracted from monitor_amba4_pkg::axi_error_code_t."""
    AXI_ERR_RESP_SLVERR            = 0x0  # Slave error response
    AXI_ERR_RESP_DECERR            = 0x1  # Decode error response
    AXI_ERR_DATA_ORPHAN            = 0x2  # Data without command
    AXI_ERR_RESP_ORPHAN            = 0x3  # Response without transaction
    AXI_ERR_PROTOCOL               = 0x4  # Protocol violation
    AXI_ERR_BURST_LENGTH           = 0x5  # Invalid burst length
    AXI_ERR_BURST_SIZE             = 0x6  # Invalid burst size
    AXI_ERR_BURST_TYPE             = 0x7  # Invalid burst type
    AXI_ERR_ID_COLLISION           = 0x8  # ID collision detected
    AXI_ERR_WRITE_BEFORE_ADDR      = 0x9  # Write data before address
    AXI_ERR_RESP_BEFORE_DATA       = 0xA  # Response before data complete
    AXI_ERR_LAST_MISSING           = 0xB  # Missing LAST signal
    AXI_ERR_STROBE_ERROR           = 0xC  # Write strobe error
    AXI_ERR_ADDR_RANGE             = 0xD  # Address-range violation (from axi_monitor_addr_check)
    AXI_ERR_RESERVED_E             = 0xE  # Reserved
    AXI_ERR_USER_DEFINED           = 0xF  # User-defined error


class AXITimeoutCode(IntEnum):
    """Auto-extracted from monitor_amba4_pkg::axi_timeout_code_t."""
    AXI_TIMEOUT_CMD                = 0x0  # Command/Address timeout
    AXI_TIMEOUT_DATA               = 0x1  # Data timeout
    AXI_TIMEOUT_RESP               = 0x2  # Response timeout
    AXI_TIMEOUT_HANDSHAKE          = 0x3  # Handshake timeout
    AXI_TIMEOUT_BURST              = 0x4  # Burst completion timeout
    AXI_TIMEOUT_EXCLUSIVE          = 0x5  # Exclusive access timeout
    AXI_TIMEOUT_RESERVED_6         = 0x6
    AXI_TIMEOUT_RESERVED_7         = 0x7
    AXI_TIMEOUT_RESERVED_8         = 0x8
    AXI_TIMEOUT_RESERVED_9         = 0x9
    AXI_TIMEOUT_RESERVED_A         = 0xA
    AXI_TIMEOUT_RESERVED_B         = 0xB
    AXI_TIMEOUT_RESERVED_C         = 0xC
    AXI_TIMEOUT_RESERVED_D         = 0xD
    AXI_TIMEOUT_RESERVED_E         = 0xE
    AXI_TIMEOUT_USER_DEFINED       = 0xF


class AXICompletionCode(IntEnum):
    """Auto-extracted from monitor_amba4_pkg::axi_completion_code_t."""
    AXI_COMPL_TRANS_COMPLETE       = 0x0  # Transaction completed successfully
    AXI_COMPL_READ_COMPLETE        = 0x1  # Read transaction complete
    AXI_COMPL_WRITE_COMPLETE       = 0x2  # Write transaction complete
    AXI_COMPL_BURST_COMPLETE       = 0x3  # Burst transaction complete
    AXI_COMPL_EXCLUSIVE_OK         = 0x4  # Exclusive access completed
    AXI_COMPL_EXCLUSIVE_FAIL       = 0x5  # Exclusive access failed
    AXI_COMPL_ATOMIC_OK            = 0x6  # Atomic operation completed
    AXI_COMPL_ATOMIC_FAIL          = 0x7  # Atomic operation failed
    AXI_COMPL_RESERVED_8           = 0x8
    AXI_COMPL_RESERVED_9           = 0x9
    AXI_COMPL_RESERVED_A           = 0xA
    AXI_COMPL_RESERVED_B           = 0xB
    AXI_COMPL_RESERVED_C           = 0xC
    AXI_COMPL_RESERVED_D           = 0xD
    AXI_COMPL_RESERVED_E           = 0xE
    AXI_COMPL_USER_DEFINED         = 0xF


class AXIThresholdCode(IntEnum):
    """Auto-extracted from monitor_amba4_pkg::axi_threshold_code_t."""
    AXI_THRESH_ACTIVE_COUNT        = 0x0  # Active transaction count threshold
    AXI_THRESH_LATENCY             = 0x1  # Latency threshold
    AXI_THRESH_ERROR_RATE          = 0x2  # Error rate threshold
    AXI_THRESH_THROUGHPUT          = 0x3  # Throughput threshold
    AXI_THRESH_QUEUE_DEPTH         = 0x4  # Queue depth threshold
    AXI_THRESH_BANDWIDTH           = 0x5  # Bandwidth utilization threshold
    AXI_THRESH_OUTSTANDING         = 0x6  # Outstanding transactions threshold
    AXI_THRESH_BURST_SIZE          = 0x7  # Average burst size threshold
    AXI_THRESH_RESERVED_8          = 0x8
    AXI_THRESH_RESERVED_9          = 0x9
    AXI_THRESH_RESERVED_A          = 0xA
    AXI_THRESH_RESERVED_B          = 0xB
    AXI_THRESH_RESERVED_C          = 0xC
    AXI_THRESH_RESERVED_D          = 0xD
    AXI_THRESH_RESERVED_E          = 0xE
    AXI_THRESH_USER_DEFINED        = 0xF


class AXIPerformanceCode(IntEnum):
    """Auto-extracted from monitor_amba4_pkg::axi_performance_code_t."""
    AXI_PERF_ADDR_LATENCY          = 0x0  # Address phase latency
    AXI_PERF_DATA_LATENCY          = 0x1  # Data phase latency
    AXI_PERF_RESP_LATENCY          = 0x2  # Response phase latency
    AXI_PERF_TOTAL_LATENCY         = 0x3  # Total transaction latency
    AXI_PERF_THROUGHPUT            = 0x4  # Transaction throughput
    AXI_PERF_ERROR_RATE            = 0x5  # Error rate
    AXI_PERF_ACTIVE_COUNT          = 0x6  # Current active transaction count
    AXI_PERF_COMPLETED_COUNT       = 0x7  # Total completed transaction count
    AXI_PERF_ERROR_COUNT           = 0x8  # Total error transaction count
    AXI_PERF_BANDWIDTH_UTIL        = 0x9  # Bandwidth utilization
    AXI_PERF_QUEUE_DEPTH           = 0xA  # Average queue depth
    AXI_PERF_BURST_EFFICIENCY      = 0xB  # Burst efficiency metric
    AXI_PERF_RESERVED_C            = 0xC
    AXI_PERF_RESERVED_D            = 0xD
    AXI_PERF_READ_WRITE_RATIO      = 0xE  # Read/Write transaction ratio
    AXI_PERF_USER_DEFINED          = 0xF


class AXIAddrMatchCode(IntEnum):
    """Auto-extracted from monitor_amba4_pkg::axi_addr_match_code_t."""
    AXI_ADDR_EXACT_MATCH           = 0x0  # Exact address match
    AXI_ADDR_RANGE_MATCH           = 0x1  # Address within range
    AXI_ADDR_MASK_MATCH             = 0x2  # Address mask match
    AXI_ADDR_PATTERN_MATCH         = 0x3  # Address pattern match
    AXI_ADDR_SEQUENTIAL            = 0x4  # Sequential address access
    AXI_ADDR_STRIDE_MATCH          = 0x5  # Stride pattern match
    AXI_ADDR_HOTSPOT               = 0x6  # Address hotspot detected
    AXI_ADDR_CONFLICT              = 0x7  # Address conflict detected
    AXI_ADDR_RESERVED_8            = 0x8
    AXI_ADDR_RESERVED_9            = 0x9
    AXI_ADDR_RESERVED_A            = 0xA
    AXI_ADDR_RESERVED_B            = 0xB
    AXI_ADDR_RESERVED_C            = 0xC
    AXI_ADDR_RESERVED_D            = 0xD
    AXI_ADDR_RESERVED_E            = 0xE
    AXI_ADDR_USER_DEFINED          = 0xF


class AXIDebugCode(IntEnum):
    """Auto-extracted from monitor_amba4_pkg::axi_debug_code_t."""
    AXI_DEBUG_STATE_CHANGE         = 0x0  # AXI state machine change
    AXI_DEBUG_PIPELINE_STALL       = 0x1  # Pipeline stall event
    AXI_DEBUG_BACKPRESSURE         = 0x2  # Backpressure event
    AXI_DEBUG_OUTSTANDING          = 0x3  # Outstanding transaction count
    AXI_DEBUG_REORDER_BUFFER       = 0x4  # Reorder buffer status
    AXI_DEBUG_ID_ALLOCATION        = 0x5  # Transaction ID allocation
    AXI_DEBUG_QOS_ESCALATION       = 0x6  # QoS escalation event
    AXI_DEBUG_HANDSHAKE            = 0x7  # Handshake timing event
    AXI_DEBUG_QUEUE_STATUS         = 0x8  # Queue status change
    AXI_DEBUG_COUNTER              = 0x9  # Counter snapshot
    AXI_DEBUG_FIFO_STATUS          = 0xA  # FIFO status
    AXI_DEBUG_RESERVED_B           = 0xB
    AXI_DEBUG_RESERVED_C           = 0xC
    AXI_DEBUG_RESERVED_D           = 0xD
    AXI_DEBUG_RESERVED_E           = 0xE
    AXI_DEBUG_USER_DEFINED         = 0xF


# =============================================================================
# APB PROTOCOL EVENT CODES - FULL 16-ENTRY COVERAGE
# =============================================================================

class APBErrorCode(IntEnum):
    """Auto-extracted from monitor_amba4_pkg::apb_error_code_t."""
    APB_ERR_PSLVERR                = 0x0  # Peripheral slave error
    APB_ERR_SETUP_VIOLATION        = 0x1  # Setup phase protocol violation
    APB_ERR_ACCESS_VIOLATION       = 0x2  # Access phase protocol violation
    APB_ERR_STROBE_ERROR           = 0x3  # Write strobe error
    APB_ERR_ADDR_DECODE            = 0x4  # Address decode error
    APB_ERR_PROT_VIOLATION         = 0x5  # Protection violation (PPROT)
    APB_ERR_ENABLE_ERROR           = 0x6  # Enable phase error
    APB_ERR_READY_ERROR            = 0x7  # PREADY protocol error
    APB_ERR_ADDR_RANGE             = 0x8  # Address-range violation
    APB_ERR_RESERVED_9             = 0x9
    APB_ERR_RESERVED_A             = 0xA
    APB_ERR_RESERVED_B             = 0xB
    APB_ERR_RESERVED_C             = 0xC
    APB_ERR_RESERVED_D             = 0xD
    APB_ERR_RESERVED_E             = 0xE
    APB_ERR_USER_DEFINED           = 0xF


class APBTimeoutCode(IntEnum):
    """Auto-extracted from monitor_amba4_pkg::apb_timeout_code_t."""
    APB_TIMEOUT_SETUP              = 0x0
    APB_TIMEOUT_ACCESS             = 0x1
    APB_TIMEOUT_ENABLE             = 0x2
    APB_TIMEOUT_PREADY_STUCK       = 0x3
    APB_TIMEOUT_TRANSFER           = 0x4
    APB_TIMEOUT_RESERVED_5         = 0x5
    APB_TIMEOUT_RESERVED_6         = 0x6
    APB_TIMEOUT_RESERVED_7         = 0x7
    APB_TIMEOUT_RESERVED_8         = 0x8
    APB_TIMEOUT_RESERVED_9         = 0x9
    APB_TIMEOUT_RESERVED_A         = 0xA
    APB_TIMEOUT_RESERVED_B         = 0xB
    APB_TIMEOUT_RESERVED_C         = 0xC
    APB_TIMEOUT_RESERVED_D         = 0xD
    APB_TIMEOUT_RESERVED_E         = 0xE
    APB_TIMEOUT_USER_DEFINED       = 0xF


class APBCompletionCode(IntEnum):
    """Auto-extracted from monitor_amba4_pkg::apb_completion_code_t."""
    APB_COMPL_TRANS_COMPLETE       = 0x0
    APB_COMPL_READ_COMPLETE        = 0x1
    APB_COMPL_WRITE_COMPLETE       = 0x2
    APB_COMPL_RESERVED_3           = 0x3
    APB_COMPL_RESERVED_4           = 0x4
    APB_COMPL_RESERVED_5           = 0x5
    APB_COMPL_RESERVED_6           = 0x6
    APB_COMPL_RESERVED_7           = 0x7
    APB_COMPL_RESERVED_8           = 0x8
    APB_COMPL_RESERVED_9           = 0x9
    APB_COMPL_RESERVED_A           = 0xA
    APB_COMPL_RESERVED_B           = 0xB
    APB_COMPL_RESERVED_C           = 0xC
    APB_COMPL_RESERVED_D           = 0xD
    APB_COMPL_RESERVED_E           = 0xE
    APB_COMPL_USER_DEFINED         = 0xF


class APBThresholdCode(IntEnum):
    """Auto-extracted from monitor_amba4_pkg::apb_threshold_code_t."""
    APB_THRESH_LATENCY             = 0x0
    APB_THRESH_ERROR_RATE          = 0x1
    APB_THRESH_ACTIVE_COUNT        = 0x2
    APB_THRESH_THROUGHPUT          = 0x3
    APB_THRESH_RESERVED_4          = 0x4
    APB_THRESH_RESERVED_5          = 0x5
    APB_THRESH_RESERVED_6          = 0x6
    APB_THRESH_RESERVED_7          = 0x7
    APB_THRESH_RESERVED_8          = 0x8
    APB_THRESH_RESERVED_9          = 0x9
    APB_THRESH_RESERVED_A          = 0xA
    APB_THRESH_RESERVED_B          = 0xB
    APB_THRESH_RESERVED_C          = 0xC
    APB_THRESH_RESERVED_D          = 0xD
    APB_THRESH_RESERVED_E          = 0xE
    APB_THRESH_USER_DEFINED        = 0xF


class APBPerformanceCode(IntEnum):
    """Auto-extracted from monitor_amba4_pkg::apb_performance_code_t."""
    APB_PERF_READ_LATENCY          = 0x0
    APB_PERF_WRITE_LATENCY         = 0x1
    APB_PERF_THROUGHPUT            = 0x2
    APB_PERF_ERROR_RATE            = 0x3
    APB_PERF_ACTIVE_COUNT          = 0x4
    APB_PERF_COMPLETED_COUNT       = 0x5
    APB_PERF_RESERVED_6            = 0x6
    APB_PERF_RESERVED_7            = 0x7
    APB_PERF_RESERVED_8            = 0x8
    APB_PERF_RESERVED_9            = 0x9
    APB_PERF_RESERVED_A            = 0xA
    APB_PERF_RESERVED_B            = 0xB
    APB_PERF_RESERVED_C            = 0xC
    APB_PERF_RESERVED_D            = 0xD
    APB_PERF_RESERVED_E            = 0xE
    APB_PERF_USER_DEFINED          = 0xF


class APBDebugCode(IntEnum):
    """Auto-extracted from monitor_amba4_pkg::apb_debug_code_t."""
    APB_DEBUG_STATE_CHANGE         = 0x0
    APB_DEBUG_SETUP_PHASE          = 0x1
    APB_DEBUG_ACCESS_PHASE         = 0x2
    APB_DEBUG_ENABLE_PHASE         = 0x3
    APB_DEBUG_PSEL_TRACE           = 0x4
    APB_DEBUG_PENABLE_TRACE        = 0x5
    APB_DEBUG_PREADY_TRACE         = 0x6
    APB_DEBUG_PPROT_TRACE          = 0x7
    APB_DEBUG_PSTRB_TRACE          = 0x8
    APB_DEBUG_RESERVED_9           = 0x9
    APB_DEBUG_RESERVED_A           = 0xA
    APB_DEBUG_RESERVED_B           = 0xB
    APB_DEBUG_RESERVED_C           = 0xC
    APB_DEBUG_RESERVED_D           = 0xD
    APB_DEBUG_RESERVED_E           = 0xE
    APB_DEBUG_USER_DEFINED         = 0xF


# =============================================================================
# AXIS PROTOCOL EVENT CODES - FULL 16-ENTRY COVERAGE
# =============================================================================

class AXISErrorCode(IntEnum):
    """Auto-extracted from monitor_amba4_pkg::axis_error_code_t."""
    AXIS_ERR_PROTOCOL              = 0x0
    AXIS_ERR_READY_TIMING          = 0x1
    AXIS_ERR_VALID_TIMING          = 0x2
    AXIS_ERR_LAST_MISSING          = 0x3
    AXIS_ERR_LAST_ORPHAN           = 0x4
    AXIS_ERR_STRB_INVALID          = 0x5
    AXIS_ERR_KEEP_INVALID          = 0x6
    AXIS_ERR_DATA_ALIGNMENT        = 0x7
    AXIS_ERR_ID_VIOLATION          = 0x8
    AXIS_ERR_DEST_VIOLATION        = 0x9
    AXIS_ERR_USER_VIOLATION        = 0xA
    AXIS_ERR_RESERVED_B            = 0xB
    AXIS_ERR_RESERVED_C            = 0xC
    AXIS_ERR_RESERVED_D            = 0xD
    AXIS_ERR_RESERVED_E            = 0xE
    AXIS_ERR_USER_DEFINED          = 0xF


class AXISTimeoutCode(IntEnum):
    """Auto-extracted from monitor_amba4_pkg::axis_timeout_code_t."""
    AXIS_TIMEOUT_HANDSHAKE         = 0x0
    AXIS_TIMEOUT_STREAM            = 0x1
    AXIS_TIMEOUT_PACKET            = 0x2
    AXIS_TIMEOUT_BACKPRESSURE      = 0x3
    AXIS_TIMEOUT_BUFFER            = 0x4
    AXIS_TIMEOUT_STALL             = 0x5
    AXIS_TIMEOUT_RESERVED_6        = 0x6
    AXIS_TIMEOUT_RESERVED_7        = 0x7
    AXIS_TIMEOUT_RESERVED_8        = 0x8
    AXIS_TIMEOUT_RESERVED_9        = 0x9
    AXIS_TIMEOUT_RESERVED_A        = 0xA
    AXIS_TIMEOUT_RESERVED_B        = 0xB
    AXIS_TIMEOUT_RESERVED_C        = 0xC
    AXIS_TIMEOUT_RESERVED_D        = 0xD
    AXIS_TIMEOUT_RESERVED_E        = 0xE
    AXIS_TIMEOUT_USER_DEFINED      = 0xF


class AXISCompletionCode(IntEnum):
    """Auto-extracted from monitor_amba4_pkg::axis_completion_code_t."""
    AXIS_COMPL_STREAM_END          = 0x0
    AXIS_COMPL_PACKET_SENT         = 0x1
    AXIS_COMPL_TRANSFER            = 0x2
    AXIS_COMPL_BURST_END           = 0x3
    AXIS_COMPL_HANDSHAKE           = 0x4
    AXIS_COMPL_RESERVED_5          = 0x5
    AXIS_COMPL_RESERVED_6          = 0x6
    AXIS_COMPL_RESERVED_7          = 0x7
    AXIS_COMPL_RESERVED_8          = 0x8
    AXIS_COMPL_RESERVED_9          = 0x9
    AXIS_COMPL_RESERVED_A          = 0xA
    AXIS_COMPL_RESERVED_B          = 0xB
    AXIS_COMPL_RESERVED_C          = 0xC
    AXIS_COMPL_RESERVED_D          = 0xD
    AXIS_COMPL_RESERVED_E          = 0xE
    AXIS_COMPL_USER_DEFINED        = 0xF


class AXISCreditCode(IntEnum):
    """Auto-extracted from monitor_amba4_pkg::axis_credit_code_t."""
    AXIS_CREDIT_READY_ASSERT       = 0x0
    AXIS_CREDIT_READY_DEASSERT     = 0x1
    AXIS_CREDIT_BUFFER_AVAILABLE   = 0x2
    AXIS_CREDIT_BUFFER_FULL        = 0x3
    AXIS_CREDIT_FLOW_CONTROL       = 0x4
    AXIS_CREDIT_BACKPRESSURE       = 0x5
    AXIS_CREDIT_THROUGHPUT         = 0x6
    AXIS_CREDIT_EFFICIENCY         = 0x7
    AXIS_CREDIT_RESERVED_8         = 0x8
    AXIS_CREDIT_RESERVED_9         = 0x9
    AXIS_CREDIT_RESERVED_A         = 0xA
    AXIS_CREDIT_RESERVED_B         = 0xB
    AXIS_CREDIT_RESERVED_C         = 0xC
    AXIS_CREDIT_RESERVED_D         = 0xD
    AXIS_CREDIT_RESERVED_E         = 0xE
    AXIS_CREDIT_USER_DEFINED       = 0xF


class AXISChannelCode(IntEnum):
    """Auto-extracted from monitor_amba4_pkg::axis_channel_code_t."""
    AXIS_CHAN_CONNECT              = 0x0
    AXIS_CHAN_DISCONNECT           = 0x1
    AXIS_CHAN_STALL                = 0x2
    AXIS_CHAN_RESUME               = 0x3
    AXIS_CHAN_CONGESTION           = 0x4
    AXIS_CHAN_ID_CHANGE            = 0x5
    AXIS_CHAN_DEST_CHANGE          = 0x6
    AXIS_CHAN_CONFIG_CHANGE        = 0x7
    AXIS_CHAN_RESERVED_8           = 0x8
    AXIS_CHAN_RESERVED_9           = 0x9
    AXIS_CHAN_RESERVED_A           = 0xA
    AXIS_CHAN_RESERVED_B           = 0xB
    AXIS_CHAN_RESERVED_C           = 0xC
    AXIS_CHAN_RESERVED_D           = 0xD
    AXIS_CHAN_RESERVED_E           = 0xE
    AXIS_CHAN_USER_DEFINED         = 0xF


class AXISStreamCode(IntEnum):
    """Auto-extracted from monitor_amba4_pkg::axis_stream_code_t."""
    AXIS_STREAM_START              = 0x0
    AXIS_STREAM_END                = 0x1
    AXIS_STREAM_PAUSE              = 0x2
    AXIS_STREAM_RESUME             = 0x3
    AXIS_STREAM_OVERFLOW           = 0x4
    AXIS_STREAM_UNDERFLOW          = 0x5
    AXIS_STREAM_TRANSFER           = 0x6
    AXIS_STREAM_IDLE               = 0x7
    AXIS_STREAM_RESERVED_8         = 0x8
    AXIS_STREAM_RESERVED_9         = 0x9
    AXIS_STREAM_RESERVED_A         = 0xA
    AXIS_STREAM_RESERVED_B         = 0xB
    AXIS_STREAM_RESERVED_C         = 0xC
    AXIS_STREAM_RESERVED_D         = 0xD
    AXIS_STREAM_RESERVED_E         = 0xE
    AXIS_STREAM_USER_DEFINED       = 0xF


# =============================================================================
# PACKET FIELD EXTRACTION FUNCTIONS - UPDATED FOR NEW FORMAT
# =============================================================================

def get_packet_type(packet: int) -> int:
    """Extract packet type from 64-bit monitor packet"""
    return (packet >> 60) & 0xF


def get_protocol(packet: int) -> int:
    """Extract protocol from 64-bit monitor packet - ✅ UPDATED for 3-bit field"""
    return (packet >> 57) & 0x7  # ✅ CHANGED: Now 3 bits at [59:57]


def get_event_code(packet: int) -> int:
    """Extract event code from 64-bit monitor packet - ✅ UPDATED bit position"""
    return (packet >> 53) & 0xF  # ✅ CHANGED: Now at [56:53] (was [57:54])


def get_channel_id(packet: int) -> int:
    """Extract channel ID from 64-bit monitor packet"""
    return (packet >> 47) & 0x3F  # ✅ UNCHANGED: 6 bits at [52:47]


def get_unit_id(packet: int) -> int:
    """Extract unit ID from 64-bit monitor packet"""
    return (packet >> 43) & 0xF  # ✅ UNCHANGED: 4 bits at [46:43]


def get_agent_id(packet: int) -> int:
    """Extract agent ID from 64-bit monitor packet"""
    return (packet >> 35) & 0xFF  # ✅ UNCHANGED: 8 bits at [42:35]


def get_event_data(packet: int) -> int:
    """Extract event data from 64-bit monitor packet - ✅ UPDATED for 35-bit field"""
    return packet & 0x7FFFFFFFF  # ✅ CHANGED: Now 35 bits [34:0] (was 36 bits)


def create_monitor_packet(packet_type: int, protocol: int, event_code: int, 
                         channel_id: int, unit_id: int, agent_id: int, 
                         event_data: int) -> int:
    """Create a 64-bit monitor packet from individual fields - ✅ UPDATED"""
    return (
        ((packet_type & 0xF) << 60) |      # [63:60] - 4 bits
        ((protocol & 0x7) << 57) |         # [59:57] - 3 bits ✅ UPDATED
        ((event_code & 0xF) << 53) |       # [56:53] - 4 bits ✅ UPDATED
        ((channel_id & 0x3F) << 47) |      # [52:47] - 6 bits
        ((unit_id & 0xF) << 43) |          # [46:43] - 4 bits
        ((agent_id & 0xFF) << 35) |        # [42:35] - 8 bits
        (event_data & 0x7FFFFFFFF)         # [34:0] - 35 bits ✅ UPDATED
    )


# =============================================================================
# PACKET ANALYSIS AND VALIDATION FUNCTIONS
# =============================================================================

def is_valid_protocol_type(protocol: int) -> bool:
    """Check if protocol type is valid"""
    return protocol in [p.value for p in ProtocolType]


def is_valid_packet_type(packet_type: int) -> bool:
    """Check if packet type is valid"""
    return packet_type in [p.value for p in PktType]


# (protocol, packet_type) -> IntEnum class that maps event_code -> name.
# Keep in lockstep with the monitor_amba4_pkg.sv enum coverage.
_EVENT_CODE_ENUM_LOOKUP = {
    (ProtocolType.PROTOCOL_ARB,  PktType.PktTypeError):      ARBErrorCode,
    (ProtocolType.PROTOCOL_ARB,  PktType.PktTypeTimeout):    ARBTimeoutCode,
    (ProtocolType.PROTOCOL_ARB,  PktType.PktTypeCompletion): ARBCompletionCode,
    (ProtocolType.PROTOCOL_ARB,  PktType.PktTypeThreshold):  ARBThresholdCode,
    (ProtocolType.PROTOCOL_ARB,  PktType.PktTypePerf):       ARBPerformanceCode,
    (ProtocolType.PROTOCOL_ARB,  PktType.PktTypeDebug):      ARBDebugCode,

    (ProtocolType.PROTOCOL_AXI,  PktType.PktTypeError):      AXIErrorCode,
    (ProtocolType.PROTOCOL_AXI,  PktType.PktTypeTimeout):    AXITimeoutCode,
    (ProtocolType.PROTOCOL_AXI,  PktType.PktTypeCompletion): AXICompletionCode,
    (ProtocolType.PROTOCOL_AXI,  PktType.PktTypeThreshold):  AXIThresholdCode,
    (ProtocolType.PROTOCOL_AXI,  PktType.PktTypePerf):       AXIPerformanceCode,
    (ProtocolType.PROTOCOL_AXI,  PktType.PktTypeAddrMatch):  AXIAddrMatchCode,
    (ProtocolType.PROTOCOL_AXI,  PktType.PktTypeDebug):      AXIDebugCode,

    (ProtocolType.PROTOCOL_APB,  PktType.PktTypeError):      APBErrorCode,
    (ProtocolType.PROTOCOL_APB,  PktType.PktTypeTimeout):    APBTimeoutCode,
    (ProtocolType.PROTOCOL_APB,  PktType.PktTypeCompletion): APBCompletionCode,
    (ProtocolType.PROTOCOL_APB,  PktType.PktTypeThreshold):  APBThresholdCode,
    (ProtocolType.PROTOCOL_APB,  PktType.PktTypePerf):       APBPerformanceCode,
    (ProtocolType.PROTOCOL_APB,  PktType.PktTypeDebug):      APBDebugCode,

    (ProtocolType.PROTOCOL_AXIS, PktType.PktTypeError):      AXISErrorCode,
    (ProtocolType.PROTOCOL_AXIS, PktType.PktTypeTimeout):    AXISTimeoutCode,
    (ProtocolType.PROTOCOL_AXIS, PktType.PktTypeCompletion): AXISCompletionCode,
    (ProtocolType.PROTOCOL_AXIS, PktType.PktTypeCredit):     AXISCreditCode,
    (ProtocolType.PROTOCOL_AXIS, PktType.PktTypeChannel):    AXISChannelCode,
    (ProtocolType.PROTOCOL_AXIS, PktType.PktTypeStream):     AXISStreamCode,
}


def get_event_code_enum(protocol: int, packet_type: int, event_code: int):
    """Return the IntEnum member matching (protocol, packet_type,
    event_code). Returns None when the (protocol, packet_type) pair
    has no Python enum defined or when event_code is out of range."""
    try:
        enum_cls = _EVENT_CODE_ENUM_LOOKUP.get(
            (ProtocolType(protocol), PktType(packet_type))
        )
    except ValueError:
        return None
    if enum_cls is None:
        return None
    try:
        return enum_cls(event_code)
    except ValueError:
        return None


def is_valid_event_code(protocol: int, packet_type: int, event_code: int) -> bool:
    """Check if an event code is valid for the given protocol and packet type."""
    return get_event_code_enum(protocol, packet_type, event_code) is not None


def get_event_code_name(protocol: int, packet_type: int, event_code: int) -> str:
    """Get human-readable name for an event code.

    Note: use `is not None` rather than truthiness, because the
    event_code=0 enum member is itself falsy (IntEnum inherits int
    truthiness), and the first entry in every code group is value 0.
    """
    enum_obj = get_event_code_enum(protocol, packet_type, event_code)
    if enum_obj is not None:
        return enum_obj.name
    return f"UNKNOWN_EVENT_{event_code:X}"


def get_protocol_name(protocol: int) -> str:
    """Get human-readable protocol name"""
    try:
        return ProtocolType(protocol).name
    except ValueError:
        return f"UNKNOWN_PROTOCOL_{protocol}"


def get_packet_type_name(packet_type: int) -> str:
    """Get human-readable packet type name"""
    try:
        return PktType(packet_type).name
    except ValueError:
        return f"UNKNOWN_PACKET_TYPE_{packet_type}"


# =============================================================================
# PACKET DATA STRUCTURE
# =============================================================================

@dataclass
class MonitorPacket:
    """Parsed monitor packet structure"""
    packet_type: int
    protocol: int
    event_code: int
    channel_id: int
    unit_id: int
    agent_id: int
    event_data: int
    raw_packet: int

    @classmethod
    def from_raw(cls, raw_packet: int) -> 'MonitorPacket':
        """Create MonitorPacket from raw 64-bit value"""
        return cls(
            packet_type=get_packet_type(raw_packet),
            protocol=get_protocol(raw_packet),
            event_code=get_event_code(raw_packet),
            channel_id=get_channel_id(raw_packet),
            unit_id=get_unit_id(raw_packet),
            agent_id=get_agent_id(raw_packet),
            event_data=get_event_data(raw_packet),
            raw_packet=raw_packet
        )

    def to_raw(self) -> int:
        """Convert back to raw 64-bit value"""
        return create_monitor_packet(
            self.packet_type, self.protocol, self.event_code,
            self.channel_id, self.unit_id, self.agent_id, self.event_data
        )

    def get_protocol_name(self) -> str:
        """Get human-readable protocol name"""
        return get_protocol_name(self.protocol)

    def get_packet_type_name(self) -> str:
        """Get human-readable packet type name"""
        return get_packet_type_name(self.packet_type)

    def get_event_code_name(self) -> str:
        """Get human-readable event code name"""
        return get_event_code_name(self.protocol, self.packet_type, self.event_code)

    def is_valid(self) -> bool:
        """Check if packet has valid field values"""
        return (
            is_valid_protocol_type(self.protocol) and
            is_valid_packet_type(self.packet_type) and
            is_valid_event_code(self.protocol, self.packet_type, self.event_code)
        )

    def matches(self, **criteria) -> bool:
        """Return True if every keyword argument matches the equivalent
        attribute on this packet. Useful for filtering a captured
        stream:

            error_pkts = [p for p in stream if p.matches(
                packet_type=PktType.PktTypeError,
                unit_id=2,                  # master-side wrappers
            )]

        Unknown attribute names raise AttributeError -- catches typos
        at filter-write time."""
        for key, expected in criteria.items():
            if not hasattr(self, key):
                raise AttributeError(
                    f"MonitorPacket has no attribute {key!r}; "
                    f"valid fields: packet_type, protocol, event_code, "
                    f"channel_id, unit_id, agent_id, event_data"
                )
            actual = getattr(self, key)
            # Normalise IntEnum vs raw int comparisons so callers can
            # mix-and-match (e.g. matches(packet_type=PktType.PktTypeError)
            # works against the raw int stored on the packet).
            if int(actual) != int(expected):
                return False
        return True

    def __str__(self) -> str:
        """Human-readable string representation"""
        return (
            f"[{self.get_protocol_name()}_{self.get_packet_type_name()}] "
            f"{self.get_event_code_name()} | "
            f"Agent:{self.agent_id:02X} Unit:{self.unit_id:X} Ch:{self.channel_id:02X} | "
            f"Data:{self.event_data:09X}"
        )


# =============================================================================
# HELPER FUNCTIONS FOR TESTING AND DEBUGGING
# =============================================================================

def validate_monitor_packet(packet: int) -> bool:
    """Validate that a monitor packet has valid field values"""
    try:
        parsed = MonitorPacket.from_raw(packet)
        return parsed.is_valid()
    except (ValueError, TypeError):
        return False


def debug_packet_bits(packet: int) -> str:
    """Return detailed bit-level breakdown of a monitor packet for debugging"""
    lines = []
    lines.append(f"Raw packet: 0x{packet:016X} (64-bit)")
    lines.append("Bit-level breakdown:")
    lines.append(f"  [63:60] packet_type = 0b{(packet >> 60) & 0xF:04b} (0x{(packet >> 60) & 0xF:X})")
    lines.append(f"  [59:57] protocol    = 0b{(packet >> 57) & 0x7:03b} (0x{(packet >> 57) & 0x7:X})")
    lines.append(f"  [56:53] event_code  = 0b{(packet >> 53) & 0xF:04b} (0x{(packet >> 53) & 0xF:X})")
    lines.append(f"  [52:47] channel_id  = 0b{(packet >> 47) & 0x3F:06b} (0x{(packet >> 47) & 0x3F:02X})")
    lines.append(f"  [46:43] unit_id     = 0b{(packet >> 43) & 0xF:04b} (0x{(packet >> 43) & 0xF:X})")
    lines.append(f"  [42:35] agent_id    = 0b{(packet >> 35) & 0xFF:08b} (0x{(packet >> 35) & 0xFF:02X})")
    lines.append(f"  [34:0]  event_data  = 0x{packet & 0x7FFFFFFFF:09X} ({packet & 0x7FFFFFFFF})")

    # Try to parse and show human-readable names
    try:
        parsed = MonitorPacket.from_raw(packet)
        lines.append("\nParsed fields:")
        lines.append(f"  Protocol: {parsed.get_protocol_name()}")
        lines.append(f"  Packet Type: {parsed.get_packet_type_name()}")
        lines.append(f"  Event Code: {parsed.get_event_code_name()}")
        lines.append(f"  Valid: {parsed.is_valid()}")
    except (ValueError, TypeError) as e:
        lines.append(f"\nParsing error: {e}")

    return "\n".join(lines)


def format_packet_fields(packet: int) -> Dict[str, Any]:
    """Format packet as dictionary with all field values"""
    return {
        'packet_type': get_packet_type(packet),
        'packet_type_name': get_packet_type_name(get_packet_type(packet)),
        'protocol': get_protocol(packet),
        'protocol_name': get_protocol_name(get_protocol(packet)),
        'event_code': get_event_code(packet),
        'event_code_name': get_event_code_name(get_protocol(packet), get_packet_type(packet), get_event_code(packet)),
        'channel_id': get_channel_id(packet),
        'unit_id': get_unit_id(packet),
        'agent_id': get_agent_id(packet),
        'event_data': get_event_data(packet),
        'raw_packet': packet
    }
