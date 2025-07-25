"""
MonBus Types and Enumerations

This module contains all the protocol types, packet types, and event code enumerations
for the MonBus monitoring system. It mirrors the SystemVerilog monitor_pkg definitions.
"""

from enum import IntEnum
from typing import Dict, Optional, Union


# =============================================================================
# PROTOCOL AND PACKET TYPE DEFINITIONS
# =============================================================================

class ProtocolType(IntEnum):
    """Protocol type enumeration - mirrors protocol_type_t"""
    AXI = 0x0
    NOC = 0x1  # Network on Chip
    APB = 0x2  # Advanced Peripheral Bus
    CUSTOM = 0x3


class PktType(IntEnum):
    """Monitor bus packet types - mirrors PktType* constants"""
    ERROR = 0x0       # PktTypeError
    COMPLETION = 0x1  # PktTypeCompletion
    THRESHOLD = 0x2   # PktTypeThreshold
    TIMEOUT = 0x3     # PktTypeTimeout
    PERF = 0x4        # PktTypePerf
    CREDIT = 0x5      # PktTypeCredit
    CHANNEL = 0x6     # PktTypeChannel
    STREAM = 0x7      # PktTypeStream
    ADDR_MATCH = 0x8  # PktTypeAddrMatch
    APB = 0x9         # PktTypeAPB
    RESERVED_A = 0xA  # PktTypeReserved_A
    RESERVED_B = 0xB  # PktTypeReserved_B
    RESERVED_C = 0xC  # PktTypeReserved_C
    RESERVED_D = 0xD  # PktTypeReserved_D
    RESERVED_E = 0xE  # PktTypeReserved_E
    DEBUG = 0xF       # PktTypeDebug


# Keep original names for backward compatibility
MonbusProtocol = ProtocolType
MonbusPktType = PktType


# =============================================================================
# AXI PROTOCOL EVENT CODES
# =============================================================================

class AXIErrorCode(IntEnum):
    """AXI Error Events - mirrors axi_error_code_t"""
    RESP_SLVERR = 0x0         # AXI_ERR_RESP_SLVERR
    RESP_DECERR = 0x1         # AXI_ERR_RESP_DECERR
    DATA_ORPHAN = 0x2         # AXI_ERR_DATA_ORPHAN
    RESP_ORPHAN = 0x3         # AXI_ERR_RESP_ORPHAN
    PROTOCOL = 0x4            # AXI_ERR_PROTOCOL
    BURST_LENGTH = 0x5        # AXI_ERR_BURST_LENGTH
    BURST_SIZE = 0x6          # AXI_ERR_BURST_SIZE
    BURST_TYPE = 0x7          # AXI_ERR_BURST_TYPE
    ID_COLLISION = 0x8        # AXI_ERR_ID_COLLISION
    WRITE_BEFORE_ADDR = 0x9   # AXI_ERR_WRITE_BEFORE_ADDR
    RESP_BEFORE_DATA = 0xA    # AXI_ERR_RESP_BEFORE_DATA
    LAST_MISSING = 0xB        # AXI_ERR_LAST_MISSING
    STROBE_ERROR = 0xC        # AXI_ERR_STROBE_ERROR
    ARBITER_STARVATION = 0xD  # AXI_ERR_ARBITER_STARVATION
    CREDIT_VIOLATION = 0xE    # AXI_ERR_CREDIT_VIOLATION
    USER_DEFINED = 0xF        # AXI_ERR_USER_DEFINED


class AXITimeoutCode(IntEnum):
    """AXI Timeout Events - mirrors axi_timeout_code_t"""
    CMD = 0x0              # AXI_TIMEOUT_CMD
    DATA = 0x1             # AXI_TIMEOUT_DATA
    RESP = 0x2             # AXI_TIMEOUT_RESP
    HANDSHAKE = 0x3        # AXI_TIMEOUT_HANDSHAKE
    BURST = 0x4            # AXI_TIMEOUT_BURST
    EXCLUSIVE = 0x5        # AXI_TIMEOUT_EXCLUSIVE
    RESERVED_6 = 0x6       # AXI_TIMEOUT_RESERVED_6
    RESERVED_7 = 0x7       # AXI_TIMEOUT_RESERVED_7
    RESERVED_8 = 0x8       # AXI_TIMEOUT_RESERVED_8
    RESERVED_9 = 0x9       # AXI_TIMEOUT_RESERVED_9
    RESERVED_A = 0xA       # AXI_TIMEOUT_RESERVED_A
    RESERVED_B = 0xB       # AXI_TIMEOUT_RESERVED_B
    RESERVED_C = 0xC       # AXI_TIMEOUT_RESERVED_C
    RESERVED_D = 0xD       # AXI_TIMEOUT_RESERVED_D
    RESERVED_E = 0xE       # AXI_TIMEOUT_RESERVED_E
    USER_DEFINED = 0xF     # AXI_TIMEOUT_USER_DEFINED


class AXICompletionCode(IntEnum):
    """AXI Completion Events - mirrors axi_completion_code_t"""
    TRANS_COMPLETE = 0x0   # AXI_COMPL_TRANS_COMPLETE
    READ_COMPLETE = 0x1    # AXI_COMPL_READ_COMPLETE
    WRITE_COMPLETE = 0x2   # AXI_COMPL_WRITE_COMPLETE
    BURST_COMPLETE = 0x3   # AXI_COMPL_BURST_COMPLETE
    EXCLUSIVE_OK = 0x4     # AXI_COMPL_EXCLUSIVE_OK
    EXCLUSIVE_FAIL = 0x5   # AXI_COMPL_EXCLUSIVE_FAIL
    ATOMIC_OK = 0x6        # AXI_COMPL_ATOMIC_OK
    ATOMIC_FAIL = 0x7      # AXI_COMPL_ATOMIC_FAIL
    RESERVED_8 = 0x8       # AXI_COMPL_RESERVED_8
    RESERVED_9 = 0x9       # AXI_COMPL_RESERVED_9
    RESERVED_A = 0xA       # AXI_COMPL_RESERVED_A
    RESERVED_B = 0xB       # AXI_COMPL_RESERVED_B
    RESERVED_C = 0xC       # AXI_COMPL_RESERVED_C
    RESERVED_D = 0xD       # AXI_COMPL_RESERVED_D
    RESERVED_E = 0xE       # AXI_COMPL_RESERVED_E
    USER_DEFINED = 0xF     # AXI_COMPL_USER_DEFINED


class AXIThresholdCode(IntEnum):
    """AXI Threshold Events - mirrors axi_threshold_code_t"""
    ACTIVE_COUNT = 0x0     # AXI_THRESH_ACTIVE_COUNT
    LATENCY = 0x1          # AXI_THRESH_LATENCY
    ERROR_RATE = 0x2       # AXI_THRESH_ERROR_RATE
    THROUGHPUT = 0x3       # AXI_THRESH_THROUGHPUT
    QUEUE_DEPTH = 0x4      # AXI_THRESH_QUEUE_DEPTH
    BANDWIDTH = 0x5        # AXI_THRESH_BANDWIDTH
    OUTSTANDING = 0x6      # AXI_THRESH_OUTSTANDING
    BURST_SIZE = 0x7       # AXI_THRESH_BURST_SIZE
    GRANT_LATENCY = 0x8    # AXI_THRESH_GRANT_LATENCY
    FAIRNESS = 0x9         # AXI_THRESH_FAIRNESS
    RESERVED_A = 0xA       # AXI_THRESH_RESERVED_A
    RESERVED_B = 0xB       # AXI_THRESH_RESERVED_B
    RESERVED_C = 0xC       # AXI_THRESH_RESERVED_C
    RESERVED_D = 0xD       # AXI_THRESH_RESERVED_D
    RESERVED_E = 0xE       # AXI_THRESH_RESERVED_E
    USER_DEFINED = 0xF     # AXI_THRESH_USER_DEFINED


class AXIPerformanceCode(IntEnum):
    """AXI Performance Events - mirrors axi_performance_code_t"""
    ADDR_LATENCY = 0x0       # AXI_PERF_ADDR_LATENCY
    DATA_LATENCY = 0x1       # AXI_PERF_DATA_LATENCY
    RESP_LATENCY = 0x2       # AXI_PERF_RESP_LATENCY
    TOTAL_LATENCY = 0x3      # AXI_PERF_TOTAL_LATENCY
    THROUGHPUT = 0x4         # AXI_PERF_THROUGHPUT
    ERROR_RATE = 0x5         # AXI_PERF_ERROR_RATE
    ACTIVE_COUNT = 0x6       # AXI_PERF_ACTIVE_COUNT
    COMPLETED_COUNT = 0x7    # AXI_PERF_COMPLETED_COUNT
    ERROR_COUNT = 0x8        # AXI_PERF_ERROR_COUNT
    BANDWIDTH_UTIL = 0x9     # AXI_PERF_BANDWIDTH_UTIL
    QUEUE_DEPTH = 0xA        # AXI_PERF_QUEUE_DEPTH
    BURST_EFFICIENCY = 0xB   # AXI_PERF_BURST_EFFICIENCY
    GRANT_EFFICIENCY = 0xC   # AXI_PERF_GRANT_EFFICIENCY
    WEIGHT_COMPLIANCE = 0xD  # AXI_PERF_WEIGHT_COMPLIANCE
    READ_WRITE_RATIO = 0xE   # AXI_PERF_READ_WRITE_RATIO
    USER_DEFINED = 0xF       # AXI_PERF_USER_DEFINED


class AXIAddrMatchCode(IntEnum):
    """AXI Address Match Events - mirrors axi_addr_match_code_t"""
    DESC = 0x0             # AXI_ADDR_MATCH_DESC
    DATA = 0x1             # AXI_ADDR_MATCH_DATA
    READ = 0x2             # AXI_ADDR_MATCH_READ
    WRITE = 0x3            # AXI_ADDR_MATCH_WRITE
    RANGE = 0x4            # AXI_ADDR_MATCH_RANGE
    EXACT = 0x5            # AXI_ADDR_MATCH_EXACT
    MASK = 0x6             # AXI_ADDR_MATCH_MASK
    BURST = 0x7            # AXI_ADDR_MATCH_BURST
    CACHEABLE = 0x8        # AXI_ADDR_MATCH_CACHEABLE
    DEVICE = 0x9           # AXI_ADDR_MATCH_DEVICE
    SECURE = 0xA           # AXI_ADDR_MATCH_SECURE
    RESERVED_B = 0xB       # AXI_ADDR_MATCH_RESERVED_B
    RESERVED_C = 0xC       # AXI_ADDR_MATCH_RESERVED_C
    RESERVED_D = 0xD       # AXI_ADDR_MATCH_RESERVED_D
    RESERVED_E = 0xE       # AXI_ADDR_MATCH_RESERVED_E
    USER_DEFINED = 0xF     # AXI_ADDR_MATCH_USER_DEFINED


class AXIDebugCode(IntEnum):
    """AXI Debug Events - mirrors axi_debug_code_t"""
    STATE_CHANGE = 0x0     # AXI_DEBUG_STATE_CHANGE
    ADDR_PHASE = 0x1       # AXI_DEBUG_ADDR_PHASE
    DATA_PHASE = 0x2       # AXI_DEBUG_DATA_PHASE
    RESP_PHASE = 0x3       # AXI_DEBUG_RESP_PHASE
    TRANS_CREATE = 0x4     # AXI_DEBUG_TRANS_CREATE
    TRANS_REMOVE = 0x5     # AXI_DEBUG_TRANS_REMOVE
    ID_ALLOCATION = 0x6    # AXI_DEBUG_ID_ALLOCATION
    HANDSHAKE = 0x7        # AXI_DEBUG_HANDSHAKE
    QUEUE_STATUS = 0x8     # AXI_DEBUG_QUEUE_STATUS
    COUNTER = 0x9          # AXI_DEBUG_COUNTER
    FIFO_STATUS = 0xA      # AXI_DEBUG_FIFO_STATUS
    CREDIT_STATUS = 0xB    # AXI_DEBUG_CREDIT_STATUS
    ARBITER_STATE = 0xC    # AXI_DEBUG_ARBITER_STATE
    BLOCK_EVENT = 0xD      # AXI_DEBUG_BLOCK_EVENT
    RESERVED_E = 0xE       # AXI_DEBUG_RESERVED_E
    USER_DEFINED = 0xF     # AXI_DEBUG_USER_DEFINED


# =============================================================================
# APB PROTOCOL EVENT CODES
# =============================================================================

class APBErrorCode(IntEnum):
    """APB Error Events - mirrors apb_error_code_t"""
    PSLVERR = 0x0            # APB_ERR_PSLVERR
    SETUP_VIOLATION = 0x1    # APB_ERR_SETUP_VIOLATION
    ACCESS_VIOLATION = 0x2   # APB_ERR_ACCESS_VIOLATION
    STROBE_ERROR = 0x3       # APB_ERR_STROBE_ERROR
    ADDR_DECODE = 0x4        # APB_ERR_ADDR_DECODE
    PROT_VIOLATION = 0x5     # APB_ERR_PROT_VIOLATION
    ENABLE_ERROR = 0x6       # APB_ERR_ENABLE_ERROR
    READY_ERROR = 0x7        # APB_ERR_READY_ERROR
    RESERVED_8 = 0x8         # APB_ERR_RESERVED_8
    RESERVED_9 = 0x9         # APB_ERR_RESERVED_9
    RESERVED_A = 0xA         # APB_ERR_RESERVED_A
    RESERVED_B = 0xB         # APB_ERR_RESERVED_B
    RESERVED_C = 0xC         # APB_ERR_RESERVED_C
    RESERVED_D = 0xD         # APB_ERR_RESERVED_D
    RESERVED_E = 0xE         # APB_ERR_RESERVED_E
    USER_DEFINED = 0xF       # APB_ERR_USER_DEFINED


class APBTimeoutCode(IntEnum):
    """APB Timeout Events - mirrors apb_timeout_code_t"""
    SETUP = 0x0              # APB_TIMEOUT_SETUP
    ACCESS = 0x1             # APB_TIMEOUT_ACCESS
    ENABLE = 0x2             # APB_TIMEOUT_ENABLE
    PREADY_STUCK = 0x3       # APB_TIMEOUT_PREADY_STUCK
    TRANSFER = 0x4           # APB_TIMEOUT_TRANSFER
    RESERVED_5 = 0x5         # APB_TIMEOUT_RESERVED_5
    RESERVED_6 = 0x6         # APB_TIMEOUT_RESERVED_6
    RESERVED_7 = 0x7         # APB_TIMEOUT_RESERVED_7
    RESERVED_8 = 0x8         # APB_TIMEOUT_RESERVED_8
    RESERVED_9 = 0x9         # APB_TIMEOUT_RESERVED_9
    RESERVED_A = 0xA         # APB_TIMEOUT_RESERVED_A
    RESERVED_B = 0xB         # APB_TIMEOUT_RESERVED_B
    RESERVED_C = 0xC         # APB_TIMEOUT_RESERVED_C
    RESERVED_D = 0xD         # APB_TIMEOUT_RESERVED_D
    RESERVED_E = 0xE         # APB_TIMEOUT_RESERVED_E
    USER_DEFINED = 0xF       # APB_TIMEOUT_USER_DEFINED


class APBCompletionCode(IntEnum):
    """APB Completion Events - mirrors apb_completion_code_t"""
    TRANS_COMPLETE = 0x0     # APB_COMPL_TRANS_COMPLETE
    READ_COMPLETE = 0x1      # APB_COMPL_READ_COMPLETE
    WRITE_COMPLETE = 0x2     # APB_COMPL_WRITE_COMPLETE
    SECURE_ACCESS = 0x3      # APB_COMPL_SECURE_ACCESS
    PRIV_ACCESS = 0x4        # APB_COMPL_PRIV_ACCESS
    RESERVED_5 = 0x5         # APB_COMPL_RESERVED_5
    RESERVED_6 = 0x6         # APB_COMPL_RESERVED_6
    RESERVED_7 = 0x7         # APB_COMPL_RESERVED_7
    RESERVED_8 = 0x8         # APB_COMPL_RESERVED_8
    RESERVED_9 = 0x9         # APB_COMPL_RESERVED_9
    RESERVED_A = 0xA         # APB_COMPL_RESERVED_A
    RESERVED_B = 0xB         # APB_COMPL_RESERVED_B
    RESERVED_C = 0xC         # APB_COMPL_RESERVED_C
    RESERVED_D = 0xD         # APB_COMPL_RESERVED_D
    RESERVED_E = 0xE         # APB_COMPL_RESERVED_E
    USER_DEFINED = 0xF       # APB_COMPL_USER_DEFINED


class APBThresholdCode(IntEnum):
    """APB Threshold Events - mirrors apb_threshold_code_t"""
    LATENCY = 0x0            # APB_THRESH_LATENCY
    ERROR_RATE = 0x1         # APB_THRESH_ERROR_RATE
    ACCESS_COUNT = 0x2       # APB_THRESH_ACCESS_COUNT
    BANDWIDTH = 0x3          # APB_THRESH_BANDWIDTH
    RESERVED_4 = 0x4         # APB_THRESH_RESERVED_4
    RESERVED_5 = 0x5         # APB_THRESH_RESERVED_5
    RESERVED_6 = 0x6         # APB_THRESH_RESERVED_6
    RESERVED_7 = 0x7         # APB_THRESH_RESERVED_7
    RESERVED_8 = 0x8         # APB_THRESH_RESERVED_8
    RESERVED_9 = 0x9         # APB_THRESH_RESERVED_9
    RESERVED_A = 0xA         # APB_THRESH_RESERVED_A
    RESERVED_B = 0xB         # APB_THRESH_RESERVED_B
    RESERVED_C = 0xC         # APB_THRESH_RESERVED_C
    RESERVED_D = 0xD         # APB_THRESH_RESERVED_D
    RESERVED_E = 0xE         # APB_THRESH_RESERVED_E
    USER_DEFINED = 0xF       # APB_THRESH_USER_DEFINED


class APBPerformanceCode(IntEnum):
    """APB Performance Events - mirrors apb_performance_code_t"""
    SETUP_LATENCY = 0x0      # APB_PERF_SETUP_LATENCY
    ACCESS_LATENCY = 0x1     # APB_PERF_ACCESS_LATENCY
    ENABLE_LATENCY = 0x2     # APB_PERF_ENABLE_LATENCY
    TOTAL_LATENCY = 0x3      # APB_PERF_TOTAL_LATENCY
    THROUGHPUT = 0x4         # APB_PERF_THROUGHPUT
    ERROR_RATE = 0x5         # APB_PERF_ERROR_RATE
    ACTIVE_COUNT = 0x6       # APB_PERF_ACTIVE_COUNT
    COMPLETED_COUNT = 0x7    # APB_PERF_COMPLETED_COUNT
    BANDWIDTH_UTIL = 0x8     # APB_PERF_BANDWIDTH_UTIL
    RESERVED_9 = 0x9         # APB_PERF_RESERVED_9
    RESERVED_A = 0xA         # APB_PERF_RESERVED_A
    RESERVED_B = 0xB         # APB_PERF_RESERVED_B
    RESERVED_C = 0xC         # APB_PERF_RESERVED_C
    RESERVED_D = 0xD         # APB_PERF_RESERVED_D
    RESERVED_E = 0xE         # APB_PERF_RESERVED_E
    USER_DEFINED = 0xF       # APB_PERF_USER_DEFINED


class APBDebugCode(IntEnum):
    """APB Debug Events - mirrors apb_debug_code_t"""
    STATE_CHANGE = 0x0       # APB_DEBUG_STATE_CHANGE
    SETUP_PHASE = 0x1        # APB_DEBUG_SETUP_PHASE
    ACCESS_PHASE = 0x2       # APB_DEBUG_ACCESS_PHASE
    ENABLE_PHASE = 0x3       # APB_DEBUG_ENABLE_PHASE
    PSEL_TRACE = 0x4         # APB_DEBUG_PSEL_TRACE
    PENABLE_TRACE = 0x5      # APB_DEBUG_PENABLE_TRACE
    PREADY_TRACE = 0x6       # APB_DEBUG_PREADY_TRACE
    PPROT_TRACE = 0x7        # APB_DEBUG_PPROT_TRACE
    PSTRB_TRACE = 0x8        # APB_DEBUG_PSTRB_TRACE
    RESERVED_9 = 0x9         # APB_DEBUG_RESERVED_9
    RESERVED_A = 0xA         # APB_DEBUG_RESERVED_A
    RESERVED_B = 0xB         # APB_DEBUG_RESERVED_B
    RESERVED_C = 0xC         # APB_DEBUG_RESERVED_C
    RESERVED_D = 0xD         # APB_DEBUG_RESERVED_D
    RESERVED_E = 0xE         # APB_DEBUG_RESERVED_E
    USER_DEFINED = 0xF       # APB_DEBUG_USER_DEFINED


# =============================================================================
# NOC PROTOCOL EVENT CODES
# =============================================================================

class NOCErrorCode(IntEnum):
    """NOC Error Events - mirrors noc_error_code_t"""
    PARITY = 0x0             # NOC_ERR_PARITY
    PROTOCOL = 0x1           # NOC_ERR_PROTOCOL
    OVERFLOW = 0x2           # NOC_ERR_OVERFLOW
    UNDERFLOW = 0x3          # NOC_ERR_UNDERFLOW
    ORPHAN = 0x4             # NOC_ERR_ORPHAN
    INVALID = 0x5            # NOC_ERR_INVALID
    HEADER_CRC = 0x6         # NOC_ERR_HEADER_CRC
    PAYLOAD_CRC = 0x7        # NOC_ERR_PAYLOAD_CRC
    SEQUENCE = 0x8           # NOC_ERR_SEQUENCE
    ROUTE = 0x9              # NOC_ERR_ROUTE
    DEADLOCK = 0xA           # NOC_ERR_DEADLOCK
    RESERVED_B = 0xB         # NOC_ERR_RESERVED_B
    RESERVED_C = 0xC         # NOC_ERR_RESERVED_C
    RESERVED_D = 0xD         # NOC_ERR_RESERVED_D
    RESERVED_E = 0xE         # NOC_ERR_RESERVED_E
    USER_DEFINED = 0xF       # NOC_ERR_USER_DEFINED


# Additional NOC event codes (truncated for brevity - include all from original)
class NOCCreditCode(IntEnum):
    """NOC Credit Events - mirrors noc_credit_code_t"""
    ALLOCATED = 0x0          # NOC_CREDIT_ALLOCATED
    CONSUMED = 0x1           # NOC_CREDIT_CONSUMED
    RETURNED = 0x2           # NOC_CREDIT_RETURNED
    OVERFLOW = 0x3           # NOC_CREDIT_OVERFLOW
    UNDERFLOW = 0x4          # NOC_CREDIT_UNDERFLOW
    EXHAUSTED = 0x5          # NOC_CREDIT_EXHAUSTED
    RESTORED = 0x6           # NOC_CREDIT_RESTORED
    EFFICIENCY = 0x7         # NOC_CREDIT_EFFICIENCY
    LEAK = 0x8               # NOC_CREDIT_LEAK
    RESERVED_9 = 0x9         # NOC_CREDIT_RESERVED_9
    RESERVED_A = 0xA         # NOC_CREDIT_RESERVED_A
    RESERVED_B = 0xB         # NOC_CREDIT_RESERVED_B
    RESERVED_C = 0xC         # NOC_CREDIT_RESERVED_C
    RESERVED_D = 0xD         # NOC_CREDIT_RESERVED_D
    RESERVED_E = 0xE         # NOC_CREDIT_RESERVED_E
    USER_DEFINED = 0xF       # NOC_CREDIT_USER_DEFINED


# =============================================================================
# PROTOCOL-SPECIFIC PAYLOAD AND STATE TYPES
# =============================================================================

class TransState(IntEnum):
    """Transaction state - mirrors trans_state_t"""
    EMPTY = 0x0          # TRANS_EMPTY
    ADDR_PHASE = 0x1     # TRANS_ADDR_PHASE
    DATA_PHASE = 0x2     # TRANS_DATA_PHASE
    RESP_PHASE = 0x3     # TRANS_RESP_PHASE
    COMPLETE = 0x4       # TRANS_COMPLETE
    ERROR = 0x5          # TRANS_ERROR
    ORPHANED = 0x6       # TRANS_ORPHANED
    CREDIT_STALL = 0x7   # TRANS_CREDIT_STALL


# =============================================================================
# EVENT CODE MAPPING AND HELPER FUNCTIONS
# =============================================================================

# Event code mapping - maps (protocol, packet_type) to appropriate enum class
EVENT_CODE_MAPPING = {
    # AXI Protocol
    (ProtocolType.AXI, PktType.ERROR): AXIErrorCode,
    (ProtocolType.AXI, PktType.TIMEOUT): AXITimeoutCode,
    (ProtocolType.AXI, PktType.COMPLETION): AXICompletionCode,
    (ProtocolType.AXI, PktType.THRESHOLD): AXIThresholdCode,
    (ProtocolType.AXI, PktType.PERF): AXIPerformanceCode,
    (ProtocolType.AXI, PktType.ADDR_MATCH): AXIAddrMatchCode,
    (ProtocolType.AXI, PktType.DEBUG): AXIDebugCode,

    # APB Protocol
    (ProtocolType.APB, PktType.ERROR): APBErrorCode,
    (ProtocolType.APB, PktType.TIMEOUT): APBTimeoutCode,
    (ProtocolType.APB, PktType.COMPLETION): APBCompletionCode,
    (ProtocolType.APB, PktType.THRESHOLD): APBThresholdCode,
    (ProtocolType.APB, PktType.PERF): APBPerformanceCode,
    (ProtocolType.APB, PktType.DEBUG): APBDebugCode,

    # NOC Protocol
    (ProtocolType.NOC, PktType.ERROR): NOCErrorCode,
    (ProtocolType.NOC, PktType.CREDIT): NOCCreditCode,
    # Add other NOC mappings as needed
}


def get_event_code_enum(protocol: ProtocolType, packet_type: PktType) -> Optional[type]:
    """Get the appropriate event code enum for a protocol/packet_type combination"""
    return EVENT_CODE_MAPPING.get((protocol, packet_type))


def get_event_code_name(protocol: Union[int, ProtocolType],
                        packet_type: Union[int, PktType],
                        event_code: int) -> str:
    """
    Get human-readable event code name

    Args:
        protocol: Protocol type (int or ProtocolType)
        packet_type: Packet type (int or PktType)
        event_code: Event code value (int)

    Returns:
        Human-readable event name
    """
    try:
        # Convert to enum types if needed
        if isinstance(protocol, int):
            protocol = ProtocolType(protocol)
        if isinstance(packet_type, int):
            packet_type = PktType(packet_type)

        # Get the appropriate enum class
        enum_class = get_event_code_enum(protocol, packet_type)
        if enum_class:
            try:
                return enum_class(event_code).name
            except ValueError:
                pass

        return f"CODE_{event_code:X}"
    except (ValueError, KeyError):
        return f"UNKNOWN_{event_code:X}"


def is_valid_event_code(protocol: Union[int, ProtocolType],
                        packet_type: Union[int, PktType],
                        event_code: int) -> bool:
    """
    Validate if an event code is valid for a protocol/packet_type combination

    Args:
        protocol: Protocol type
        packet_type: Packet type
        event_code: Event code to validate

    Returns:
        True if valid, False otherwise
    """
    try:
        # Convert to enum types if needed
        if isinstance(protocol, int):
            protocol = ProtocolType(protocol)
        if isinstance(packet_type, int):
            packet_type = PktType(packet_type)

        # Get the appropriate enum class
        enum_class = get_event_code_enum(protocol, packet_type)
        if enum_class:
            try:
                enum_class(event_code)
                return True
            except ValueError:
                pass

        return False
    except (ValueError, KeyError):
        return False
