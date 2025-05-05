"""
FIFO WaveDrom Utilities - Protocol Scenarios and Checks

This module provides FIFO-specific scenarios, checks, and signal groups for WaveDrom visualization.
"""

from CocoTBFramework.components.wavedrom_utils import (
    EdgeType, ArrowStyle, SignalEvent, SignalRelation,
    WaveformContainer, ScenarioConfig, CommonGroups
)
from CocoTBFramework.components.wavedrom_utils.protocol_checks import ProtocolType

# Define FIFO-specific signal groups
FIFO_GROUPS = {
    # Write Interface
    "FIFO Write": [
        "i_write", "o_wr_full", "o_wr_almost_full", "o_wr_count",
        "i_wr_data"
    ],
    # Read Interface
    "FIFO Read": [
        "i_read", "o_rd_empty", "o_rd_almost_empty", "o_rd_count",
        "o_rd_data", "ow_rd_data"
    ],
    # Control Signals
    "Control": [
        "clk", "rst_n"
    ],
    # Internal State
    "Internal State": [
        "r_write_ptr", "r_read_ptr", "r_count"
    ]
}

# Define FIFO operation modes
FIFO_MODES = {
    "flop": {
        "description": "Registered read data (flop mode)",
        "data_signal": "o_rd_data",
        "data_delay": 1  # Data appears 1 cycle after read
    },
    "mux": {
        "description": "Combinational read data (mux mode)",
        "data_signal": "ow_rd_data",
        "data_delay": 0  # Data appears same cycle as read
    }
}

# Debug check functions for FIFO protocol

async def check_fifo_overflow(dut, wave_gen):
    """Check for FIFO overflow condition"""
    # Check for write when full
    if hasattr(dut, 'i_write') and hasattr(dut, 'o_wr_full'):
        if dut.i_write.value == 1 and dut.o_wr_full.value == 1:
            wave_gen.add_debug_point(
                wave_gen.current_cycle,
                "FIFO Protocol Violation: Write while full (overflow)",
                {'write': 1, 'full': 1}
            )
            return True
    return False

async def check_fifo_underflow(dut, wave_gen):
    """Check for FIFO underflow condition"""
    # Check for read when empty
    if hasattr(dut, 'i_read') and hasattr(dut, 'o_rd_empty'):
        if dut.i_read.value == 1 and dut.o_rd_empty.value == 1:
            wave_gen.add_debug_point(
                wave_gen.current_cycle,
                "FIFO Protocol Violation: Read while empty (underflow)",
                {'read': 1, 'empty': 1}
            )
            return True
    return False

async def check_fifo_fullness_warning(dut, wave_gen):
    """Check for FIFO approaching full condition"""
    if hasattr(dut, 'o_wr_count'):
        count = dut.o_wr_count.value
        # Get FIFO depth if available
        fifo_depth = getattr(dut, 'FIFO_DEPTH', 16)  # Default to 16 if not defined
        
        # Warning threshold (80% full)
        threshold = int(fifo_depth * 0.8)
        
        if count >= threshold:
            wave_gen.add_debug_point(
                wave_gen.current_cycle,
                f"FIFO Fullness Warning: {count}/{fifo_depth} entries used ({count/fifo_depth*100:.1f}%)",
                {'count': count, 'depth': fifo_depth, 'percentage': count/fifo_depth}
            )
            return True
    return False

async def check_fifo_emptiness_warning(dut, wave_gen):
    """Check for FIFO approaching empty condition"""
    if hasattr(dut, 'o_rd_count') and hasattr(dut, 'i_read'):
        count = dut.o_rd_count.value
        
        # Only warn if reads are happening
        if dut.i_read.value == 1 and count <= 2:
            wave_gen.add_debug_point(
                wave_gen.current_cycle,
                f"FIFO Emptiness Warning: Only {count} entries left",
                {'count': count, 'read': 1}
            )
            return True
    return False

async def check_fifo_simultaneous_read_write(dut, wave_gen):
    """Check for simultaneous read and write behavior"""
    if hasattr(dut, 'i_read') and hasattr(dut, 'i_write'):
        if dut.i_read.value == 1 and dut.i_write.value == 1:
            # Check if FIFO count is stable (should be if read and write happen simultaneously)
            if hasattr(dut, 'r_count'):
                prev_count = wave_gen.get_last_value("r_count")
                curr_count = dut.r_count.value
                
                if prev_count is not None and curr_count != prev_count:
                    # Count changed despite simultaneous read/write - this may be an implementation detail
                    # but worth noting for verification
                    wave_gen.add_debug_point(
                        wave_gen.current_cycle,
                        "FIFO Note: Count changed during simultaneous read/write",
                        {'read': 1, 'write': 1, 'prev_count': prev_count, 'curr_count': curr_count}
                    )
                    return True
    return False

async def check_fifo_data_stability(dut, wave_gen, mode="flop"):
    """Check for data stability during read operations"""
    # Get configuration for FIFO mode
    mode_config = FIFO_MODES.get(mode, FIFO_MODES["flop"])
    data_signal = mode_config["data_signal"]
    data_delay = mode_config["data_delay"]
    
    if not hasattr(dut, data_signal) or not hasattr(dut, 'i_read'):
        return False
        
    # For flop mode, check data stability one cycle after read
    if mode == "flop" and data_delay == 1:
        # Check if a read happened in the previous cycle
        read_previous_cycle = wave_gen.cycles_since_event(
            SignalEvent("i_read", EdgeType.RISING)
        ) == 1
        
        if read_previous_cycle:
            # Data should be stable now for registered read data
            current_data = getattr(dut, data_signal).value
            prev_data_events = [(c, v) for c, s, v, e in wave_gen.event_history 
                              if s == data_signal and c < wave_gen.current_cycle]
            
            if prev_data_events and current_data != prev_data_events[-1][1]:
                # Data changed as expected after read
                return False
    
    # For mux mode, check data stability same cycle as read
    elif mode == "mux" and data_delay == 0:
        if dut.i_read.value == 1:
            # Data should be presented combinationally
            # This is harder to verify as data should change immediately
            # Just note that a read is happening
            wave_gen.add_debug_point(
                wave_gen.current_cycle,
                "FIFO Mux-Mode Read: Combinational data should be valid now",
                {'read': 1}
            )
            return True
    
    return False

# Predefined FIFO scenarios

fifo_write_scenario = ScenarioConfig(
    name="FIFO Write Operations",
    description="Verify FIFO write interface behavior",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # Write causing count to increase
        SignalRelation(
            cause=SignalEvent("i_write", EdgeType.RISING),
            effect=SignalEvent("r_count", EdgeType.ANY_CHANGE),
            min_cycles=0,
            max_cycles=1,
            style=ArrowStyle.BLOCKING
        ),
        # Write affecting full status (when approaching capacity)
        SignalRelation(
            cause=SignalEvent("i_write", EdgeType.RISING),
            effect=SignalEvent("o_wr_almost_full", EdgeType.RISING),
            min_cycles=0,
            max_cycles=None,
            style=ArrowStyle.SPLINE
        ),
        # Full status blocking writes
        SignalRelation(
            cause=SignalEvent("o_wr_full", EdgeType.RISING),
            effect=SignalEvent("i_write", EdgeType.FALLING),
            min_cycles=0,
            max_cycles=None,
            style=ArrowStyle.WEAK
        )
    ],
    debug_checks=[
        {
            'function': check_fifo_overflow,
            'description': "Check overflow condition"
        },
        {
            'function': check_fifo_fullness_warning,
            'description': "Check fullness warning"
        }
    ]
)

fifo_read_flop_scenario = ScenarioConfig(
    name="FIFO Read Operations (Flop Mode)",
    description="Verify FIFO read interface behavior with registered data",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # Read causing count to decrease
        SignalRelation(
            cause=SignalEvent("i_read", EdgeType.RISING),
            effect=SignalEvent("r_count", EdgeType.ANY_CHANGE),
            min_cycles=0,
            max_cycles=1,
            style=ArrowStyle.BLOCKING
        ),
        # Read triggering data output after 1 cycle (registered)
        SignalRelation(
            cause=SignalEvent("i_read", EdgeType.RISING),
            effect=SignalEvent("o_rd_data", EdgeType.ANY_CHANGE),
            min_cycles=1,
            max_cycles=1,
            style=ArrowStyle.NONBLOCKING
        ),
        # Empty status blocking reads
        SignalRelation(
            cause=SignalEvent("o_rd_empty", EdgeType.RISING),
            effect=SignalEvent("i_read", EdgeType.FALLING),
            min_cycles=0,
            max_cycles=None,
            style=ArrowStyle.WEAK
        )
    ],
    debug_checks=[
        {
            'function': check_fifo_underflow,
            'description': "Check underflow condition"
        },
        {
            'function': check_fifo_emptiness_warning,
            'description': "Check emptiness warning"
        },
        {
            'function': lambda dut, wave_gen: check_fifo_data_stability(dut, wave_gen, "flop"),
            'description': "Check data stability (flop mode)"
        }
    ]
)

fifo_read_mux_scenario = ScenarioConfig(
    name="FIFO Read Operations (Mux Mode)",
    description="Verify FIFO read interface behavior with combinational data",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # Read causing count to decrease
        SignalRelation(
            cause=SignalEvent("i_read", EdgeType.RISING),
            effect=SignalEvent("r_count", EdgeType.ANY_CHANGE),
            min_cycles=0,
            max_cycles=1,
            style=ArrowStyle.BLOCKING
        ),
        # Read immediately presenting data (combinational)
        SignalRelation(
            cause=SignalEvent("i_read", EdgeType.RISING),
            effect=SignalEvent("ow_rd_data", EdgeType.ANY_CHANGE),
            min_cycles=0,
            max_cycles=0,
            style=ArrowStyle.STRAIGHT
        ),
        # Empty status blocking reads
        SignalRelation(
            cause=SignalEvent("o_rd_empty", EdgeType.RISING),
            effect=SignalEvent("i_read", EdgeType.FALLING),
            min_cycles=0,
            max_cycles=None,
            style=ArrowStyle.WEAK