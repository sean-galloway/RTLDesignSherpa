"""
GAXI WaveDrom Utilities - Protocol Scenarios and Checks

This module provides GAXI (Generic AXI)-specific scenarios, checks, and signal groups 
for WaveDrom visualization.
"""

from CocoTBFramework.components.wavedrom_utils import (
    EdgeType, ArrowStyle, SignalEvent, SignalRelation,
    WaveformContainer, ScenarioConfig, CommonGroups
)
from CocoTBFramework.components.wavedrom_utils.protocol_checks import ProtocolType

# Define GAXI-specific signal groups
GAXI_GROUPS = {
    # Standard Mode (Single Bus)
    "GAXI Standard": [
        "m2s_valid", "s2m_ready", "m2s_pkt"
    ],
    # Multi-Signal Mode (Multiple Signals)
    "GAXI Multi": [
        "m2s_valid", "s2m_ready", "m2s_pkt_addr", "m2s_pkt_data", 
        "m2s_pkt_cmd", "m2s_pkt_strb"
    ],
    # Control Signals
    "Control": [
        "clk", "rst_n"
    ],
    # Buffer State
    "Buffer State": [
        "r_buffer_full", "r_buffer_empty", "r_buffer_count"
    ]
}

# Define GAXI operation modes
GAXI_MODES = {
    "skid": {
        "description": "Standard skid buffer mode",
        "transfer_delay": 0  # Data transfers in same cycle when valid and ready are both high
    },
    "fifo_mux": {
        "description": "FIFO multiplexer mode with combinational output",
        "transfer_delay": 0  # Data appears in same cycle
    },
    "fifo_flop": {
        "description": "FIFO flip-flop mode with registered output",
        "transfer_delay": 1  # Data appears one cycle later
    }
}

# Debug check functions for GAXI protocol

async def check_gaxi_handshake_stall(dut, wave_gen):
    """Check for stalled valid without ready handshake"""
    # Only check if required signals exist
    if not all(hasattr(dut, s) for s in ['m2s_valid', 's2m_ready']):
        return False
        
    # Check for valid without ready
    if dut.m2s_valid.value == 1 and dut.s2m_ready.value == 0:
        # Check how long valid has been asserted
        stall_cycles = wave_gen.cycles_since_event(
            SignalEvent("m2s_valid", EdgeType.RISING)
        )
        
        if stall_cycles > 10:  # Stalled for too long
            wave_gen.add_debug_point(
                wave_gen.current_cycle,
                f"GAXI Handshake Stall: valid asserted without ready for {stall_cycles} cycles",
                {'m2s_valid': 1, 's2m_ready': 0, 'cycles': stall_cycles}
            )
            return True
    return False

async def check_gaxi_ready_without_valid(dut, wave_gen):
    """Check for ready without valid (potential inefficiency)"""
    # Only check if required signals exist
    if not all(hasattr(dut, s) for s in ['m2s_valid', 's2m_ready']):
        return False
        
    # Check for ready without valid for extended periods
    if dut.s2m_ready.value == 1 and dut.m2s_valid.value == 0:
        # Check how long ready has been asserted
        ready_cycles = wave_gen.cycles_since_event(
            SignalEvent("s2m_ready", EdgeType.RISING)
        )
        
        if ready_cycles > 20:  # Ready asserted for too long without valid
            wave_gen.add_debug_point(
                wave_gen.current_cycle,
                f"GAXI Efficiency Note: ready asserted without valid for {ready_cycles} cycles",
                {'s2m_ready': 1, 'm2s_valid': 0, 'cycles': ready_cycles}
            )
            return True
    return False

async def check_gaxi_buffer_fullness(dut, wave_gen):
    """Check buffer fullness conditions"""
    # Check if buffer state signals are available
    if not any(hasattr(dut, s) for s in ['r_buffer_full', 'r_buffer_count']):
        return False
        
    # Check specific buffer count if available
    if hasattr(dut, 'r_buffer_count'):
        count = dut.r_buffer_count.value
        # Get buffer capacity
        buffer_capacity = getattr(dut, 'BUFFER_DEPTH', 4)  # Default to 4 if not defined
        
        # Warning threshold (75% full)
        threshold = int(buffer_capacity * 0.75)
        
        if count >= threshold:
            wave_gen.add_debug_point(
                wave_gen.current_cycle,
                f"GAXI Buffer Fullness: {count}/{buffer_capacity} entries used ({count/buffer_capacity*100:.1f}%)",
                {'count': count, 'capacity': buffer_capacity, 'percentage': count/buffer_capacity}
            )
            return True
    # Use the buffer full signal if count not available
    elif hasattr(dut, 'r_buffer_full') and dut.r_buffer_full.value == 1:
        wave_gen.add_debug_point(
            wave_gen.current_cycle,
            "GAXI Buffer Full: May cause backpressure",
            {'r_buffer_full': 1}
        )
        return True
        
    return False

async def check_gaxi_data_transfer(dut, wave_gen, mode="skid"):
    """Check proper data transfer according to GAXI mode"""
    # Get configuration for GAXI mode
    mode_config = GAXI_MODES.get(mode, GAXI_MODES["skid"])
    transfer_delay = mode_config["transfer_delay"]
    
    # Check if required signals exist - prefer multi-signal mode if available
    has_single_pkt = hasattr(dut, 'm2s_pkt')
    has_multi_pkt = any(hasattr(dut, f'm2s_pkt_{field}') for field in ['addr', 'data', 'cmd'])
    
    if not (has_single_pkt or has_multi_pkt) or not all(hasattr(dut, s) for s in ['m2s_valid', 's2m_ready']):
        return False
        
    # Check for valid & ready handshake
    if dut.m2s_valid.value == 1 and dut.s2m_ready.value == 1:
        # A transfer is happening this cycle
        
        # For skid buffer and fifo_mux modes, data transfer happens immediately
        if mode in ["skid", "fifo_mux"] and transfer_delay == 0:
            wave_gen.add_debug_point(
                wave_gen.current_cycle,
                "GAXI Transfer: Data transferred this cycle",
                {'m2s_valid': 1, 's2m_ready': 1, 'mode': mode}
            )
            return True
            
    # For fifo_flop mode, check if a transfer happened in the previous cycle
    elif mode == "fifo_flop" and transfer_delay == 1:
        # Check if a handshake happened in the previous cycle
        valid_ready_prev_cycle = False
        
        # Scan event history for valid & ready in previous cycle
        for cycle, sig, val, edge in reversed(wave_gen.event_history):
            if cycle == wave_gen.current_cycle - 1:
                if sig == "m2s_valid" and val == 1:
                    # Valid was high in previous cycle
                    for c2, s2, v2, e2 in reversed(wave_gen.event_history):
                        if c2 == wave_gen.current_cycle - 1 and s2 == "s2m_ready" and v2 == 1:
                            # Ready was also high in previous cycle
                            valid_ready_prev_cycle = True
                            break
                    break
        
        if valid_ready_prev_cycle:
            # Data should be transferred this cycle for fifo_flop mode
            wave_gen.add_debug_point(
                wave_gen.current_cycle,
                "GAXI Transfer: Data transferred this cycle (from previous handshake)",
                {'mode': 'fifo_flop'}
            )
            return True
            
    return False

async def check_gaxi_backpressure(dut, wave_gen):
    """Check for backpressure effects (ready deasserted after valid)"""
    # Only check if required signals exist
    if not all(hasattr(dut, s) for s in ['m2s_valid', 's2m_ready']):
        return False
        
    # Check if ready was deasserted after valid
    if dut.m2s_valid.value == 1 and dut.s2m_ready.value == 0:
        # Check if ready was previously high
        ready_falling = wave_gen.cycles_since_event(
            SignalEvent("s2m_ready", EdgeType.FALLING)
        ) == 1
        
        if ready_falling:
            wave_gen.add_debug_point(
                wave_gen.current_cycle,
                "GAXI Backpressure: Ready deasserted while Valid still high",
                {'m2s_valid': 1, 's2m_ready': 0, 'backpressure': True}
            )
            return True
    
    return False

# Predefined GAXI scenarios

gaxi_handshake_scenario = ScenarioConfig(
    name="GAXI Handshake Protocol",
    description="Verify GAXI handshaking behavior",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # Valid leading to ready assertion
        SignalRelation(
            cause=SignalEvent("m2s_valid", EdgeType.RISING),
            effect=SignalEvent("s2m_ready", EdgeType.RISING),
            min_cycles=0,
            max_cycles=None,  # No defined upper limit
            style=ArrowStyle.SPLINE
        ),
        # Valid cleared after handshake
        SignalRelation(
            cause=SignalEvent("s2m_ready", EdgeType.RISING),
            effect=SignalEvent("m2s_valid", EdgeType.FALLING),
            min_cycles=0,
            max_cycles=None,
            style=ArrowStyle.SPLINE
        )
    ],
    debug_checks=[
        {
            'function': check_gaxi_handshake_stall,
            'description': "Check handshake stalls"
        },
        {
            'function': check_gaxi_ready_without_valid,
            'description': "Check ready without valid"
        }
    ]
)

gaxi_skid_buffer_scenario = ScenarioConfig(
    name="GAXI Skid Buffer Mode",
    description="Verify GAXI skid buffer mode operation",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # Valid & ready causing data transfer
        SignalRelation(
            cause=SignalEvent("m2s_valid", EdgeType.RISING),
            effect=SignalEvent("s2m_ready", EdgeType.RISING),
            min_cycles=0,
            max_cycles=None,
            style=ArrowStyle.SPLINE
        ),
        # Buffer fullness affecting ready
        SignalRelation(
            cause=SignalEvent("r_buffer_full", EdgeType.RISING),
            effect=SignalEvent("s2m_ready", EdgeType.FALLING),
            min_cycles=0,
            max_cycles=1,
            style=ArrowStyle.BLOCKING
        )
    ],
    debug_checks=[
        {
            'function': check_gaxi_buffer_fullness,
            'description': "Check buffer fullness"
        },
        {
            'function': lambda dut, wave_gen: check_gaxi_data_transfer(dut, wave_gen, "skid"),
            'description': "Check data transfer (skid mode)"
        }
    ]
)

gaxi_fifo_mux_scenario = ScenarioConfig(
    name="GAXI FIFO Mux Mode",
    description="Verify GAXI FIFO mux mode operation",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # Valid & ready causing data transfer
        SignalRelation(
            cause=SignalEvent("m2s_valid", EdgeType.RISING),
            effect=SignalEvent("s2m_ready", EdgeType.RISING),
            min_cycles=0,
            max_cycles=None,
            style=ArrowStyle.SPLINE
        ),
        # Data changes immediately when valid & ready
        SignalRelation(
            cause=SignalEvent("s2m_ready", EdgeType.RISING),
            effect=SignalEvent("m2s_pkt", EdgeType.ANY_CHANGE),
            min_cycles=0,
            max_cycles=0,
            style=ArrowStyle.STRAIGHT
        )
    ],
    debug_checks=[
        {
            'function': lambda dut, wave_gen: check_gaxi_data_transfer(dut, wave_gen, "fifo_mux"),
            'description': "Check data transfer (fifo_mux mode)"
        },
        {
            'function': check_gaxi_backpressure,
            'description': "Check backpressure effects"
        }
    ]
)

gaxi_fifo_flop_scenario = ScenarioConfig(
    name="GAXI FIFO Flop Mode",
    description="Verify GAXI FIFO flop mode operation",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # Valid & ready causing data transfer in next cycle
        SignalRelation(
            cause=SignalEvent("m2s_valid", EdgeType.RISING),
            effect=SignalEvent("s2m_ready", EdgeType.RISING),
            min_cycles=0,
            max_cycles=None,
            style=ArrowStyle.SPLINE
        ),
        # Data changes one cycle after valid & ready
        SignalRelation(
            cause=SignalEvent("s2m_ready", EdgeType.RISING),
            effect=SignalEvent("m2s_pkt", EdgeType.ANY_CHANGE),
            min_cycles=1,
            max_cycles=1,
            style=ArrowStyle.NONBLOCKING
        )
    ],
    debug_checks=[
        {
            'function': lambda dut, wave_gen: check_gaxi_data_transfer(dut, wave_gen, "fifo_flop"),
            'description': "Check data transfer (fifo_flop mode)"
        },
        {
            'function': check_gaxi_backpressure,
            'description': "Check backpressure effects"
        }
    ]
)

gaxi_buffer_scenario = ScenarioConfig(
    name="GAXI Buffer States",
    description="Verify GAXI buffer state transitions",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # Handshakes affecting buffer count
        SignalRelation(
            cause=SignalEvent("m2s_valid", EdgeType.RISING),
            effect=SignalEvent("r_buffer_count", EdgeType.ANY_CHANGE),
            min_cycles=0,
            max_cycles=1,
            style=ArrowStyle.BLOCKING
        ),
        # Buffer full affecting ready
        SignalRelation(
            cause=SignalEvent("r_buffer_full", EdgeType.RISING),
            effect=SignalEvent("s2m_ready", EdgeType.FALLING),
            min_cycles=0,
            max_cycles=1,
            style=ArrowStyle.BLOCKING
        )
    ],
    debug_checks=[
        {
            'function': check_gaxi_buffer_fullness,
            'description': "Check buffer fullness"
        }
    ]
)

def get_signal_groups(dut):
    """
    Return signal groups appropriate for the DUT
    
    Args:
        dut: Device under test
        
    Returns:
        Dictionary of signal groups
    """
    groups = {}
    
    # Check if main handshake signals exist
    has_handshake = all(hasattr(dut, s) for s in ['m2s_valid', 's2m_ready'])
    
    if not has_handshake:
        # No GAXI signals found
        return GAXI_GROUPS
    
    # Check for single-signal mode
    if hasattr(dut, 'm2s_pkt'):
        groups["GAXI Standard"] = ["m2s_valid", "s2m_ready", "m2s_pkt"]
    
    # Check for multi-signal mode
    multi_signals = []
    for field in ['addr', 'data', 'cmd', 'strb', 'id', 'user']:
        signal = f'm2s_pkt_{field}'
        if hasattr(dut, signal):
            multi_signals.append(signal)
    
    if multi_signals:
        groups["GAXI Multi"] = ["m2s_valid", "s2m_ready"] + multi_signals
    
    # Control signals
    control_signals = []
    for signal in ["clk", "rst_n"]:
        if hasattr(dut, signal):
            control_signals.append(signal)
    
    if control_signals:
        groups["Control"] = control_signals
    
    # Buffer state signals
    buffer_signals = []
    for signal in ["r_buffer_full", "r_buffer_empty", "r_buffer_count"]:
        if hasattr(dut, signal):
            buffer_signals.append(signal)
    
    if buffer_signals:
        groups["Buffer State"] = buffer_signals
    
    return groups

def create_gaxi_scenarios(dut, mode="skid", include_scenarios=None):
    """
    Create GAXI scenarios based on available signals in the DUT
    and the specified operating mode
    
    Args:
        dut: Device under test
        mode: GAXI mode ("skid", "fifo_mux", or "fifo_flop")
        include_scenarios: Optional list of scenario names to include
                          (None = all applicable)
    
    Returns:
        List of applicable scenarios
    """
    # Check which signals are available
    has_handshake = all(hasattr(dut, s) for s in ['m2s_valid', 's2m_ready'])
    has_buffer_state = any(hasattr(dut, s) for s in ['r_buffer_full', 'r_buffer_count'])
    
    if not has_handshake:
        # No GAXI signals found
        return []
    
    # Build list of applicable scenarios
    scenarios = []
    
    # Handshake scenario is always applicable
    if include_scenarios is None or 'handshake' in include_scenarios:
        scenarios.append(gaxi_handshake_scenario)
    
    # Add mode-specific scenario
    if mode == "skid" and (include_scenarios is None or 'skid' in include_scenarios):
        scenarios.append(gaxi_skid_buffer_scenario)
    elif mode == "fifo_mux" and (include_scenarios is None or 'fifo_mux' in include_scenarios):
        scenarios.append(gaxi_fifo_mux_scenario)
    elif mode == "fifo_flop" and (include_scenarios is None or 'fifo_flop' in include_scenarios):
        scenarios.append(gaxi_fifo_flop_scenario)
    
    # Buffer scenario requires buffer state signals
    if has_buffer_state and (include_scenarios is None or 'buffer' in include_scenarios):
        scenarios.append(gaxi_buffer_scenario)
    
    return scenarios
