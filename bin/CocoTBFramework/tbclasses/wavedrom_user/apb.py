"""
APB WaveDrom Utilities - Protocol Scenarios and Checks

This module provides APB-specific scenarios, checks, and signal groups for WaveDrom visualization.
"""

from CocoTBFramework.components.wavedrom_utils import (
    EdgeType, ArrowStyle, SignalEvent, SignalRelation,
    WaveformContainer, ScenarioConfig, CommonGroups
)
from CocoTBFramework.components.wavedrom_utils.protocol_checks import ProtocolType

# Define APB-specific signal groups
APB_GROUPS = {
    "APB Interface": ["s_apb_PSEL", "s_apb_PENABLE", "s_apb_PREADY", "s_apb_PWRITE", 
                      "s_apb_PWDATA", "s_apb_PRDATA", "s_apb_PSLVERR"],
    "Control": ["pclk", "presetn", "cg_pclk", "o_apb_clock_gating", "r_wakeup"],
    "Command Channel": ["o_cmd_valid", "i_cmd_ready", "o_cmd_pwrite", "o_cmd_pwdata"],
    "Response Channel": ["i_rsp_valid", "o_rsp_ready", "i_rsp_prdata", "i_rsp_pslverr"],
    "State Machine": ["r_apb_state"]
}

# Define valid APB FSM state transitions
APB_STATE_TRANSITIONS = {
    1: [2],     # IDLE(1) -> BUSY(2)
    2: [4],     # BUSY(2) -> WAIT(4) 
    4: [1]      # WAIT(4) -> IDLE(1)
}

# Define APB state values
APB_STATES = {
    1: "IDLE",
    2: "BUSY",
    4: "WAIT"
}

# Debug check functions for APB protocol

async def check_apb_pready_timing(dut, wave_gen):
    """Check if PREADY is properly asserted after cmd_valid and rsp_valid"""
    # We're in a BUSY state but PREADY hasn't been asserted for too long
    if hasattr(dut, 'r_apb_state') and dut.r_apb_state.value.integer == 2:  # BUSY state
        busy_cycles = wave_gen.cycles_since_event(
            SignalEvent("r_apb_state", EdgeType.ANY_CHANGE, 2)  # BUSY is 2
        )
        if busy_cycles > 10:
            wave_gen.add_debug_point(
                wave_gen.current_cycle,
                "APB stuck in BUSY state without response for 10+ cycles",
                {'state': "BUSY", 'cycles': busy_cycles}
            )
            return True
    return False

async def check_command_response_handshake(dut, wave_gen):
    """Check for improper command-response handshake"""
    if hasattr(dut, 'o_cmd_valid') and hasattr(dut, 'i_cmd_ready'):
        if dut.o_cmd_valid.value == 1 and dut.i_cmd_ready.value == 0:
            stall_cycles = wave_gen.cycles_since_event(
                SignalEvent("o_cmd_valid", EdgeType.RISING)
            )
            if stall_cycles > 5:
                wave_gen.add_debug_point(
                    wave_gen.current_cycle,
                    "Command stalled - valid without ready for 5+ cycles",
                    {'o_cmd_valid': 1, 'i_cmd_ready': 0, 'cycles': stall_cycles}
                )
                return True
    return False

async def check_clock_gating_behavior(dut, wave_gen):
    """Check for proper clock gating behavior"""
    
    # Only check if clock gating is enabled and relevant signals exist
    if not all(hasattr(dut, attr) for attr in ['i_cfg_cg_enable', 'r_apb_state', 'o_apb_clock_gating']):
        return False
        
    if dut.i_cfg_cg_enable.value == 0:
        return False
    
    # Check if in IDLE state with no activity but clock not gated
    if (dut.r_apb_state.value.integer == 1 and  # IDLE state
        dut.s_apb_PSEL.value == 0 and
        dut.o_cmd_valid.value == 0 and
        dut.i_rsp_valid.value == 0):
        
        # If we've been idle for longer than idle_count, clock should be gated
        idle_cycles = wave_gen.cycles_since_event(
            SignalEvent("r_apb_state", EdgeType.ANY_CHANGE, 1)  # IDLE is 1
        )
        
        if hasattr(dut, 'i_cfg_cg_idle_count'):
            idle_count = dut.i_cfg_cg_idle_count.value
            
            # Clock should be gated after idle_count + 2 (allowing for implementation delay)
            if idle_cycles > idle_count + 2:
                # Clock should be gated by now
                if dut.o_apb_clock_gating.value == 0:
                    wave_gen.add_debug_point(
                        wave_gen.current_cycle,
                        f"Clock Gating Issue: Not gated after {idle_cycles} idle cycles (limit: {idle_count})",
                        {'idle_cycles': idle_cycles, 'idle_limit': idle_count}
                    )
                    return True
    
    # Check for incorrect gating during active states
    if hasattr(dut, 'o_apb_clock_gating') and dut.o_apb_clock_gating.value == 1:
        if (hasattr(dut, 'r_apb_state') and dut.r_apb_state.value.integer != 1 or  # Not in IDLE state
            dut.s_apb_PSEL.value == 1 or
            dut.o_cmd_valid.value == 1 or
            dut.i_rsp_valid.value == 1):
            
            wave_gen.add_debug_point(
                wave_gen.current_cycle,
                "Clock Gating Issue: Clock gated during active operation",
                {'state': dut.r_apb_state.value.integer if hasattr(dut, 'r_apb_state') else "N/A", 
                 'psel': dut.s_apb_PSEL.value,
                 'cmd_valid': dut.o_cmd_valid.value,
                 'rsp_valid': dut.i_rsp_valid.value}
            )
            return True
    
    return False

async def check_apb_protocol_violations(dut, wave_gen):
    """Comprehensive check for APB protocol violations"""
    
    # 1. Check for PENABLE without PSEL
    if dut.s_apb_PENABLE.value == 1 and dut.s_apb_PSEL.value == 0:
        wave_gen.add_debug_point(
            wave_gen.current_cycle,
            "APB Protocol Violation: PENABLE asserted without PSEL",
            {'PENABLE': 1, 'PSEL': 0}
        )
        return True
        
    # 2. Check PSEL->PENABLE timing (must happen on next cycle)
    if dut.s_apb_PSEL.value == 1 and dut.s_apb_PENABLE.value == 0:
        # Get time since PSEL assertion
        psel_cycles = wave_gen.cycles_since_event(
            SignalEvent("s_apb_PSEL", EdgeType.RISING)
        )
        if psel_cycles > 1:
            wave_gen.add_debug_point(
                wave_gen.current_cycle,
                f"APB Protocol Violation: PENABLE not asserted cycle after PSEL ({psel_cycles} cycles)",
                {'PSEL': 1, 'PENABLE': 0, 'cycles': psel_cycles}
            )
            return True
    
    # 3. Check PREADY responsiveness
    if (dut.s_apb_PSEL.value == 1 and 
        dut.s_apb_PENABLE.value == 1 and 
        hasattr(dut, 'r_apb_state') and
        dut.r_apb_state.value.integer == 2):  # BUSY
        
        busy_cycles = wave_gen.cycles_since_event(
            SignalEvent("r_apb_state", EdgeType.ANY_CHANGE, 2)  # BUSY is 2
        )
        if busy_cycles > 20:  # Excessive time in BUSY state
            wave_gen.add_debug_point(
                wave_gen.current_cycle,
                f"APB Responsiveness Issue: No PREADY after {busy_cycles} cycles in BUSY state",
                {'state': "BUSY", 'cycles': busy_cycles, 'cmd_valid': dut.o_cmd_valid.value}
            )
            return True
    
    # 4. Check for multiple PSEL/PENABLE during active transfer
    if (dut.s_apb_PREADY.value == 0 and 
        hasattr(dut, 'r_apb_state') and 
        dut.r_apb_state.value.integer == 2):  # BUSY
        
        # Look for PSEL/PENABLE changes
        psel_toggle = wave_gen.cycles_since_event(
            SignalEvent("s_apb_PSEL", EdgeType.ANY_CHANGE)
        )
        if hasattr(dut, 'busy_cycles') and psel_toggle < dut.busy_cycles:
            wave_gen.add_debug_point(
                wave_gen.current_cycle,
                "APB Protocol Violation: PSEL changed during active transfer",
                {'state': "BUSY", 'PSEL_changed': True}
            )
            return True
    
    return False

async def check_fsm_transitions(dut, wave_gen):
    """Monitor FSM state transitions for correctness"""
    
    # Only check if state signal exists
    if not hasattr(dut, 'r_apb_state'):
        return False
        
    # 1. Check for invalid state transitions
    current_state = dut.r_apb_state.value.integer
    
    # Get previous state if available
    prev_state_event = wave_gen.cycles_since_event(
        SignalEvent("r_apb_state", EdgeType.ANY_CHANGE)
    )
    
    if prev_state_event == 1:  # Just had a transition last cycle
        # Get value before most recent change
        prev_events = [(c, v) for c, s, v, e in wave_gen.event_history 
                      if s == "r_apb_state" and c < wave_gen.current_cycle]
        
        if prev_events:
            prev_state = max(prev_events, key=lambda x: x[0])[1]
            
            # Check valid transitions
            # IDLE(1) -> BUSY(2) -> WAIT(4) -> IDLE(1)
            if current_state not in APB_STATE_TRANSITIONS.get(prev_state, []):
                # Get state names for better debug messages
                prev_state_name = APB_STATES.get(prev_state, str(prev_state))
                current_state_name = APB_STATES.get(current_state, str(current_state))
                
                wave_gen.add_debug_point(
                    wave_gen.current_cycle,
                    f"Invalid FSM transition: {prev_state_name}({prev_state}) -> {current_state_name}({current_state})",
                    {'prev_state': prev_state, 'current_state': current_state}
                )
                return True
    
    return False

async def check_fifo_overrun(dut, wave_gen):
    """Check for potential FIFO overruns in command or response paths"""
    
    # Check command FIFO count approaching limit if signal exists
    if hasattr(dut, 'r_cmd_count'):
        cmd_count = dut.r_cmd_count.value
        if cmd_count >= 3:  # Nearing FIFO depth of SKID_DEPTH
            wave_gen.add_debug_point(
                wave_gen.current_cycle,
                f"Command FIFO nearing capacity: {cmd_count}/4 entries used",
                {'cmd_count': cmd_count, 
                 'cmd_valid': dut.o_cmd_valid.value if hasattr(dut, 'o_cmd_valid') else 'N/A', 
                 'cmd_ready': dut.i_cmd_ready.value if hasattr(dut, 'i_cmd_ready') else 'N/A'}
            )
            return True
        
    # Check response FIFO count approaching limit if signal exists
    if hasattr(dut, 'r_rsp_count'):
        rsp_count = dut.r_rsp_count.value
        if rsp_count >= 3:  # Nearing FIFO depth of SKID_DEPTH
            wave_gen.add_debug_point(
                wave_gen.current_cycle,
                f"Response FIFO nearing capacity: {rsp_count}/4 entries used",
                {'rsp_count': rsp_count, 
                 'rsp_valid': dut.i_rsp_valid.value if hasattr(dut, 'i_rsp_valid') else 'N/A', 
                 'rsp_ready': dut.o_rsp_ready.value if hasattr(dut, 'o_rsp_ready') else 'N/A'}
            )
            return True
    
    return False

# Predefined APB scenarios

apb_setup_scenario = ScenarioConfig(
    name="APB Transaction Setup",
    description="Verify APB setup phase timing",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # PSEL & PENABLE activates command valid
        SignalRelation(
            cause=SignalEvent("s_apb_PSEL", EdgeType.RISING),
            effect=SignalEvent("s_apb_PENABLE", EdgeType.RISING),
            min_cycles=1,
            max_cycles=1,
            style=ArrowStyle.STRAIGHT
        ),
        # PSEL & PENABLE leads to command valid
        SignalRelation(
            cause=SignalEvent("s_apb_PENABLE", EdgeType.RISING),
            effect=SignalEvent("o_cmd_valid", EdgeType.RISING),
            min_cycles=1,
            max_cycles=1,
            style=ArrowStyle.STRAIGHT
        ),
        # Command valid leads to state transition to BUSY
        SignalRelation(
            cause=SignalEvent("o_cmd_valid", EdgeType.RISING),
            effect=SignalEvent.state_change("r_apb_state", "IDLE", "BUSY"),
            min_cycles=0,
            max_cycles=1,
            style=ArrowStyle.BLOCKING
        )
    ],
    debug_checks=[{
        'function': check_command_response_handshake,
        'description': "Check command handshake"
    }]
)

apb_response_scenario = ScenarioConfig(
    name="APB Response Handling",
    description="Verify APB response phase timing",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # Response valid triggers PREADY
        SignalRelation(
            cause=SignalEvent("i_rsp_valid", EdgeType.RISING),
            effect=SignalEvent("s_apb_PREADY", EdgeType.RISING),
            min_cycles=0,
            max_cycles=1,
            style=ArrowStyle.BLOCKING
        ),
        # PREADY leads to FSM transitioning to WAIT
        SignalRelation(
            cause=SignalEvent("s_apb_PREADY", EdgeType.RISING),
            effect=SignalEvent.state_change("r_apb_state", "BUSY", "WAIT"),
            min_cycles=0,
            max_cycles=1,
            style=ArrowStyle.BLOCKING
        ),
        # WAIT state always returns to IDLE
        SignalRelation(
            cause=SignalEvent.state_change("r_apb_state", "WAIT", "IDLE"),
            effect=SignalEvent("s_apb_PREADY", EdgeType.FALLING),
            min_cycles=0,
            max_cycles=1,
            style=ArrowStyle.STRAIGHT
        )
    ],
    debug_checks=[{
        'function': check_apb_pready_timing,
        'description': "Check PREADY timing"
    }]
)

apb_clock_gating_scenario = ScenarioConfig(
    name="Clock Gating Behavior",
    description="Verify APB clock gating activation/deactivation",
    pre_cycles=3,
    post_cycles=3,
    relations=[
        # Activity wakes up the clock
        SignalRelation(
            cause=SignalEvent("s_apb_PSEL", EdgeType.RISING),
            effect=SignalEvent("r_wakeup", EdgeType.RISING),
            min_cycles=0,
            max_cycles=1,
            style=ArrowStyle.STRAIGHT
        ),
        # Wakeup disables clock gating
        SignalRelation(
            cause=SignalEvent("r_wakeup", EdgeType.RISING),
            effect=SignalEvent("o_apb_clock_gating", EdgeType.FALLING),
            min_cycles=0,
            max_cycles=2,
            style=ArrowStyle.SPLINE
        )
    ],
    debug_checks=[{
        'function': check_clock_gating_behavior,
        'description': "Check clock gating behavior"
    }]
)

apb_protocol_scenario = ScenarioConfig(
    name="APB Protocol Compliance",
    description="Verify APB protocol compliance",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # PSEL must precede PENABLE
        SignalRelation(
            cause=SignalEvent("s_apb_PSEL", EdgeType.RISING),
            effect=SignalEvent("s_apb_PENABLE", EdgeType.RISING),
            min_cycles=1,
            max_cycles=1,
            style=ArrowStyle.STRAIGHT
        ),
    ],
    debug_checks=[{
        'function': check_apb_protocol_violations,
        'description': "Check APB protocol violations"
    }]
)

apb_state_machine_scenario = ScenarioConfig(
    name="APB State Machine",
    description="Verify APB state machine transitions",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # IDLE to BUSY
        SignalRelation(
            cause=SignalEvent.state_change("r_apb_state", "IDLE", "BUSY"),
            effect=SignalEvent("o_cmd_valid", EdgeType.RISING),
            min_cycles=0,
            max_cycles=1,
            style=ArrowStyle.STRAIGHT
        ),
        # BUSY to WAIT
        SignalRelation(
            cause=SignalEvent("s_apb_PREADY", EdgeType.RISING),
            effect=SignalEvent.state_change("r_apb_state", "BUSY", "WAIT"),
            min_cycles=0,
            max_cycles=1,
            style=ArrowStyle.STRAIGHT
        ),
        # WAIT to IDLE
        SignalRelation(
            cause=SignalEvent.state_change("r_apb_state", "WAIT", "IDLE"),
            effect=SignalEvent("s_apb_PENABLE", EdgeType.FALLING),
            min_cycles=0,
            max_cycles=1,
            style=ArrowStyle.STRAIGHT
        )
    ],
    debug_checks=[{
        'function': check_fsm_transitions,
        'description': "Check FSM transitions"
    }]
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
    
    # APB Interface signals - always include if they exist
    apb_signals = []
    for signal in ["s_apb_PSEL", "s_apb_PENABLE", "s_apb_PREADY", "s_apb_PWRITE", 
                  "s_apb_PWDATA", "s_apb_PRDATA", "s_apb_PSLVERR"]:
        if hasattr(dut, signal):
            apb_signals.append(signal)
            
    if apb_signals:
        groups["APB Interface"] = apb_signals
    
    # Control signals
    control_signals = []
    for signal in ["pclk", "presetn"]:
        if hasattr(dut, signal):
            control_signals.append(signal)
            
    if control_signals:
        groups["Control"] = control_signals
    
    # Clock gating signals
    cg_signals = []
    for signal in ["cg_pclk", "o_apb_clock_gating", "r_wakeup", "i_cfg_cg_enable", "i_cfg_cg_idle_count"]:
        if hasattr(dut, signal):
            cg_signals.append(signal)
            
    if cg_signals:
        groups["Clock Gating"] = cg_signals
    
    # Command channel signals
    cmd_signals = []
    for signal in ["o_cmd_valid", "i_cmd_ready", "o_cmd_pwrite", "o_cmd_pwdata", "o_cmd_paddr", "o_cmd_pstrb"]:
        if hasattr(dut, signal):
            cmd_signals.append(signal)
            
    if cmd_signals:
        groups["Command Channel"] = cmd_signals
    
    # Response channel signals
    rsp_signals = []
    for signal in ["i_rsp_valid", "o_rsp_ready", "i_rsp_prdata", "i_rsp_pslverr"]:
        if hasattr(dut, signal):
            rsp_signals.append(signal)
            
    if rsp_signals:
        groups["Response Channel"] = rsp_signals
    
    # State machine signals
    if hasattr(dut, "r_apb_state"):
        groups["State Machine"] = ["r_apb_state"]
    
    # If no signals were found, return the predefined groups
    if not groups:
        return APB_GROUPS
    
    return groups

def create_apb_scenarios(dut, include_scenarios=None):
    """
    Create APB scenarios based on available signals in the DUT
    
    Args:
        dut: Device under test
        include_scenarios: Optional list of scenario names to include
                          (None = all available)
    
    Returns:
        List of applicable scenarios
    """
    # Check which signals are available
    has_state = hasattr(dut, 'r_apb_state')
    has_cmd_channel = hasattr(dut, 'o_cmd_valid') and hasattr(dut, 'i_cmd_ready')
    has_rsp_channel = hasattr(dut, 'i_rsp_valid') and hasattr(dut, 'o_rsp_ready')
    has_clock_gating = hasattr(dut, 'o_apb_clock_gating') and hasattr(dut, 'r_wakeup')
    
    # Build list of applicable scenarios
    scenarios = []
    
    # Basic APB protocol scenario is always applicable
    if include_scenarios is None or 'protocol' in include_scenarios:
        scenarios.append(apb_protocol_scenario)
    
    # Setup scenario requires command channel
    if (include_scenarios is None or 'setup' in include_scenarios) and has_cmd_channel:
        scenarios.append(apb_setup_scenario)
    
    # Response scenario requires response channel
    if (include_scenarios is None or 'response' in include_scenarios) and has_rsp_channel:
        scenarios.append(apb_response_scenario)
    
    # State machine scenario requires state signal
    if (include_scenarios is None or 'state_machine' in include_scenarios) and has_state:
        scenarios.append(apb_state_machine_scenario)
    
    # Clock gating scenario requires clock gating signals
    if (include_scenarios is None or 'clock_gating' in include_scenarios) and has_clock_gating:
        scenarios.append(apb_clock_gating_scenario)
    
    return scenarios
