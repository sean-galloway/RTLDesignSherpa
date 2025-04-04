"""APB Wavedrom Scenarios"""

import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.clock import Clock

# Import wavedrom utilities
from CocoTBFramework.components.wavedrom_utils import (
    EdgeType, ArrowStyle, SignalEvent, SignalRelation,
    WaveformContainer, ScenarioConfig, CommonGroups
)

# Define APB-specific signal groups
APB_GROUPS = {
    "APB Interface": ["s_apb_PSEL", "s_apb_PENABLE", "s_apb_PREADY", "s_apb_PWRITE", 
    "s_apb_PWDATA", "s_apb_PRDATA", "s_apb_PSLVERR"],
    "Control": ["pclk", "presetn", "cg_pclk", "o_apb_clock_gating", "r_wakeup"],
    "Command Channel": ["o_cmd_valid", "i_cmd_ready", "o_cmd_pwrite", "o_cmd_pwdata"],
    "Response Channel": ["i_rsp_valid", "o_rsp_ready", "i_rsp_prdata", "i_rsp_pslverr"],
    "State Machine": ["r_apb_state"]
}

async def check_clock_gating_behavior(dut, wave_gen):
    """Check for proper clock gating behavior"""
    
    # Only check if clock gating is enabled
    if dut.i_cfg_cg_enable.value == 0:
        return False
    
    # Check if in IDLE state with no activity but clock not gated
    if (dut.r_apb_state.value.integer == 1 and  # IDLE state (assuming IDLE=1 in enum)
        dut.s_apb_PSEL.value == 0 and
        dut.o_cmd_valid.value == 0 and
        dut.i_rsp_valid.value == 0):
        
        # If we've been idle for longer than idle_count, clock should be gated
        idle_cycles = wave_gen.cycles_since_event(
            SignalEvent("r_apb_state", EdgeType.ANY_CHANGE, 1)  # IDLE is 1
        )
        
        idle_count = dut.i_cfg_cg_idle_count.value
        
        # Clock should be gated after idle_count + 2 (allowing for implementation delay)
        if idle_cycles > idle_count + 2 and dut.o_apb_clock_gating.value == 0:
            wave_gen.add_debug_point(
                wave_gen.current_cycle,
                f"Clock Gating Issue: Not gated after {idle_cycles} idle cycles (limit: {idle_count})",
                {'idle_cycles': idle_cycles, 'idle_limit': idle_count}
            )
            return True
    
    # Check for incorrect gating during active states
    if dut.o_apb_clock_gating.value == 1 and (dut.r_apb_state.value.integer != 1 or  # Not in IDLE state
                dut.s_apb_PSEL.value == 1 or
                dut.o_cmd_valid.value == 1 or
                dut.i_rsp_valid.value == 1):
        wave_gen.add_debug_point(
            wave_gen.current_cycle,
            "Clock Gating Issue: Clock gated during active operation",
            {'state': dut.r_apb_state.value.integer, 
                'psel': dut.s_apb_PSEL.value,
                'cmd_valid': dut.o_cmd_valid.value,
                'rsp_valid': dut.i_rsp_valid.value}
        )
        return True
    
    return False

# Define debug check functions for APB protocol
async def check_apb_pready_timing(dut, wave_gen):
    """Check if PREADY is properly asserted after cmd_valid and rsp_valid"""
    # We're in a BUSY state but PREADY hasn't been asserted for too long
    if dut.r_apb_state.value.integer == 2:  # BUSY state
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

# Setup the APB scenarios
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
    debug_checks=[
        {
            'function': check_command_response_handshake,
            'description': "Check command handshake"
        }
    ]
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
    debug_checks=[
        {
            'function': check_apb_pready_timing,
            'description': "Check PREADY timing"
        }
    ]
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
    ]
)

# APB Protocol violation checks
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
    if dut.s_apb_PSEL.value == 1 and dut.s_apb_PENABLE.value == 1 and dut.r_apb_state.value.integer == 2:  # BUSY
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
    if dut.s_apb_PREADY.value == 0 and dut.r_apb_state.value.integer == 2:  # BUSY
        # Look for PSEL/PENABLE changes
        psel_toggle = wave_gen.cycles_since_event(
            SignalEvent("s_apb_PSEL", EdgeType.ANY_CHANGE)
        )
        if psel_toggle < busy_cycles:
            wave_gen.add_debug_point(
                wave_gen.current_cycle,
                "APB Protocol Violation: PSEL changed during active transfer",
                {'state': "BUSY", 'PSEL_changed': True}
            )
            return True
    
    return False

# FSM state transition monitoring
async def check_fsm_transitions(dut, wave_gen):
    """Monitor FSM state transitions for correctness"""
    
    # 1. Check for invalid state transitions
    current_state = dut.r_apb_state.value.integer

    # Get previous state if available
    prev_state_event = wave_gen.cycles_since_event(
        SignalEvent("r_apb_state", EdgeType.ANY_CHANGE)
    )

    if prev_state_event == 1:  # Just had a transition last cycle
        if prev_events := [
            (c, v)
            for c, s, v, e in wave_gen.event_history
            if s == "r_apb_state" and c < wave_gen.current_cycle
        ]:
            prev_state = max(prev_events, key=lambda x: x[0])[1]

            # Check valid transitions
            # IDLE(1) -> BUSY(2) -> WAIT(4) -> IDLE(1)
            valid_transitions = {
                1: [2],     # IDLE -> BUSY
                2: [4],     # BUSY -> WAIT
                4: [1]      # WAIT -> IDLE
            }

            if current_state not in valid_transitions.get(prev_state, []):
                wave_gen.add_debug_point(
                    wave_gen.current_cycle,
                    f"Invalid FSM transition: {prev_state} -> {current_state}",
                    {'prev_state': prev_state, 'current_state': current_state}
                )
                return True

    return False

# Clock gating monitoring
async def check_clock_gating(dut, wave_gen):
    """Check for proper clock gating behavior"""
    
    # Check if in IDLE state with no activity but clock not gated
    if (dut.r_apb_state.value.integer == 1 and  # IDLE state
        dut.s_apb_PSEL.value == 0 and
        dut.o_cmd_valid.value == 0 and
        dut.i_rsp_valid.value == 0 and
        dut.o_apb_clock_gating.value == 0):
        
        # How long have we been idle?
        idle_cycles = wave_gen.cycles_since_event(
            SignalEvent("r_apb_state", EdgeType.ANY_CHANGE, 1)  # IDLE is 1
        )
        
        # Should be gated after idle_count cycles
        idle_count = dut.i_cfg_cg_idle_count.value
        
        if idle_cycles > idle_count + 3:  # Allow a couple extra cycles for logic
            wave_gen.add_debug_point(
                wave_gen.current_cycle,
                f"Clock Gating Issue: Still active after {idle_cycles} idle cycles (limit: {idle_count})",
                {'idle_cycles': idle_cycles, 'idle_limit': idle_count}
            )
            return True
    
    return False

# Command-Response FIFO monitoring
async def check_fifo_overrun(dut, wave_gen):
    """Check for potential FIFO overruns in command or response paths"""
    
    # Check command FIFO count approaching limit
    cmd_count = dut.r_cmd_count.value
    if cmd_count >= 3:  # Nearing FIFO depth of SKID_DEPTH
        wave_gen.add_debug_point(
            wave_gen.current_cycle,
            f"Command FIFO nearing capacity: {cmd_count}/4 entries used",
            {'cmd_count': cmd_count, 'cmd_valid': dut.o_cmd_valid.value, 'cmd_ready': dut.i_cmd_ready.value}
        )
        return True
        
    # Check response FIFO count approaching limit
    rsp_count = dut.r_rsp_count.value
    if rsp_count >= 3:  # Nearing FIFO depth of SKID_DEPTH
        wave_gen.add_debug_point(
            wave_gen.current_cycle,
            f"Response FIFO nearing capacity: {rsp_count}/4 entries used",
            {'rsp_count': rsp_count, 'rsp_valid': dut.i_rsp_valid.value, 'rsp_ready': dut.o_rsp_ready.value}
        )
        return True
    
    return False