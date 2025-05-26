"""
Standard protocol checks for WaveDrom verification

This module provides reusable verification checks for common protocol patterns
and violations that can be used with the WaveDrom generator.
"""

from typing import Dict, Any, Callable, Awaitable
from enum import Enum, auto

from .models import SignalEvent, EdgeType


class ProtocolType(Enum):
    """Types of protocols for check selection"""
    HANDSHAKE = auto()  # Basic valid/ready or req/ack handshake
    STATE_MACHINE = auto()  # State machine transitions
    CLOCK_GATING = auto()  # Clock gating control
    FIFO = auto()  # FIFO buffer checks
    MEMORY = auto()  # Memory interface
    APB = auto()  # APB protocol
    AXI = auto()  # AXI protocol
    SPI = auto()  # SPI protocol
    I2C = auto()  # I2C protocol


async def check_handshake_stall(dut, wave_gen, valid_signal="valid", ready_signal="ready", timeout=5):
    """
    Check for handshake protocol stalls (valid without ready for too long)
    
    Args:
        dut: Device under test
        wave_gen: WaveDrom generator instance
        valid_signal: Name of the valid signal
        ready_signal: Name of the ready signal
        timeout: Maximum cycles valid can be asserted without ready
        
    Returns:
        bool: True if a stall is detected
    """
    # Get the DUT signal values
    valid_value = getattr(dut, valid_signal).value
    ready_value = getattr(dut, ready_signal).value
    
    # Check for valid without ready
    if valid_value == 1 and ready_value == 0:
        # Check how long valid has been asserted
        cycles_since_valid = wave_gen.cycles_since_event(
            SignalEvent(valid_signal, EdgeType.RISING)
        )
        
        if cycles_since_valid > timeout:
            wave_gen.add_debug_point(
                wave_gen.current_cycle,
                f"Handshake stall: {valid_signal} asserted without {ready_signal} for {cycles_since_valid} cycles",
                {valid_signal: 1, ready_signal: 0, 'cycles': cycles_since_valid}
            )
            return True
            
    return False


async def check_ready_without_valid(dut, wave_gen, valid_signal="valid", ready_signal="ready"):
    """
    Check for ready asserted without valid (potential protocol violation)
    
    Args:
        dut: Device under test
        wave_gen: WaveDrom generator instance
        valid_signal: Name of the valid signal
        ready_signal: Name of the ready signal
        
    Returns:
        bool: True if violation is detected
    """
    # Get the DUT signal values
    valid_value = getattr(dut, valid_signal).value
    ready_value = getattr(dut, ready_signal).value
    
    # Check for ready without valid
    if valid_value == 0 and ready_value == 1:
        # How long has ready been high without valid?
        cycles_since_ready = wave_gen.cycles_since_event(
            SignalEvent(ready_signal, EdgeType.RISING)
        )
        
        if cycles_since_ready > 0:  # Just detecting the condition
            wave_gen.add_debug_point(
                wave_gen.current_cycle,
                f"Protocol note: {ready_signal} asserted without {valid_signal}",
                {valid_signal: 0, ready_signal: 1, 'cycles': cycles_since_ready}
            )
            return True
            
    return False


async def check_state_deadlock(dut, wave_gen, state_signal="state", timeout=10):
    """
    Check for state machine deadlock (stuck in same state too long)
    
    Args:
        dut: Device under test
        wave_gen: WaveDrom generator instance
        state_signal: Name of the state signal
        timeout: Maximum cycles in same state before considered deadlocked
        
    Returns:
        bool: True if deadlock is detected
    """
    # How long since state last changed?
    stuck_cycles = wave_gen.cycles_since_event(
        SignalEvent(state_signal, EdgeType.ANY_CHANGE)
    )
    
    if stuck_cycles > timeout:
        # Get current state value
        try:
            state_value = getattr(dut, state_signal).value
            # Check if it's an integer object with value property
            if hasattr(state_value, "integer"):
                state_value = state_value.integer
        except AttributeError:
            state_value = "unknown"
            
        wave_gen.add_debug_point(
            wave_gen.current_cycle,
            f"Potential deadlock: {state_signal} stuck in {state_value} for {stuck_cycles} cycles",
            {state_signal: state_value, 'stuck_cycles': stuck_cycles}
        )
        return True
        
    return False


async def check_fifo_overflow(dut, wave_gen, count_signal="count", capacity=8, threshold=0.8):
    """
    Check for FIFO near-overflow condition
    
    Args:
        dut: Device under test
        wave_gen: WaveDrom generator instance
        count_signal: Name of the FIFO count signal
        capacity: Maximum FIFO capacity
        threshold: Threshold percentage for warning (0.0-1.0)
        
    Returns:
        bool: True if near-overflow is detected
    """
    try:
        # Get current count value
        count_value = getattr(dut, count_signal).value
        # Check if it's an integer object with value property
        if hasattr(count_value, "integer"):
            count_value = count_value.integer
            
        # Check if count exceeds threshold
        warning_threshold = int(capacity * threshold)
        if count_value >= warning_threshold:
            wave_gen.add_debug_point(
                wave_gen.current_cycle,
                f"FIFO near capacity: {count_value}/{capacity} entries used ({int(count_value/capacity*100)}%)",
                {'count': count_value, 'capacity': capacity, 'percentage': count_value/capacity}
            )
            return True
    except (AttributeError, TypeError):
        # If count signal doesn't exist or isn't accessible, don't report
        pass
        
    return False


async def check_clock_gating(dut, wave_gen, state_signal="state", idle_state=1, 
                           clock_gate_signal="clock_gating", idle_count_signal=None):
    """
    Check for proper clock gating behavior
    
    Args:
        dut: Device under test
        wave_gen: WaveDrom generator instance
        state_signal: Name of the state signal
        idle_state: Value representing the idle state
        clock_gate_signal: Name of the clock gating control signal
        idle_count_signal: Optional signal indicating required idle cycles
        
    Returns:
        bool: True if clock gating issue is detected
    """
    try:
        # Get current state and clock gating values
        state_value = getattr(dut, state_signal).value
        if hasattr(state_value, "integer"):
            state_value = state_value.integer
            
        clock_gate_value = getattr(dut, clock_gate_signal).value
        
        # Determine idle threshold
        idle_threshold = 5  # Default
        if idle_count_signal:
            try:
                count_value = getattr(dut, idle_count_signal).value
                if hasattr(count_value, "integer"):
                    idle_threshold = count_value.integer
            except AttributeError:
                pass
                
        # Check if in idle state
        if state_value == idle_state:
            # How long in idle state?
            idle_cycles = wave_gen.cycles_since_event(
                SignalEvent(state_signal, EdgeType.ANY_CHANGE, idle_state)
            )
            
            # Should be gated after idle_threshold cycles
            if idle_cycles > idle_threshold + 2:  # Allow a couple extra cycles for implementation
                if clock_gate_value == 0:  # Not gated (assuming 1=gated, 0=not gated)
                    wave_gen.add_debug_point(
                        wave_gen.current_cycle,
                        f"Clock Gating Issue: Still active after {idle_cycles} idle cycles (threshold: {idle_threshold})",
                        {'idle_cycles': idle_cycles, 'idle_threshold': idle_threshold}
                    )
                    return True
        # Check for incorrect gating during active state            
        elif clock_gate_value == 1:  # Gated during active state
            wave_gen.add_debug_point(
                wave_gen.current_cycle,
                f"Clock Gating Issue: Clock gated during active state {state_value}",
                {'state': state_value, 'clock_gate': 1}
            )
            return True
    except AttributeError:
        # If signals don't exist or aren't accessible, don't report
        pass
        
    return False


async def check_invalid_state_transition(dut, wave_gen, state_signal="state", 
                                       valid_transitions=None):
    """
    Check for invalid state machine transitions
    
    Args:
        dut: Device under test
        wave_gen: WaveDrom generator instance
        state_signal: Name of the state signal
        valid_transitions: Dictionary mapping from states to valid next states
        
    Returns:
        bool: True if invalid transition is detected
    """
    if valid_transitions is None:
        return False
        
    # Check if state just changed this cycle
    prev_state_event = wave_gen.cycles_since_event(
        SignalEvent(state_signal, EdgeType.ANY_CHANGE)
    )
    
    if prev_state_event == 1:  # Just had a transition last cycle
        try:
            # Get current state
            current_state = getattr(dut, state_signal).value
            if hasattr(current_state, "integer"):
                current_state = current_state.integer
                
            # Get value before most recent change from event history
            prev_events = [(c, v) for c, s, v, e in wave_gen.event_history 
                           if s == state_signal and c < wave_gen.current_cycle]
            
            if prev_events:
                prev_state = max(prev_events, key=lambda x: x[0])[1]
                
                # Check if transition is valid
                if prev_state in valid_transitions and current_state not in valid_transitions[prev_state]:
                    wave_gen.add_debug_point(
                        wave_gen.current_cycle,
                        f"Invalid state transition: {prev_state} -> {current_state}",
                        {'prev_state': prev_state, 'current_state': current_state}
                    )
                    return True
        except (AttributeError, IndexError):
            # If state signal doesn't exist or event history is incomplete, don't report
            pass
            
    return False


def create_protocol_checks(protocol_type: ProtocolType, **kwargs) -> Dict[str, Dict[str, Any]]:
    """
    Create standard protocol checks for a specific protocol
    
    Args:
        protocol_type: Type of protocol to create checks for
        **kwargs: Protocol-specific configuration parameters
        
    Returns:
        Dictionary of debug check configurations
    """
    checks = []
    
    if protocol_type == ProtocolType.HANDSHAKE:
        valid_signal = kwargs.get('valid_signal', 'valid')
        ready_signal = kwargs.get('ready_signal', 'ready')
        timeout = kwargs.get('timeout', 5)
        
        checks.append({
            'function': lambda dut, wave_gen: check_handshake_stall(
                dut, wave_gen, valid_signal, ready_signal, timeout
            ),
            'description': f"Check {valid_signal}/{ready_signal} handshake stalls"
        })
        
        checks.append({
            'function': lambda dut, wave_gen: check_ready_without_valid(
                dut, wave_gen, valid_signal, ready_signal
            ),
            'description': f"Check {ready_signal} without {valid_signal}"
        })
        
    elif protocol_type == ProtocolType.STATE_MACHINE:
        state_signal = kwargs.get('state_signal', 'state')
        timeout = kwargs.get('timeout', 10)
        valid_transitions = kwargs.get('valid_transitions', None)
        
        checks.append({
            'function': lambda dut, wave_gen: check_state_deadlock(
                dut, wave_gen, state_signal, timeout
            ),
            'description': f"Check {state_signal} deadlock"
        })
        
        if valid_transitions:
            checks.append({
                'function': lambda dut, wave_gen: check_invalid_state_transition(
                    dut, wave_gen, state_signal, valid_transitions
                ),
                'description': f"Check {state_signal} invalid transitions"
            })
            
    elif protocol_type == ProtocolType.FIFO:
        count_signal = kwargs.get('count_signal', 'count')
        capacity = kwargs.get('capacity', 8)
        threshold = kwargs.get('threshold', 0.8)
        
        checks.append({
            'function': lambda dut, wave_gen: check_fifo_overflow(
                dut, wave_gen, count_signal, capacity, threshold
            ),
            'description': f"Check {count_signal} overflow"
        })
        
    elif protocol_type == ProtocolType.CLOCK_GATING:
        state_signal = kwargs.get('state_signal', 'state')
        idle_state = kwargs.get('idle_state', 1)
        clock_gate_signal = kwargs.get('clock_gate_signal', 'clock_gating')
        idle_count_signal = kwargs.get('idle_count_signal', None)
        
        checks.append({
            'function': lambda dut, wave_gen: check_clock_gating(
                dut, wave_gen, state_signal, idle_state, clock_gate_signal, idle_count_signal
            ),
            'description': f"Check {clock_gate_signal} behavior"
        })
    
    # Return as a dictionary keyed by description
    return {check['description']: check for check in checks}
