"""
AXI4 WaveDrom Utilities - Protocol Scenarios and Checks

This module provides AXI4-specific scenarios, checks, and signal groups for WaveDrom visualization.
"""

from CocoTBFramework.components.wavedrom_utils import (
    EdgeType, ArrowStyle, SignalEvent, SignalRelation,
    WaveformContainer, ScenarioConfig, CommonGroups
)
from CocoTBFramework.components.wavedrom_utils.protocol_checks import ProtocolType

# Define AXI4-specific signal groups
AXI4_GROUPS = {
    # Write Address Channel
    "AXI Write Address": [
        "axi_awvalid", "axi_awready", "axi_awid", "axi_awaddr", 
        "axi_awlen", "axi_awsize", "axi_awburst", "axi_awlock",
        "axi_awcache", "axi_awprot", "axi_awqos", "axi_awregion", "axi_awuser"
    ],
    # Write Data Channel
    "AXI Write Data": [
        "axi_wvalid", "axi_wready", "axi_wdata", "axi_wstrb", 
        "axi_wlast", "axi_wuser"
    ],
    # Write Response Channel
    "AXI Write Response": [
        "axi_bvalid", "axi_bready", "axi_bid", "axi_bresp", "axi_buser"
    ],
    # Read Address Channel
    "AXI Read Address": [
        "axi_arvalid", "axi_arready", "axi_arid", "axi_araddr", 
        "axi_arlen", "axi_arsize", "axi_arburst", "axi_arlock",
        "axi_arcache", "axi_arprot", "axi_arqos", "axi_arregion", "axi_aruser"
    ],
    # Read Data Channel
    "AXI Read Data": [
        "axi_rvalid", "axi_rready", "axi_rid", "axi_rdata", 
        "axi_rresp", "axi_rlast", "axi_ruser"
    ],
    # Control Signals
    "Control": ["axi_aclk", "axi_aresetn"],
    # Internal State
    "Internal State": ["r_write_state", "r_read_state"]
}

# Debug check functions for AXI4 protocol

async def check_axi_write_addr_data_ordering(dut, wave_gen):
    """Check if write address and data ordering follows protocol"""
    # Get master-side signals
    if not all(hasattr(dut, s) for s in ['axi_awvalid', 'axi_wvalid']):
        return False
        
    # Check if awvalid is asserted after wvalid without awready
    if (dut.axi_wvalid.value == 1 and 
        dut.axi_awvalid.value == 0 and 
        wave_gen.get_last_value("axi_awready") == 0):
        
        # Check how long wvalid has been asserted
        wvalid_cycles = wave_gen.cycles_since_event(
            SignalEvent("axi_wvalid", EdgeType.RISING)
        )
        
        if wvalid_cycles > 1:
            # This is a protocol violation - data can't be transferred
            # before the associated address
            wave_gen.add_debug_point(
                wave_gen.current_cycle,
                f"AXI4 Protocol Violation: Write data sent before address ({wvalid_cycles} cycles)",
                {'wvalid': 1, 'awvalid': 0, 'cycles': wvalid_cycles}
            )
            return True
    
    return False

async def check_axi_read_interleaving(dut, wave_gen):
    """Check if read data is interleaved properly with IDs"""
    if not all(hasattr(dut, s) for s in ['axi_rvalid', 'axi_rid']):
        return False
        
    # Check if a read response is being sent
    if dut.axi_rvalid.value == 1:
        # Get current read ID
        rid = dut.axi_rid.value
        
        # Check if there was a different transaction in progress
        prev_rvalid_event = wave_gen.cycles_since_event(
            SignalEvent("axi_rvalid", EdgeType.FALLING)
        )
        
        if prev_rvalid_event == 1:  # Just finished a read response
            prev_events = [(c, v) for c, s, v, e in wave_gen.event_history 
                          if s == "axi_rid" and c < wave_gen.current_cycle]
            
            if prev_events:
                prev_rid = max(prev_events, key=lambda x: x[0])[1]
                
                # Check if this is the start of a new interleaved transfer
                if (prev_rid != rid and 
                    hasattr(dut, 'axi_rlast') and 
                    wave_gen.get_last_value("axi_rlast") == 0):
                    # This is an interleaved transfer - not a violation but noteworthy
                    wave_gen.add_debug_point(
                        wave_gen.current_cycle,
                        f"AXI4 Interleaved Read: ID change from {prev_rid} to {rid} mid-transfer",
                        {'prev_rid': prev_rid, 'current_rid': rid}
                    )
                    return True
    
    return False

async def check_axi_write_resp_ordering(dut, wave_gen):
    """Check write response ordering follows protocol"""
    if not all(hasattr(dut, s) for s in ['axi_bvalid', 'axi_wlast']):
        return False
        
    # Check if a write response is being sent
    if dut.axi_bvalid.value == 1:
        # Check if wlast was received before bvalid
        wlast_before_bvalid = False
        
        # Search event history for wlast assertion before bvalid
        bvalid_rising_cycle = 0
        for cycle, sig, val, edge in reversed(wave_gen.event_history):
            if sig == "axi_bvalid" and edge == EdgeType.RISING:
                bvalid_rising_cycle = cycle
                break
                
        for cycle, sig, val, edge in reversed(wave_gen.event_history):
            if sig == "axi_wlast" and val == 1 and cycle < bvalid_rising_cycle:
                wlast_before_bvalid = True
                break
        
        if not wlast_before_bvalid:
            # This is a protocol violation - response can't be sent before last data
            wave_gen.add_debug_point(
                wave_gen.current_cycle,
                "AXI4 Protocol Violation: Write response sent before last data",
                {'bvalid': 1, 'wlast_seen': wlast_before_bvalid}
            )
            return True
    
    return False

async def check_axi_exclusive_access(dut, wave_gen):
    """Check exclusive access protocol compliance"""
    # Only check if exclusive signals are present
    if not any(hasattr(dut, s) for s in ['axi_awlock', 'axi_arlock']):
        return False
        
    # Check for exclusive read followed by non-exclusive write to same address
    if (hasattr(dut, 'axi_arvalid') and hasattr(dut, 'axi_arlock') and
        dut.axi_arvalid.value == 1 and dut.axi_arlock.value == 1):  # Exclusive read
        
        # Remember address for exclusive read
        if hasattr(dut, 'axi_araddr'):
            excl_addr = dut.axi_araddr.value
            
            # Add annotation for exclusive read
            wave_gen.add_debug_point(
                wave_gen.current_cycle,
                f"AXI4 Exclusive Read: address 0x{excl_addr:X}",
                {'arvalid': 1, 'arlock': 1, 'araddr': excl_addr}
            )
            return True
    
    return False

async def check_axi_burst_boundary(dut, wave_gen):
    """Check if AXI bursts cross 4KB boundaries (violation)"""
    if not all(hasattr(dut, s) for s in ['axi_awvalid', 'axi_awaddr', 'axi_awlen']):
        return False
        
    # Check for address phase of burst transaction
    if dut.axi_awvalid.value == 1 and dut.axi_awlen.value > 0:
        # Get burst parameters
        addr = dut.axi_awaddr.value
        length = dut.axi_awlen.value + 1  # AXI defines length as awlen+1
        
        # Check if burst has size information
        if hasattr(dut, 'axi_awsize'):
            size = dut.axi_awsize.value
            bytes_per_beat = 1 << size
        else:
            # Assume data width / 8 if size not available
            if hasattr(dut, 'DATA_WIDTH'):
                bytes_per_beat = dut.DATA_WIDTH // 8
            else:
                bytes_per_beat = 4  # Default to 32-bit
        
        # Calculate end address of burst
        end_addr = addr + (length * bytes_per_beat) - 1
        
        # Check if burst crosses 4KB boundary (lower 12 bits of address)
        if (addr & 0xFFFFF000) != (end_addr & 0xFFFFF000):
            wave_gen.add_debug_point(
                wave_gen.current_cycle,
                "AXI4 Protocol Violation: Burst crosses 4KB boundary",
                {'addr': addr, 'end_addr': end_addr, 'length': length, 'bytes_per_beat': bytes_per_beat}
            )
            return True
    
    return False

async def check_axi_handshake_stalls(dut, wave_gen):
    """Check for stalled handshakes on any AXI channel"""
    # List of valid/ready pairs to check
    channels = [
        ('axi_awvalid', 'axi_awready'),
        ('axi_wvalid', 'axi_wready'),
        ('axi_bvalid', 'axi_bready'),
        ('axi_arvalid', 'axi_arready'),
        ('axi_rvalid', 'axi_rready')
    ]
    
    for valid_signal, ready_signal in channels:
        # Skip channels that don't exist in the DUT
        if not all(hasattr(dut, s) for s in [valid_signal, ready_signal]):
            continue
            
        # Check for valid without ready
        if getattr(dut, valid_signal).value == 1 and getattr(dut, ready_signal).value == 0:
            # Check how long valid has been asserted
            valid_cycles = wave_gen.cycles_since_event(
                SignalEvent(valid_signal, EdgeType.RISING)
            )
            
            # Report if stalled for too long (threshold depends on channel)
            if valid_cycles > 10:  # Using 10 as a general threshold
                wave_gen.add_debug_point(
                    wave_gen.current_cycle,
                    f"AXI4 Handshake Stall: {valid_signal} asserted without {ready_signal} for {valid_cycles} cycles",
                    {valid_signal: 1, ready_signal: 0, 'cycles': valid_cycles}
                )
                return True
    
    return False

# Predefined AXI4 scenarios

axi4_write_scenario = ScenarioConfig(
    name="AXI4 Write Transaction",
    description="Verify AXI4 write transaction flow",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # Write address and write data handshakes
        SignalRelation(
            cause=SignalEvent("axi_awvalid", EdgeType.RISING),
            effect=SignalEvent("axi_awready", EdgeType.RISING),
            min_cycles=0,
            max_cycles=None,  # No specific timing requirement
            style=ArrowStyle.SPLINE
        ),
        SignalRelation(
            cause=SignalEvent("axi_wvalid", EdgeType.RISING),
            effect=SignalEvent("axi_wready", EdgeType.RISING),
            min_cycles=0,
            max_cycles=None,  # No specific timing requirement
            style=ArrowStyle.SPLINE
        ),
        # Last write data triggers write response
        SignalRelation(
            cause=SignalEvent("axi_wlast", EdgeType.RISING),
            effect=SignalEvent("axi_bvalid", EdgeType.RISING),
            min_cycles=1,
            max_cycles=None,
            style=ArrowStyle.SPLINE
        )
    ],
    debug_checks=[
        {
            'function': check_axi_write_addr_data_ordering,
            'description': "Check address/data ordering"
        },
        {
            'function': check_axi_write_resp_ordering,
            'description': "Check write response ordering"
        },
        {
            'function': check_axi_burst_boundary,
            'description': "Check burst boundary"
        }
    ]
)

axi4_read_scenario = ScenarioConfig(
    name="AXI4 Read Transaction",
    description="Verify AXI4 read transaction flow",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # Read address handshake
        SignalRelation(
            cause=SignalEvent("axi_arvalid", EdgeType.RISING),
            effect=SignalEvent("axi_arready", EdgeType.RISING),
            min_cycles=0,
            max_cycles=None,  # No specific timing requirement
            style=ArrowStyle.SPLINE
        ),
        # Address acceptance triggers read data
        SignalRelation(
            cause=SignalEvent("axi_arready", EdgeType.RISING),
            effect=SignalEvent("axi_rvalid", EdgeType.RISING),
            min_cycles=1,
            max_cycles=None,
            style=ArrowStyle.SPLINE
        ),
        # Read data handshake
        SignalRelation(
            cause=SignalEvent("axi_rvalid", EdgeType.RISING),
            effect=SignalEvent("axi_rready", EdgeType.RISING),
            min_cycles=0,
            max_cycles=None,
            style=ArrowStyle.SPLINE
        )
    ],
    debug_checks=[
        {
            'function': check_axi_read_interleaving,
            'description': "Check read interleaving"
        },
        {
            'function': check_axi_burst_boundary,
            'description': "Check burst boundary"
        }
    ]
)

axi4_handshake_scenario = ScenarioConfig(
    name="AXI4 Handshake Timing",
    description="Verify AXI4 handshake timing behavior",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # All valid-ready handshake pairs
        SignalRelation(
            cause=SignalEvent("axi_awvalid", EdgeType.RISING),
            effect=SignalEvent("axi_awready", EdgeType.RISING),
            min_cycles=0,
            max_cycles=None,
            style=ArrowStyle.SPLINE
        ),
        SignalRelation(
            cause=SignalEvent("axi_wvalid", EdgeType.RISING),
            effect=SignalEvent("axi_wready", EdgeType.RISING),
            min_cycles=0,
            max_cycles=None,
            style=ArrowStyle.SPLINE
        ),
        SignalRelation(
            cause=SignalEvent("axi_bvalid", EdgeType.RISING),
            effect=SignalEvent("axi_bready", EdgeType.RISING),
            min_cycles=0,
            max_cycles=None,
            style=ArrowStyle.SPLINE
        ),
        SignalRelation(
            cause=SignalEvent("axi_arvalid", EdgeType.RISING),
            effect=SignalEvent("axi_arready", EdgeType.RISING),
            min_cycles=0,
            max_cycles=None,
            style=ArrowStyle.SPLINE
        ),
        SignalRelation(
            cause=SignalEvent("axi_rvalid", EdgeType.RISING),
            effect=SignalEvent("axi_rready", EdgeType.RISING),
            min_cycles=0,
            max_cycles=None,
            style=ArrowStyle.SPLINE
        )
    ],
    debug_checks=[
        {
            'function': check_axi_handshake_stalls,
            'description': "Check handshake stalls"
        }
    ]
)

axi4_exclusive_scenario = ScenarioConfig(
    name="AXI4 Exclusive Access",
    description="Verify AXI4 exclusive access behavior",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # Exclusive read followed by exclusive write
        SignalRelation(
            cause=SignalEvent("axi_arlock", EdgeType.RISING),
            effect=SignalEvent("axi_awlock", EdgeType.RISING),
            min_cycles=1,
            max_cycles=None,
            style=ArrowStyle.SPLINE
        ),
        # Exclusive write response indicates success/failure
        SignalRelation(
            cause=SignalEvent("axi_awlock", EdgeType.RISING),
            effect=SignalEvent("axi_bresp", EdgeType.ANY_CHANGE),
            min_cycles=1,
            max_cycles=None,
            style=ArrowStyle.SPLINE
        )
    ],
    debug_checks=[
        {
            'function': check_axi_exclusive_access,
            'description': "Check exclusive access protocol"
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
    
    # Check which AXI channels are present
    # Write Address Channel
    wa_signals = []
    for signal in ["axi_awvalid", "axi_awready", "axi_awid", "axi_awaddr", 
                   "axi_awlen", "axi_awsize", "axi_awburst", "axi_awlock",
                   "axi_awcache", "axi_awprot", "axi_awqos", "axi_awregion", "axi_awuser"]:
        if hasattr(dut, signal):
            wa_signals.append(signal)
            
    if wa_signals:
        groups["AXI Write Address"] = wa_signals
    
    # Write Data Channel
    wd_signals = []
    for signal in ["axi_wvalid", "axi_wready", "axi_wdata", "axi_wstrb", 
                   "axi_wlast", "axi_wuser"]:
        if hasattr(dut, signal):
            wd_signals.append(signal)
            
    if wd_signals:
        groups["AXI Write Data"] = wd_signals
    
    # Write Response Channel
    wr_signals = []
    for signal in ["axi_bvalid", "axi_bready", "axi_bid", "axi_bresp", "axi_buser"]:
        if hasattr(dut, signal):
            wr_signals.append(signal)
            
    if wr_signals:
        groups["AXI Write Response"] = wr_signals
    
    # Read Address Channel
    ra_signals = []
    for signal in ["axi_arvalid", "axi_arready", "axi_arid", "axi_araddr", 
                   "axi_arlen", "axi_arsize", "axi_arburst", "axi_arlock",
                   "axi_arcache", "axi_arprot", "axi_arqos", "axi_arregion", "axi_aruser"]:
        if hasattr(dut, signal):
            ra_signals.append(signal)
            
    if ra_signals:
        groups["AXI Read Address"] = ra_signals
    
    # Read Data Channel
    rd_signals = []
    for signal in ["axi_rvalid", "axi_rready", "axi_rid", "axi_rdata", 
                   "axi_rresp", "axi_rlast", "axi_ruser"]:
        if hasattr(dut, signal):
            rd_signals.append(signal)
            
    if rd_signals:
        groups["AXI Read Data"] = rd_signals
    
    # Control Signals
    control_signals = []
    for signal in ["axi_aclk", "axi_aresetn"]:
        if hasattr(dut, signal):
            control_signals.append(signal)
            
    if control_signals:
        groups["Control"] = control_signals
    
    # Internal State
    state_signals = []
    for signal in ["r_write_state", "r_read_state"]:
        if hasattr(dut, signal):
            state_signals.append(signal)
            
    if state_signals:
        groups["Internal State"] = state_signals
    
    # If no signals were found, return the predefined groups
    if not groups:
        return AXI4_GROUPS
    
    return groups

def create_axi4_scenarios(dut, include_scenarios=None):
    """
    Create AXI4 scenarios based on available signals in the DUT
    
    Args:
        dut: Device under test
        include_scenarios: Optional list of scenario names to include
                          (None = all available)
    
    Returns:
        List of applicable scenarios
    """
    # Check which signals are available
    has_write_addr = hasattr(dut, 'axi_awvalid') and hasattr(dut, 'axi_awready')
    has_write_data = hasattr(dut, 'axi_wvalid') and hasattr(dut, 'axi_wready')
    has_write_resp = hasattr(dut, 'axi_bvalid') and hasattr(dut, 'axi_bready')
    has_write = has_write_addr and has_write_data and has_write_resp
    
    has_read_addr = hasattr(dut, 'axi_arvalid') and hasattr(dut, 'axi_arready')
    has_read_data = hasattr(dut, 'axi_rvalid') and hasattr(dut, 'axi_rready')
    has_read = has_read_addr and has_read_data
    
    has_lock = hasattr(dut, 'axi_awlock') or hasattr(dut, 'axi_arlock')
    
    # Build list of applicable scenarios
    scenarios = []
    
    # Write transaction scenario
    if (include_scenarios is None or 'write' in include_scenarios) and has_write:
        scenarios.append(axi4_write_scenario)
    
    # Read transaction scenario
    if (include_scenarios is None or 'read' in include_scenarios) and has_read:
        scenarios.append(axi4_read_scenario)
    
    # Handshake scenario requires at least one channel
    if (include_scenarios is None or 'handshake' in include_scenarios) and (has_write or has_read):
        scenarios.append(axi4_handshake_scenario)
    
    # Exclusive access scenario requires lock signals
    if (include_scenarios is None or 'exclusive' in include_scenarios) and has_lock:
        scenarios.append(axi4_exclusive_scenario)
    
    return scenarios
