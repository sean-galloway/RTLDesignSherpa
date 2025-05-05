"""
Example CocoTB test demonstrating WaveDrom utilities
"""

import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer

# Import wavedrom utilities
from wavedrom_utils import (
    EdgeType, ArrowStyle, SignalEvent, SignalRelation,
    WaveformContainer, ScenarioConfig, CommonGroups
)

# Define debug check functions
async def check_protocol_timing(dut, wave_gen):
    """Check for req-ack protocol violations"""
    if dut.req.value == 1 and dut.ack.value == 0:
        cycles_since_req = wave_gen.cycles_since_event(
            SignalEvent("req", EdgeType.RISING)
        )
        if cycles_since_req > 3:
            wave_gen.add_debug_point(
                wave_gen.current_cycle,
                "Protocol violation: ACK not received within 3 cycles",
                {'req': 1, 'ack': 0, 'cycles': cycles_since_req}
            )
            return True
    return False

async def check_state_deadlock(dut, wave_gen):
    """Check for state machine deadlocks"""
    stuck_cycles = wave_gen.cycles_since_event(
        SignalEvent("state", EdgeType.ANY_CHANGE)
    )
    if stuck_cycles > 10:
        wave_gen.add_debug_point(
            wave_gen.current_cycle,
            f"State machine stuck in {dut.state.value} for {stuck_cycles} cycles",
            {'state': dut.state.value, 'stuck_cycles': stuck_cycles}
        )
        return True
    return False

# Create scenarios
protocol_scenario = ScenarioConfig(
    name="Protocol Timing Check",
    description="Verify request-acknowledge timing constraints",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        SignalRelation(
            cause=SignalEvent("req", EdgeType.RISING),
            effect=SignalEvent("ack", EdgeType.RISING),
            min_cycles=1,
            max_cycles=3,
            style=ArrowStyle.SETUP
        )
    ],
    debug_checks=[{
        'function': check_protocol_timing,
        'description': "Check req-ack timing"
    }]
)

state_scenario = ScenarioConfig(
    name="State Machine Deadlock",
    description="Detect potential state machine deadlocks",
    pre_cycles=5,
    post_cycles=2,
    relations=[
        SignalRelation(
            cause=SignalEvent.state_change("state", "BUSY", "DONE"),
            effect=SignalEvent("done", EdgeType.RISING),
            style=ArrowStyle.STRAIGHT
        )
    ],
    debug_checks=[{
        'function': check_state_deadlock,
        'description': "Check for stuck states"
    }]
)

@cocotb.test()
async def test_protocol_verification(dut):
    """Test protocol behaviors with waveform verification"""

    # Clock generation
    clock = dut.clk
    cocotb.start_soon(generate_clock(dut))

    # Reset
    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1

    # Use predefined signal groups and add custom ones
    signal_groups = CommonGroups.combine(
        CommonGroups.CONTROL,
        CommonGroups.REQ_ACK,
        CommonGroups.custom("Status", ["done", "error"]),
        {"State": ["state", "counter"]}
    )

    # Create container with scenarios
    container = WaveformContainer(
        title="Protocol Verification",
        clock_signal="clk",
        signal_groups=signal_groups,
        scenarios=[
            protocol_scenario,
            state_scenario
        ]
    )

    # Run all scenarios
    await container.run_all_scenarios(dut)

    # Generate final waveform
    container.generate_wavedrom("protocol_verification.json")

async def generate_clock(dut):
    """Generate clock signal"""
    while True:
        dut.clk.value = 0
        await Timer(5, units='ns')
        dut.clk.value = 1
        await Timer(5, units='ns')

