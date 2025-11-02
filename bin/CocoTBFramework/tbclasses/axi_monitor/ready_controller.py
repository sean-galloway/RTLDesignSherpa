# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: HandshakeEvent
# Purpose: AXI Monitor Ready Controller - Streamlined for Final Testbench
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI Monitor Ready Controller - Streamlined for Final Testbench

Provides independent control over AXI ready signals for monitor testing.
Since monitors are passive observers, ready signals need independent control
separate from the valid/data signal generation.

Streamlined Features:
- Pre-assert ready (ready before valid)
- Delayed ready (N cycles after valid)
- FlexRandomizer integration (TB provides randomizer)
- Handshake notification callbacks
- Simplified API for testbench use
"""

import asyncio
from typing import Dict, List, Optional, Callable, Union, Any
from collections import deque
import cocotb
from cocotb.triggers import RisingEdge, Timer, Combine, First
from cocotb.utils import get_sim_time

from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer


class HandshakeEvent:
    """Information about a valid/ready handshake event"""

    def __init__(self, timestamp: float, ready_delay: int, pattern_info: str = ""):
        self.timestamp = timestamp
        self.ready_delay = ready_delay  # Cycles from valid to ready
        self.pattern_info = pattern_info

    def __repr__(self):
        return f"Handshake @ {self.timestamp:.1f}ns (delay={self.ready_delay}, {self.pattern_info})"


class ReadyController:
    """
    Independent control of AXI ready signals for monitor testing.

    Provides sophisticated ready signal patterns while monitoring valid signals
    to generate proper handshake timing and notifications.
    """

    def __init__(self, dut, ready_signal_name: str, valid_signal_name: str,
                    clock_name: str = 'aclk', reset_name: str = 'aresetn',
                    log=None, instance_name: str = "ReadyCtrl"):
        """
        Initialize ready controller for a specific AXI channel.

        Args:
            dut: DUT object with the signals
            ready_signal_name: Name of ready signal to control (e.g., 'cmd_ready')
            valid_signal_name: Name of valid signal to monitor (e.g., 'cmd_valid')
            clock_name: Name of clock signal
            reset_name: Name of reset signal
            log: Logger instance
            instance_name: Name for logging
        """
        self.dut = dut
        self.ready_signal_name = ready_signal_name
        self.valid_signal_name = valid_signal_name
        self.clock_name = clock_name
        self.reset_name = reset_name
        self.log = log
        self.instance_name = instance_name

        # Get signal references with error checking
        try:
            self.ready_signal = getattr(dut, ready_signal_name)
            self.valid_signal = getattr(dut, valid_signal_name)
            self.clock = getattr(dut, clock_name)
            self.reset = getattr(dut, reset_name)
        except AttributeError as e:
            raise ValueError(f"Signal not found in DUT: {e}")

        # State tracking
        self.current_mode = "immediate"  # immediate, delayed, random
        self.enabled = False
        self.delay_cycles = 0
        self.randomizer = None
        self.randomizer_field = "ready_delay"

        # Statistics and callbacks
        self.handshake_events = []
        self.handshake_callbacks = []
        self.stats = {
            'handshakes': 0,
            'immediate_handshakes': 0,
            'delayed_handshakes': 0,
            'max_delay': 0,
            'total_delay_cycles': 0
        }

        # Control task handle
        self._control_task = None
        self._stop_requested = False

        if self.log:
            self.log.info(f"{instance_name} initialized for {ready_signal_name}/{valid_signal_name}")

    async def start_control(self):
        """Start the ready signal control task"""
        if self._control_task is None:
            self._stop_requested = False
            self._control_task = cocotb.start_soon(self._ready_control_task())

            if self.log:
                self.log.debug(f"{self.instance_name} control task started")

    async def stop_control(self):
        """Stop the ready signal control task"""
        self._stop_requested = True
        if self._control_task:
            self._control_task.kill()
            self._control_task = None

        # De-assert ready
        self.ready_signal.value = 0

        if self.log:
            self.log.debug(f"{self.instance_name} control task stopped")

    async def set_immediate_ready(self, enable: bool = True):
        """
        Set ready to assert immediately (before or with valid).

        Args:
            enable: If True, ready is always asserted. If False, controller disabled.
        """
        self.current_mode = "immediate" if enable else "disabled"
        self.enabled = enable

        if enable:
            self.ready_signal.value = 1
        else:
            self.ready_signal.value = 0

        if self.log:
            status = "enabled" if enable else "disabled"
            self.log.debug(f"{self.instance_name} immediate ready {status}")

    async def set_delayed_ready(self, delay_cycles: int):
        """
        Set ready to assert N cycles after valid.

        Args:
            delay_cycles: Number of clock cycles to wait after valid before asserting ready
        """
        if delay_cycles < 0:
            raise ValueError("Delay cycles must be non-negative")

        self.current_mode = "delayed"
        self.enabled = True
        self.delay_cycles = delay_cycles
        self.ready_signal.value = 0  # Start with ready de-asserted

        if self.log:
            self.log.debug(f"{self.instance_name} delayed ready: {delay_cycles} cycles")

    async def set_random_ready(self, randomizer: FlexRandomizer, field_name: str = "ready_delay"):
        """
        Use FlexRandomizer to generate ready delays.

        Args:
            randomizer: FlexRandomizer instance with delay constraints
            field_name: Field name in randomizer for ready delays
        """
        if field_name not in randomizer.get_field_names():
            raise ValueError(f"Field '{field_name}' not found in randomizer")

        self.current_mode = "random"
        self.enabled = True
        self.randomizer = randomizer
        self.randomizer_field = field_name
        self.ready_signal.value = 0

        if self.log:
            self.log.debug(f"{self.instance_name} random ready using field '{field_name}'")

    def add_handshake_callback(self, callback: Callable[[HandshakeEvent], None]):
        """
        Add callback for handshake events.

        Args:
            callback: Function called with HandshakeEvent when valid/ready both assert
        """
        self.handshake_callbacks.append(callback)

        if self.log:
            self.log.debug(f"{self.instance_name} added handshake callback")

    def remove_handshake_callback(self, callback: Callable):
        """Remove a handshake callback"""
        if callback in self.handshake_callbacks:
            self.handshake_callbacks.remove(callback)

    async def _ready_control_task(self):
        """Main ready signal control task"""
        try:
            while not self._stop_requested:
                # Wait for reset deassertion
                while self.reset.value == 0:
                    await RisingEdge(self.clock)
                    if self._stop_requested:
                        return

                # Wait for valid assertion
                while self.valid_signal.value == 0:
                    await RisingEdge(self.clock)
                    if self._stop_requested:
                        return

                # Valid is now asserted - handle based on current mode
                if not self.enabled:
                    # Controller disabled - wait for next cycle
                    await RisingEdge(self.clock)
                    continue

                valid_timestamp = get_sim_time('ns')
                delay_used = 0
                pattern_info = self.current_mode

                if self.current_mode == "immediate":
                    # Ready should already be asserted
                    if self.ready_signal.value == 0:
                        self.ready_signal.value = 1
                    delay_used = 0

                elif self.current_mode == "delayed":
                    # Wait specified cycles then assert ready
                    for cycle in range(self.delay_cycles):
                        await RisingEdge(self.clock)
                        if self._stop_requested:
                            return
                        if self.valid_signal.value == 0:
                            # Valid deasserted before ready - break
                            break

                    if self.valid_signal.value == 1:  # Still valid
                        self.ready_signal.value = 1
                        delay_used = self.delay_cycles

                elif self.current_mode == "random":
                    # Generate random delay
                    values = self.randomizer.next()
                    random_delay = values[self.randomizer_field]
                    pattern_info = f"random({random_delay})"

                    for cycle in range(random_delay):
                        await RisingEdge(self.clock)
                        if self._stop_requested:
                            return
                        if self.valid_signal.value == 0:
                            break

                    if self.valid_signal.value == 1:
                        self.ready_signal.value = 1
                        delay_used = random_delay

                # Wait for handshake completion or valid deassertion
                if self.valid_signal.value == 1 and self.ready_signal.value == 1:
                    # Handshake occurred
                    handshake_event = HandshakeEvent(valid_timestamp, delay_used, pattern_info)
                    self._record_handshake(handshake_event)

                    # Wait for next clock edge
                    await RisingEdge(self.clock)

                    # De-assert ready for next transaction (unless immediate mode)
                    if self.current_mode != "immediate":
                        self.ready_signal.value = 0

        except Exception as e:
            if self.log:
                self.log.error(f"{self.instance_name} control task error: {e}")
            raise

    def _record_handshake(self, event: HandshakeEvent):
        """Record handshake event and update statistics"""
        self.handshake_events.append(event)

        # Update statistics
        self.stats['handshakes'] += 1
        if event.ready_delay == 0:
            self.stats['immediate_handshakes'] += 1
        else:
            self.stats['delayed_handshakes'] += 1

        self.stats['max_delay'] = max(self.stats['max_delay'], event.ready_delay)
        self.stats['total_delay_cycles'] += event.ready_delay

        # Call callbacks
        for callback in self.handshake_callbacks:
            try:
                callback(event)
            except Exception as e:
                if self.log:
                    self.log.error(f"{self.instance_name} callback error: {e}")

        if self.log:
            self.log.debug(f"{self.instance_name} handshake: {event}")

    def get_statistics(self) -> Dict[str, Any]:
        """Get handshake statistics"""
        stats = self.stats.copy()
        if stats['handshakes'] > 0:
            stats['avg_delay'] = stats['total_delay_cycles'] / stats['handshakes']
        else:
            stats['avg_delay'] = 0.0
        return stats

    def get_recent_handshakes(self, count: int = 10) -> List[HandshakeEvent]:
        """Get most recent handshake events"""
        return self.handshake_events[-count:]

    def clear_statistics(self):
        """Clear statistics and handshake history"""
        self.handshake_events.clear()
        for key in self.stats:
            self.stats[key] = 0

    def __repr__(self):
        return (f"ReadyController({self.ready_signal_name}, mode={self.current_mode}, "
                f"enabled={self.enabled}, handshakes={self.stats['handshakes']})")


# Helper functions for common use cases in the testbench
def create_ready_controllers_for_monitor(dut, is_read: bool, log=None) -> Dict[str, ReadyController]:
    """
    Create ready controllers for AXI monitor interfaces based on read/write mode.

    Args:
        dut: DUT object
        is_read: True for read monitor, False for write monitor
        log: Logger instance

    Returns:
        Dictionary of controller_name -> ReadyController
    """
    controllers = {}

    # CMD ready controller (always needed)
    controllers['cmd_ready'] = ReadyController(
        dut=dut,
        ready_signal_name='cmd_ready',
        valid_signal_name='cmd_valid',
        instance_name='CMD_Ready',
        log=log
    )

    # DATA ready controller (always needed)
    controllers['data_ready'] = ReadyController(
        dut=dut,
        ready_signal_name='data_ready',
        valid_signal_name='data_valid',
        instance_name='DATA_Ready',
        log=log
    )

    # RESP ready controller (only for writes)
    if not is_read:
        controllers['resp_ready'] = ReadyController(
            dut=dut,
            ready_signal_name='resp_ready',
            valid_signal_name='resp_valid',
            instance_name='RESP_Ready',
            log=log
        )

    return controllers


async def setup_all_controllers_immediate(controllers: Dict[str, ReadyController]):
    """Set all controllers to immediate ready mode"""
    for controller in controllers.values():
        await controller.set_immediate_ready(True)


async def setup_all_controllers_delayed(controllers: Dict[str, ReadyController], delay: int):
    """Set all controllers to same delayed ready mode"""
    for controller in controllers.values():
        await controller.set_delayed_ready(delay)


async def start_all_controllers(controllers: Dict[str, ReadyController]):
    """Start all ready controllers"""
    for controller in controllers.values():
        await controller.start_control()


async def stop_all_controllers(controllers: Dict[str, ReadyController]):
    """Stop all ready controllers"""
    for controller in controllers.values():
        await controller.stop_control()


def get_combined_statistics(controllers: Dict[str, ReadyController]) -> Dict[str, Any]:
    """Get combined statistics from all controllers"""
    combined = {
        'total_handshakes': 0,
        'total_immediate': 0,
        'total_delayed': 0,
        'controllers': {}
    }

    for name, controller in controllers.items():
        stats = controller.get_statistics()
        combined['total_handshakes'] += stats['handshakes']
        combined['total_immediate'] += stats['immediate_handshakes']
        combined['total_delayed'] += stats['delayed_handshakes']
        combined['controllers'][name] = stats

    return combined


# Example usage for the final testbench
def demo_usage_in_testbench():
    """
    Example of how to use ReadyController in the final testbench.
    This is just documentation - not actual runnable code.
    """

    # In testbench __init__:
    # self.ready_controllers = create_ready_controllers_for_monitor(dut, self.IS_READ, log)

    # In setup_clocks_and_reset():
    # await start_all_controllers(self.ready_controllers)
    # await setup_all_controllers_immediate(self.ready_controllers)

    # In setup_ready_profile():
    # if profile == 'immediate':
    #     await setup_all_controllers_immediate(self.ready_controllers)
    # elif profile == 'delayed':
    #     await setup_all_controllers_delayed(self.ready_controllers, 5)
    # else:
    #     # Use FlexRandomizer
    #     randomizer = create_randomizer_for_profile(profile)
    #     for controller in self.ready_controllers.values():
    #         await controller.set_random_ready(randomizer, 'ready_delay')

    # In shutdown():
    # await stop_all_controllers(self.ready_controllers)

    # In get_ready_statistics():
    # return get_combined_statistics(self.ready_controllers)

    pass
