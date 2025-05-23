"""
Enhanced centralized controller for AXI ready signals.

This module provides an enhanced ReadySignalController class that serves as a
single point of control for all ready signals in the AXI interface, with special
handling for the o_block_ready signal and timing control features.
"""

import cocotb
from cocotb.triggers import RisingEdge, Edge, Timer


class ReadySignalController:
    """
    Enhanced centralized controller for AXI ready signals.

    This class provides a single point of control for all ready signals in the AXI interface.
    It handles special conditions like o_block_ready assertion and provides timing control
    for ready signal delays.

    Key features:
    - Single point of control for all ready signals
    - Automatic handling of o_block_ready to i_addr_ready relationship
    - Methods for forcing ready signals low for specific durations
    - Event tracking and logging
    """

    def __init__(self, dut, log=None):
        """
        Initialize the controller with the DUT and optional logger

        Args:
            dut: Device under test
            log: Optional logger for event tracking
        """
        self.dut = dut
        self.log = log

        # Default ready states (typically asserted for good throughput)
        self.default_i_addr_ready = 1
        self.default_i_data_ready = 1
        self.default_i_resp_ready = 1

        # Current states
        self.i_addr_ready_forced_low = False
        self.i_data_ready_forced_low = False
        self.i_resp_ready_forced_low = False

        # Block ready state
        self.block_ready_asserted = False

        # Monitor tasks
        self.monitor_tasks = []
        self.delay_tasks = {}

        # Events for tracking
        self.block_ready_events = []

    async def start(self):
        """
        Start the controller and monitoring tasks

        This initiates monitoring of the o_block_ready signal and applies
        initial ready signal values.
        """
        # First stop any existing monitors to avoid duplicates
        await self.stop()

        # Start block_ready monitor
        task = cocotb.start_soon(self._monitor_block_ready())
        self.monitor_tasks.append(task)

        # Apply initial values
        self.apply_ready_values()

        if self.log:
            self.log.debug("Ready signal controller started")

    def clear_block_ready_events(self):
        """
        Clear the history of block_ready events
        """
        self.block_ready_events = []
        if self.log:
            self.log.debug(f"Cleared block_ready event history @ {cocotb.utils.get_sim_time('ns')}ns")

    async def stop(self):
        """
        Stop all monitoring tasks

        This cleanly terminates all monitoring tasks started by the controller.
        """
        for task in self.monitor_tasks:
            task.kill()
        self.monitor_tasks = []

        # Kill any active delay tasks
        for task_id, task in self.delay_tasks.items():
            task.kill()
        self.delay_tasks = {}

        if self.log:
            self.log.debug("Ready signal controller stopped")

    def apply_ready_values(self):
        """
        Apply the current ready values to the DUT signals

        This applies the current state of all ready signals, taking into account
        forced values and the block_ready state.
        """
        # For address channel ready (i_addr_ready)
        # Special case: i_addr_ready is forced low by o_block_ready
        if self.block_ready_asserted or self.i_addr_ready_forced_low:
            self.dut.i_addr_ready.value = 0
        else:
            self.dut.i_addr_ready.value = self.default_i_addr_ready

        # For other ready signals
        if not self.i_data_ready_forced_low:
            self.dut.i_data_ready.value = self.default_i_data_ready

        if not self.i_resp_ready_forced_low:
            self.dut.i_resp_ready.value = self.default_i_resp_ready

    async def _monitor_block_ready(self):
        """
        Monitor o_block_ready and control i_addr_ready accordingly

        This is the core functionality that ensures i_addr_ready is deasserted
        whenever o_block_ready is asserted.
        """
        try:
            while True:
                # Wait for o_block_ready to change
                await Edge(self.dut.o_block_ready)

                # Record block_ready events
                current_time = cocotb.utils.get_sim_time('ns')
                event = {
                    'time': current_time,
                    'value': self.dut.o_block_ready.value
                }
                self.block_ready_events.append(event)

                if self.log:
                    self.log.info(f"o_block_ready changed to {self.dut.o_block_ready.value} @ {current_time}ns")

                # Update block_ready state
                self.block_ready_asserted = bool(self.dut.o_block_ready.value)

                if self.dut.o_block_ready.value:
                    # o_block_ready asserted, must force i_addr_ready low
                    self.dut.i_addr_ready.value = 0
                elif not self.i_addr_ready_forced_low:
                    self.dut.i_addr_ready.value = self.default_i_addr_ready

        except Exception as e:
            if self.log:
                self.log.error(f"Error in block_ready monitor: {str(e)}")

    def set_addr_ready(self, value):
        """
        Set the address channel ready signal (i_addr_ready)

        Args:
            value: Value to set (0 or 1)
        """
        self.default_i_addr_ready = value
        # Only apply if not forced low and not blocked
        if not self.i_addr_ready_forced_low and not self.block_ready_asserted:
            self.dut.i_addr_ready.value = value

    def set_data_ready(self, value):
        """
        Set the data channel ready signal (i_data_ready)

        Args:
            value: Value to set (0 or 1)
        """
        self.default_i_data_ready = value
        if not self.i_data_ready_forced_low:
            self.dut.i_data_ready.value = value

    def set_resp_ready(self, value):
        """
        Set the response channel ready signal (i_resp_ready)

        Args:
            value: Value to set (0 or 1)
        """
        self.default_i_resp_ready = value
        if not self.i_resp_ready_forced_low:
            self.dut.i_resp_ready.value = value

    def force_addr_ready_low(self, forced=True):
        """
        Force the address ready signal low regardless of default state

        Args:
            forced: True to force low, False to restore default
        """
        self.i_addr_ready_forced_low = forced
        if forced:
            self.dut.i_addr_ready.value = 0
        elif not self.block_ready_asserted:
            self.dut.i_addr_ready.value = self.default_i_addr_ready

    def force_data_ready_low(self, forced=True):
        """
        Force the data ready signal low regardless of default state

        Args:
            forced: True to force low, False to restore default
        """
        self.i_data_ready_forced_low = forced
        self.dut.i_data_ready.value = 0 if forced else self.default_i_data_ready

    def force_resp_ready_low(self, forced=True):
        """
        Force the response ready signal low regardless of default state

        Args:
            forced: True to force low, False to restore default
        """
        self.i_resp_ready_forced_low = forced
        self.dut.i_resp_ready.value = 0 if forced else self.default_i_resp_ready

    async def delay_addr_ready(self, cycles):
        """
        Delay address ready signal by specific number of clock cycles

        This forces the address ready signal low for the specified number of cycles
        and then automatically restores it.

        Args:
            cycles: Number of clock cycles to delay ready signal

        Returns:
            Task ID for tracking
        """
        task_id = f"addr_ready_{cocotb.utils.get_sim_time('ns')}"

        # Force ready low
        self.force_addr_ready_low(True)

        if self.log:
            self.log.debug(f"Delaying addr_ready for {cycles} cycles @ {cocotb.utils.get_sim_time('ns')}ns")

        # Create delay task
        async def _delay_task():
            # Wait for specified cycles
            for _ in range(cycles):
                await RisingEdge(self.dut.aclk)

            # Release the forced-low state if still in this delay
            if self.delay_tasks.get(task_id) is not None:
                self.force_addr_ready_low(False)
                if self.log:
                    self.log.debug(f"Released addr_ready after {cycles} cycles @ {cocotb.utils.get_sim_time('ns')}ns")

                # Remove task from tracking
                if task_id in self.delay_tasks:
                    del self.delay_tasks[task_id]

        # Start and track the task
        self.delay_tasks[task_id] = cocotb.start_soon(_delay_task())
        return task_id

    async def delay_data_ready(self, cycles):
        """
        Delay data ready signal by specific number of clock cycles

        This forces the data ready signal low for the specified number of cycles
        and then automatically restores it.

        Args:
            cycles: Number of clock cycles to delay ready signal

        Returns:
            Task ID for tracking
        """
        task_id = f"data_ready_{cocotb.utils.get_sim_time('ns')}"

        # Force ready low
        self.force_data_ready_low(True)

        if self.log:
            self.log.debug(f"Delaying data_ready for {cycles} cycles @ {cocotb.utils.get_sim_time('ns')}ns")

        # Create delay task
        async def _delay_task():
            # Wait for specified cycles
            for _ in range(cycles):
                await RisingEdge(self.dut.aclk)

            # Release the forced-low state if still in this delay
            if self.delay_tasks.get(task_id) is not None:
                self.force_data_ready_low(False)
                if self.log:
                    self.log.debug(f"Released data_ready after {cycles} cycles @ {cocotb.utils.get_sim_time('ns')}ns")

                # Remove task from tracking
                if task_id in self.delay_tasks:
                    del self.delay_tasks[task_id]

        # Start and track the task
        self.delay_tasks[task_id] = cocotb.start_soon(_delay_task())
        return task_id

    async def delay_resp_ready(self, cycles):
        """
        Delay response ready signal by specific number of clock cycles

        This forces the response ready signal low for the specified number of cycles
        and then automatically restores it.

        Args:
            cycles: Number of clock cycles to delay ready signal

        Returns:
            Task ID for tracking
        """
        task_id = f"resp_ready_{cocotb.utils.get_sim_time('ns')}"

        # Force ready low
        self.force_resp_ready_low(True)

        if self.log:
            self.log.debug(f"Delaying resp_ready for {cycles} cycles @ {cocotb.utils.get_sim_time('ns')}ns")

        # Create delay task
        async def _delay_task():
            # Wait for specified cycles
            for _ in range(cycles):
                await RisingEdge(self.dut.aclk)

            # Release the forced-low state if still in this delay
            if self.delay_tasks.get(task_id) is not None:
                self.force_resp_ready_low(False)
                if self.log:
                    self.log.debug(f"Released resp_ready after {cycles} cycles @ {cocotb.utils.get_sim_time('ns')}ns")

                # Remove task from tracking
                if task_id in self.delay_tasks:
                    del self.delay_tasks[task_id]

        # Start and track the task
        self.delay_tasks[task_id] = cocotb.start_soon(_delay_task())
        return task_id

    def cancel_delay(self, task_id):
        """
        Cancel a previously scheduled ready signal delay

        Args:
            task_id: Task ID returned from delay_* method

        Returns:
            True if task was found and cancelled, False otherwise
        """
        if task_id not in self.delay_tasks:
            return False
        self.delay_tasks[task_id].kill()
        del self.delay_tasks[task_id]

        # Determine which ready signal to restore based on task ID prefix
        if task_id.startswith("addr_ready_"):
            self.force_addr_ready_low(False)
        elif task_id.startswith("data_ready_"):
            self.force_data_ready_low(False)
        elif task_id.startswith("resp_ready_"):
            self.force_resp_ready_low(False)

        if self.log:
            self.log.debug(f"Cancelled delay task {task_id} @ {cocotb.utils.get_sim_time('ns')}ns")

        return True

    def get_block_ready_state(self):
        """
        Get current state of block_ready signal

        Returns:
            True if block_ready is asserted, False otherwise
        """
        return self.block_ready_asserted

    def get_block_ready_events(self):
        """
        Get list of block_ready events

        Returns:
            List of events, each with 'time' and 'value' keys
        """
        return self.block_ready_events
