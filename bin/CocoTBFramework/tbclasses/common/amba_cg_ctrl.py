"""
Generic AXI Clock Gate Controller

This module provides a generic class for controlling AXI clock gating
with support for multiple valid signals from both user and interface sides.
"""

import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from CocoTBFramework.tbclasses.misc.tbbase import TBBase


class AxiClockGateCtrl(TBBase):
    """
    Generic AXI Clock Gate Controller class.

    Controls clock gating based on activity from multiple valid signals
    on both user and AXI interface sides.
    """

    def __init__(self, dut, instance_path="", clock_signal_name="clk_in", user_valid_signals=None, axi_valid_signals=None):
        """
        Initialize the AXI Clock Gate Controller.

        Args:
            dut: Device under test
            instance_path: Path to the clock gate controller instance (e.g., "i_amba_clock_gate_ctrl")
            clock_signal_name: Name of the clock signal
            user_valid_signals: List of user-side valid signal names
            axi_valid_signals: List of AXI-side valid signal names
        """
        super().__init__(dut)

        # Store parameters
        self.dut = dut
        self.instance_path = instance_path
        self.clock_signal_name = clock_signal_name

        # Default empty lists if not provided
        self.user_valid_signals = user_valid_signals or []
        self.axi_valid_signals = axi_valid_signals or []

        # Store the full paths to the user and AXI valid signals
        self.user_valid_paths = []
        self.axi_valid_paths = []

        # Register signal paths
        self._register_signals()

        # Track current state
        self.is_enabled = False
        self.idle_count = 0
        self.is_gated = False
        self.is_idle = False

    def _register_signals(self):
        """Register all signal paths for user and AXI valid signals."""
        # Process user valid signals
        for signal_name in self.user_valid_signals:
            signal_path = f"{self.instance_path}.{signal_name}" if self.instance_path else signal_name
            if signal := self._get_signal(signal_path):
                self.user_valid_paths.append(signal)
            else:
                self.log.warning(f"User valid signal not found: {signal_path}")

        # Process AXI valid signals
        for signal_name in self.axi_valid_signals:
            signal_path = f"{self.instance_path}.{signal_name}" if self.instance_path else signal_name
            if signal := self._get_signal(signal_path):
                self.axi_valid_paths.append(signal)
            else:
                self.log.warning(f"AXI valid signal not found: {signal_path}")

        self.log.info(f"Registered {len(self.user_valid_paths)} user valid signals and {len(self.axi_valid_paths)} AXI valid signals")

    def _get_signal(self, signal_path):
        """
        Helper to get a signal by hierarchical path.

        Args:
            signal_path: Path to the signal, can include dots for hierarchy

        Returns:
            Signal object or None if not found
        """
        # Handle hierarchical paths
        parts = signal_path.split('.')
        current = self.dut

        for part in parts:
            if hasattr(current, part):
                current = getattr(current, part)
            else:
                self.log.warning(f"Signal part not found: {part} in path {signal_path}")
                return None

        return current

    def enable_clock_gating(self, enable=True):
        """
        Enable or disable clock gating.

        Args:
            enable: True to enable clock gating, False to disable
        """
        # signal_path = f"{self.instance_path}.i_cfg_cg_enable" if self.instance_path else "i_cfg_cg_enable"
        signal_path = "i_cfg_cg_enable"
        if signal := self._get_signal(signal_path):
            signal.value = 1 if enable else 0
            self.is_enabled = enable
            self.log.info(f"Clock gating {'enabled' if enable else 'disabled'}")
        else:
            self.log.error(f"Clock gating enable signal not found: {signal_path}")

    def set_idle_count(self, count):
        """
        Set the idle count threshold for clock gating.

        Args:
            count: Number of idle cycles before clock gating is activated
        """
        # signal_path = f"{self.instance_path}.i_cfg_cg_idle_count" if self.instance_path else "i_cfg_cg_idle_count"
        signal_path = "i_cfg_cg_idle_count"
        if signal := self._get_signal(signal_path):
            signal.value = count
            self.idle_count = count
            self.log.info(f"Idle count set to {count}")
        else:
            self.log.error(f"Idle count signal not found: {signal_path}")

    async def monitor_activity(self, duration=1000, units='ns'):
        """
        Monitor activity on valid signals for a specified duration.

        Args:
            duration: Duration to monitor
            units: Time units for duration

        Returns:
            Dict with activity statistics
        """
        # Initialize statistics
        stats = {
            'total_cycles': 0,
            'active_cycles': 0,
            'gated_cycles': 0,
            'user_active_cycles': 0,
            'axi_active_cycles': 0
        }

        start_time = cocotb.utils.get_sim_time(units)
        end_time = start_time + duration

        # Get clock signal
        clock_signal_path = f"{self.instance_path}.{self.clock_signal_name}" if self.instance_path else self.clock_signal_name
        clock_signal = self._get_signal(clock_signal_path)

        if not clock_signal:
            self.log.error(f"Clock signal not found: {clock_signal_path}")
            return stats

        # Get gating and idle indicators if available
        gating_signal_path = f"{self.instance_path}.o_gating" if self.instance_path else "o_gating"
        gating_signal = self._get_signal(gating_signal_path)

        idle_signal_path = f"{self.instance_path}.o_idle" if self.instance_path else "o_idle"
        idle_signal = self._get_signal(idle_signal_path)

        while cocotb.utils.get_sim_time(units) < end_time:
            # Wait for clock edge
            await RisingEdge(clock_signal)

            # Increment total cycles
            stats['total_cycles'] += 1

            # Check user valid signals
            user_active = any(signal.value == 1 for signal in self.user_valid_paths if hasattr(signal, 'value'))
            if user_active:
                stats['user_active_cycles'] += 1

            # Check AXI valid signals
            axi_active = any(signal.value == 1 for signal in self.axi_valid_paths if hasattr(signal, 'value'))
            if axi_active:
                stats['axi_active_cycles'] += 1

            # Overall activity
            if user_active or axi_active:
                stats['active_cycles'] += 1

            # Track gating if signal available
            if gating_signal and gating_signal.value == 1:
                stats['gated_cycles'] += 1
                self.is_gated = True
            else:
                self.is_gated = False

            # Track idle state if signal available
            if idle_signal:
                self.is_idle = (idle_signal.value == 1)

        # Calculate percentages
        if stats['total_cycles'] > 0:
            stats['active_percent'] = (stats['active_cycles'] / stats['total_cycles']) * 100
            stats['gated_percent'] = (stats['gated_cycles'] / stats['total_cycles']) * 100
            stats['user_active_percent'] = (stats['user_active_cycles'] / stats['total_cycles']) * 100
            stats['axi_active_percent'] = (stats['axi_active_cycles'] / stats['total_cycles']) * 100

        self.log.info(f"Activity monitoring complete: {stats['active_percent']:.1f}% active, {stats['gated_percent']:.1f}% gated")
        return stats

    def get_current_state(self):
        """
        Get the current state of the clock gate controller.

        Returns:
            Dict with current state information
        """
        # Update gating and idle state from signals if available
        gating_signal_path = f"{self.instance_path}.o_gating" if self.instance_path else "o_gating"
        gating_signal = self._get_signal(gating_signal_path)

        idle_signal_path = f"{self.instance_path}.o_idle" if self.instance_path else "o_idle"
        idle_signal = self._get_signal(idle_signal_path)

        if gating_signal:
            self.is_gated = bool(gating_signal.value)

        if idle_signal:
            self.is_idle = bool(idle_signal.value)

        return {
            'enabled': self.is_enabled,
            'idle_count': self.idle_count,
            'is_gated': self.is_gated,
            'is_idle': self.is_idle
        }

    def force_wakeup(self):
        """
        Force a wakeup by temporarily asserting all user valid signals.
        This is useful for testing or ensuring the clock is active.
        """
        # Store original values
        original_values = {}
        for signal_name, signal in zip(self.user_valid_signals, self.user_valid_paths):
            if hasattr(signal, 'value'):
                original_values[signal_name] = signal.value
                signal.value = 1

        self.log.info("Forced wakeup by asserting all user valid signals")
        return original_values

    def restore_signals(self, original_values):
        """
        Restore signals to their original values after a forced wakeup.

        Args:
            original_values: Dict mapping signal names to their original values
        """
        for signal_name, signal in zip(self.user_valid_signals, self.user_valid_paths):
            if signal_name in original_values and hasattr(signal, 'value'):
                signal.value = original_values[signal_name]

        self.log.info("Restored signals to original values")

    async def wait_for_idle(self, timeout=1000, units='ns'):
        """
        Wait for the controller to enter idle state.

        Args:
            timeout: Maximum time to wait
            units: Time units for timeout

        Returns:
            True if idle state was reached, False if timeout
        """
        start_time = cocotb.utils.get_sim_time(units)
        end_time = start_time + timeout

        # Get idle signal
        idle_signal_path = f"{self.instance_path}.o_idle" if self.instance_path else "o_idle"
        idle_signal = self._get_signal(idle_signal_path)

        if not idle_signal:
            self.log.error(f"Idle signal not found: {idle_signal_path}")
            return False

        # Get clock signal for waiting
        clock_signal_path = f"{self.instance_path}.{self.clock_signal_name}" if self.instance_path else self.clock_signal_name
        clock_signal = self._get_signal(clock_signal_path)

        while cocotb.utils.get_sim_time(units) < end_time:
            # Check if already idle
            if idle_signal.value == 1:
                self.is_idle = True
                self.log.info("Idle state reached")
                return True

            # Wait for next clock
            await RisingEdge(clock_signal)

        self.log.warning(f"Timeout waiting for idle state ({timeout} {units})")
        return False

    async def wait_for_gating(self, timeout=1000, units='ns'):
        """
        Wait for the controller to enter gated state.

        Args:
            timeout: Maximum time to wait
            units: Time units for timeout

        Returns:
            True if gated state was reached, False if timeout
        """
        start_time = cocotb.utils.get_sim_time(units)
        end_time = start_time + timeout

        # Get gating signal
        gating_signal_path = f"{self.instance_path}.o_gating" if self.instance_path else "o_gating"
        gating_signal = self._get_signal(gating_signal_path)

        if not gating_signal:
            self.log.error(f"Gating signal not found: {gating_signal_path}")
            return False

        # Get clock signal for waiting
        clock_signal_path = f"{self.instance_path}.{self.clock_signal_name}" if self.instance_path else self.clock_signal_name
        clock_signal = self._get_signal(clock_signal_path)

        while cocotb.utils.get_sim_time(units) < end_time:
            # Check if already gated
            if gating_signal.value == 1:
                self.is_gated = True
                self.log.info("Gated state reached")
                return True

            # Wait for next clock
            await RisingEdge(clock_signal)

        self.log.warning(f"Timeout waiting for gated state ({timeout} {units})")
        return False

# # Create with multiple valid signals from both sides
# clock_gate = AxiClockGateCtrl(
#     dut,
#     clock_gate_prefix="cg_",
#     user_valid_signals=["s_axi_arvalid", "s_axi_rvalid"]
#     axi_valid_signals=["m_axi_arvalid", "m_axi_rvalid"]
# )

# # Configure
# clock_gate.enable_clock_gating(True)
# clock_gate.set_idle_count(8)

# # Monitor activity
# stats = await clock_gate.monitor_activity(1000, 'ns')
# print(f"Active: {stats['active_percent']}%, Gated: {stats['gated_percent']}%")
