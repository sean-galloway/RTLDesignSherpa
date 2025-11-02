# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AxiClockGateCtrl
# Purpose: Enhanced Generic AXI Clock Gate Controller
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Enhanced Generic AXI Clock Gate Controller

This module provides a flexible class for controlling AXI clock gating
with support for configurable signal names and multiple clock domains.
"""

import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from CocoTBFramework.tbclasses.shared.tbbase import TBBase


class AxiClockGateCtrl(TBBase):
    """
    Enhanced AXI Clock Gate Controller class.

    Controls clock gating based on activity from multiple valid signals
    with configurable signal names for different clock domains.
    """

    def __init__(self, dut, instance_path="", clock_signal_name="clk_in",
                    user_valid_signals=None, axi_valid_signals=None,
                    gating_signal_name="gating", idle_signal_name="idle",
                    enable_signal_name="cfg_cg_enable", idle_count_signal_name="cfg_cg_idle_count"):
        """
        Initialize the AXI Clock Gate Controller.

        Args:
            dut: Device under test
            instance_path: Path to the clock gate controller instance (e.g., "amba_clock_gate_ctrl")
            clock_signal_name: Name of the clock signal
            user_valid_signals: List of user-side valid signal names
            axi_valid_signals: List of AXI-side valid signal names
            gating_signal_name: Name of the gating status signal (e.g., "pclk_cg_gating")
            idle_signal_name: Name of the idle status signal (e.g., "pclk_cg_idle")
            enable_signal_name: Name of the clock gating enable signal
            idle_count_signal_name: Name of the idle count configuration signal
        """
        super().__init__(dut)

        # Store parameters
        self.dut = dut
        self.instance_path = instance_path
        self.clock_signal_name = clock_signal_name
        self.gating_signal_name = gating_signal_name
        self.idle_signal_name = idle_signal_name
        self.enable_signal_name = enable_signal_name
        self.idle_count_signal_name = idle_count_signal_name

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

        # Signal objects for direct access
        self.clock_signal = None
        self.gating_signal = None
        self.idle_signal = None
        self.enable_signal = None
        self.idle_count_signal = None

        self._cache_control_signals()

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

    def _cache_control_signals(self):
        """Cache frequently accessed control signals for performance."""
        # Clock signal
        clock_path = f"{self.instance_path}.{self.clock_signal_name}" if self.instance_path else self.clock_signal_name
        self.clock_signal = self._get_signal(clock_path)

        # Gating status signal
        gating_path = f"{self.instance_path}.{self.gating_signal_name}" if self.instance_path else self.gating_signal_name
        self.gating_signal = self._get_signal(gating_path)

        # Idle status signal
        idle_path = f"{self.instance_path}.{self.idle_signal_name}" if self.instance_path else self.idle_signal_name
        self.idle_signal = self._get_signal(idle_path)

        # Enable control signal
        enable_path = f"{self.instance_path}.{self.enable_signal_name}" if self.instance_path else self.enable_signal_name
        self.enable_signal = self._get_signal(enable_path)

        # Idle count control signal
        idle_count_path = f"{self.instance_path}.{self.idle_count_signal_name}" if self.instance_path else self.idle_count_signal_name
        self.idle_count_signal = self._get_signal(idle_count_path)

        # Log which signals were found
        signals_found = []
        if self.clock_signal: signals_found.append(f"clock({self.clock_signal_name})")
        if self.gating_signal: signals_found.append(f"gating({self.gating_signal_name})")
        if self.idle_signal: signals_found.append(f"idle({self.idle_signal_name})")
        if self.enable_signal: signals_found.append(f"enable({self.enable_signal_name})")
        if self.idle_count_signal: signals_found.append(f"idle_count({self.idle_count_signal_name})")

        self.log.info(f"Cached control signals: {', '.join(signals_found)}")

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
                self.log.debug(f"Signal part not found: {part} in path {signal_path}")
                return None

        return current

    def enable_clock_gating(self, enable=True):
        """
        Enable or disable clock gating.

        Args:
            enable: True to enable clock gating, False to disable
        """
        if self.enable_signal:
            self.enable_signal.value = 1 if enable else 0
            self.is_enabled = enable
            self.log.info(f"Clock gating {'enabled' if enable else 'disabled'} via {self.enable_signal_name}")
        else:
            self.log.error(f"Clock gating enable signal not found: {self.enable_signal_name}")

    def set_idle_count(self, count):
        """
        Set the idle count threshold for clock gating.

        Args:
            count: Number of idle cycles before clock gating is activated
        """
        if self.idle_count_signal:
            self.idle_count_signal.value = count
            self.idle_count = count
            self.log.info(f"Idle count set to {count} via {self.idle_count_signal_name}")
        else:
            self.log.error(f"Idle count signal not found: {self.idle_count_signal_name}")

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

        if not self.clock_signal:
            self.log.error(f"Clock signal not found: {self.clock_signal_name}")
            return stats

        while cocotb.utils.get_sim_time(units) < end_time:
            # Wait for clock edge
            await RisingEdge(self.clock_signal)

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
            if self.gating_signal and self.gating_signal.value == 1:
                stats['gated_cycles'] += 1
                self.is_gated = True
            else:
                self.is_gated = False

            # Track idle state if signal available
            if self.idle_signal:
                self.is_idle = (self.idle_signal.value == 1)

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
        if self.gating_signal:
            self.is_gated = bool(self.gating_signal.value)

        if self.idle_signal:
            self.is_idle = bool(self.idle_signal.value)

        return {
            'enabled': self.is_enabled,
            'idle_count': self.idle_count,
            'is_gated': self.is_gated,
            'is_idle': self.is_idle,
            'domain': self.instance_path or 'top_level',
            'gating_signal': self.gating_signal_name,
            'idle_signal': self.idle_signal_name
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

        self.log.info(f"Forced wakeup by asserting all user valid signals in {self.instance_path or 'top_level'}")
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

        self.log.info(f"Restored signals to original values in {self.instance_path or 'top_level'}")

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

        if not self.idle_signal:
            self.log.error(f"Idle signal not found: {self.idle_signal_name}")
            return False

        if not self.clock_signal:
            self.log.error(f"Clock signal not found: {self.clock_signal_name}")
            return False

        while cocotb.utils.get_sim_time(units) < end_time:
            # Check if already idle
            if self.idle_signal.value == 1:
                self.is_idle = True
                self.log.info(f"Idle state reached in {self.instance_path or 'top_level'}")
                return True

            # Wait for next clock
            await RisingEdge(self.clock_signal)

        self.log.warning(f"Timeout waiting for idle state ({timeout} {units}) in {self.instance_path or 'top_level'}")
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

        if not self.gating_signal:
            self.log.error(f"Gating signal not found: {self.gating_signal_name}")
            return False

        if not self.clock_signal:
            self.log.error(f"Clock signal not found: {self.clock_signal_name}")
            return False

        while cocotb.utils.get_sim_time(units) < end_time:
            # Check if already gated
            if self.gating_signal.value == 1:
                self.is_gated = True
                self.log.info(f"Gated state reached in {self.instance_path or 'top_level'}")
                return True

            # Wait for next clock
            await RisingEdge(self.clock_signal)

        self.log.warning(f"Timeout waiting for gated state ({timeout} {units}) in {self.instance_path or 'top_level'}")
        return False


class MultiDomainClockGateCtrl:
    """
    Multi-domain clock gating controller that manages multiple AxiClockGateCtrl instances
    for different clock domains (e.g., PCLK and ACLK).
    """

    def __init__(self, controllers=None):
        """
        Initialize multi-domain clock gate controller.

        Args:
            controllers: Dict of domain_name -> AxiClockGateCtrl instances
        """
        self.controllers = controllers or {}
        self.log = None

        # Set up logging from first controller
        if self.controllers:
            first_ctrl = next(iter(self.controllers.values()))
            self.log = first_ctrl.log

    def add_controller(self, domain_name, controller):
        """Add a clock gate controller for a specific domain."""
        self.controllers[domain_name] = controller
        if self.log is None:
            self.log = controller.log

    def enable_all_clock_gating(self, enable=True):
        """Enable/disable clock gating for all domains."""
        for domain, ctrl in self.controllers.items():
            ctrl.enable_clock_gating(enable)

    def set_all_idle_counts(self, idle_count):
        """Set idle count for all domains."""
        for domain, ctrl in self.controllers.items():
            ctrl.set_idle_count(idle_count)

    async def monitor_all_activity(self, duration=1000, units='ns'):
        """Monitor activity across all domains."""
        # Start monitoring tasks for all domains
        tasks = {}
        for domain, ctrl in self.controllers.items():
            task = cocotb.start_soon(ctrl.monitor_activity(duration, units))
            tasks[domain] = task

        # Collect results
        results = {}
        for domain, task in tasks.items():
            results[domain] = await task

        return results

    def get_all_states(self):
        """Get current state of all controllers."""
        states = {}
        for domain, ctrl in self.controllers.items():
            states[domain] = ctrl.get_current_state()
        return states

    async def wait_for_all_idle(self, timeout=1000, units='ns'):
        """Wait for all domains to reach idle state."""
        tasks = {}
        for domain, ctrl in self.controllers.items():
            task = cocotb.start_soon(ctrl.wait_for_idle(timeout, units))
            tasks[domain] = task

        results = {}
        for domain, task in tasks.items():
            results[domain] = await task

        all_idle = all(results.values())
        if self.log:
            if all_idle:
                self.log.info("All domains reached idle state")
            else:
                failed_domains = [d for d, r in results.items() if not r]
                self.log.warning(f"Failed to reach idle in domains: {failed_domains}")

        return all_idle

    async def wait_for_all_gating(self, timeout=1000, units='ns'):
        """Wait for all domains to reach gated state."""
        tasks = {}
        for domain, ctrl in self.controllers.items():
            task = cocotb.start_soon(ctrl.wait_for_gating(timeout, units))
            tasks[domain] = task

        results = {}
        for domain, task in tasks.items():
            results[domain] = await task

        all_gated = all(results.values())
        if self.log:
            if all_gated:
                self.log.info("All domains reached gated state")
            else:
                failed_domains = [d for d, r in results.items() if not r]
                self.log.warning(f"Failed to reach gated state in domains: {failed_domains}")

        return all_gated


# Example usage for CDC testbench:
"""
# Create controllers for both domains
pclk_cg_ctrl = AxiClockGateCtrl(
    dut,
    instance_path="pclk_gate_ctrl",
    clock_signal_name="pclk",
    user_valid_signals=["s_apb_PSEL", "w_rsp_valid"],
    axi_valid_signals=["w_cmd_valid"],
    gating_signal_name="pclk_cg_gating",
    idle_signal_name="pclk_cg_idle"
)

aclk_cg_ctrl = AxiClockGateCtrl(
    dut,
    instance_path="aclk_gate_ctrl",
    clock_signal_name="aclk",
    user_valid_signals=["rsp_valid"],
    axi_valid_signals=["cmd_valid", "cmd_ready"],
    gating_signal_name="aclk_cg_gating",
    idle_signal_name="aclk_cg_idle"
)

# Create multi-domain controller
multi_cg = MultiDomainClockGateCtrl({
    'pclk': pclk_cg_ctrl,
    'aclk': aclk_cg_ctrl
})

# Configure all domains
multi_cg.enable_all_clock_gating(True)
multi_cg.set_all_idle_counts(8)

# Monitor activity across domains
stats = await multi_cg.monitor_all_activity(1000, 'ns')
print(f"PCLK: {stats['pclk']['gated_percent']:.1f}% gated")
print(f"ACLK: {stats['aclk']['gated_percent']:.1f}% gated")

# Wait for all domains to reach gated state
all_gated = await multi_cg.wait_for_all_gating(2000, 'ns')
"""