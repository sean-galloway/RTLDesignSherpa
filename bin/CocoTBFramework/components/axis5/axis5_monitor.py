# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXIS5Monitor
# Purpose: AXIS5 Monitor - Stream protocol monitor with AMBA5 extensions
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-21

"""
AXIS5 Monitor - Stream protocol monitor with AMBA5 extensions

This module provides AXIS5 Monitor functionality with:
- TWAKEUP: Wake-up signaling observation
- TPARITY: Data parity verification
"""

import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.utils import get_sim_time

from ..axis4.axis_monitor import AXISMonitor
from .axis5_packet import AXIS5Packet
from .axis5_field_configs import AXIS5FieldConfigs


class AXIS5Monitor(AXISMonitor):
    """
    AXIS5 Monitor component for observing AXI5-Stream protocol.

    Extends AXISMonitor with AMBA5-specific features:
    - Wake-up signaling observation (TWAKEUP)
    - Parity verification (TPARITY)
    - Extended protocol violation checking
    """

    def __init__(self, dut, title, prefix, clock, field_config=None,
                 is_slave=False, mode='skid',
                 bus_name='', pkt_prefix='', multi_sig=False,
                 log=None, super_debug=False, signal_map=None,
                 enable_wakeup=True, enable_parity=False, **kwargs):
        """
        Initialize AXIS5 Monitor.

        Args:
            dut: Device under test
            title: Component title/name
            prefix: Bus prefix (e.g., "s_axis5_", "m_axis5_", "axis5_")
            clock: Clock signal
            field_config: Field configuration (if None, creates default)
            is_slave: True if monitoring slave side, False for master side
            mode: Protocol mode ('skid', 'blocking', etc.)
            bus_name: Bus/channel name
            pkt_prefix: Packet field prefix
            multi_sig: Whether using multi-signal mode
            log: Logger instance
            super_debug: Enable detailed debugging
            signal_map: Optional manual signal mapping
            enable_wakeup: Enable TWAKEUP observation
            enable_parity: Enable TPARITY verification
            **kwargs: Additional configuration
        """
        # Store AXIS5 configuration before super().__init__
        self.enable_wakeup = enable_wakeup
        self.enable_parity = enable_parity

        # Create AXIS5 field config if none provided
        if field_config is None:
            field_config = AXIS5FieldConfigs.create_axis5_field_config(
                enable_wakeup=enable_wakeup,
                enable_parity=enable_parity
            )

        # Initialize parent
        super().__init__(
            dut=dut, title=title, prefix=prefix, clock=clock,
            field_config=field_config, is_slave=is_slave,
            mode=mode, bus_name=bus_name, pkt_prefix=pkt_prefix,
            multi_sig=multi_sig, log=log, super_debug=super_debug,
            signal_map=signal_map, **kwargs
        )

        # AXIS5 state
        self._wakeup_active = False
        self._wakeup_history = []

        # AXIS5 statistics
        self.wakeup_events = 0
        self.wakeup_violations = 0
        self.parity_errors_observed = 0
        self.parity_checks_passed = 0
        self.axis5_protocol_violations = 0

        # Resolve AXIS5-specific signals
        self._resolve_axis5_signals()

        # Start wakeup monitor if enabled
        if self.enable_wakeup and self.wakeup_signal is not None:
            cocotb.start_soon(self._monitor_wakeup())

        if self.log:
            side = "slave" if self.is_slave else "master"
            self.log.info(f"AXIS5Monitor '{self.title}' initialized: "
                         f"{side} side, wakeup={self.enable_wakeup}, parity={self.enable_parity}")

    def _resolve_axis5_signals(self):
        """Resolve AXIS5-specific signals."""
        # Try to find TWAKEUP signal
        self.wakeup_signal = None
        if self.enable_wakeup:
            wakeup_names = [
                f"{self.prefix}twakeup",
                f"{self.prefix}wakeup",
                f"{self.prefix}TWAKEUP",
            ]
            for name in wakeup_names:
                if hasattr(self.dut, name):
                    self.wakeup_signal = getattr(self.dut, name)
                    break

        # Try to find TPARITY signal
        self.parity_signal = None
        if self.enable_parity:
            parity_names = [
                f"{self.prefix}tparity",
                f"{self.prefix}parity",
                f"{self.prefix}TPARITY",
            ]
            for name in parity_names:
                if hasattr(self.dut, name):
                    self.parity_signal = getattr(self.dut, name)
                    break

    async def _monitor_wakeup(self):
        """Monitor for TWAKEUP signaling and check protocol compliance."""
        try:
            last_wakeup_time = None
            data_after_wakeup = False

            while True:
                await RisingEdge(self.clock)

                if self.wakeup_signal is not None:
                    try:
                        wakeup_val = int(self.wakeup_signal.value)

                        if wakeup_val and not self._wakeup_active:
                            # Rising edge of wakeup
                            self._wakeup_active = True
                            last_wakeup_time = get_sim_time(units='ns')
                            self.wakeup_events += 1
                            data_after_wakeup = False

                            self._wakeup_history.append({
                                'time': last_wakeup_time,
                                'type': 'assert'
                            })

                            if self.log and self.super_debug:
                                self.log.debug(f"AXIS5Monitor '{self.title}': "
                                             f"TWAKEUP asserted at {last_wakeup_time}ns")

                        elif not wakeup_val and self._wakeup_active:
                            # Falling edge of wakeup
                            self._wakeup_active = False

                            self._wakeup_history.append({
                                'time': get_sim_time(units='ns'),
                                'type': 'deassert'
                            })

                            # Check if data was seen during wakeup
                            if not data_after_wakeup:
                                # This may or may not be a violation depending on spec interpretation
                                pass

                    except ValueError:
                        pass  # Signal may be X/Z

                # Check for data transfer to track wakeup->data sequence
                if self._wakeup_active and self._is_handshake_valid():
                    data_after_wakeup = True

        except Exception as e:
            if self.log:
                self.log.error(f"AXIS5Monitor '{self.title}': Exception in _monitor_wakeup: {e}")

    async def _monitor_recv(self):
        """
        Monitor for AXIS5 transfers with parity checking.

        Extends parent _monitor_recv with parity verification and AXIS5 protocol checking.
        """
        try:
            while True:
                await FallingEdge(self.clock)

                # Check for valid handshake
                if self._is_handshake_valid():
                    current_time = get_sim_time(units='ns')

                    # Create AXIS5 packet from current data
                    packet = AXIS5Packet(
                        field_config=self.field_config,
                        enable_wakeup=self.enable_wakeup,
                        enable_parity=self.enable_parity,
                        timestamp=current_time
                    )

                    # Collect data using inherited functionality
                    data_dict = self._get_data_dict()
                    self._finish_packet(current_time, packet, data_dict)

                    # Check parity if enabled
                    if self.enable_parity:
                        self._check_parity(packet)

                    # Check AXIS5-specific protocol violations
                    self._check_axis5_protocol_violations(packet)

                    # Update statistics (standard AXIS)
                    self.packets_observed += 1
                    self.total_data_bytes += packet.get_byte_count()

                    # Handle frame boundaries
                    if packet.is_last():
                        self.frames_observed += 1
                        self._current_frame.append(packet)
                        await self._process_complete_frame(self._current_frame)
                        self._current_frame = []
                        self._frame_id = None
                    else:
                        self._current_frame.append(packet)
                        if self._frame_id is None:
                            self._frame_id = packet.id

                    # Check for base protocol violations
                    self._check_protocol_violations(packet)

                    # Write to memory model if available
                    if self.memory_model:
                        self.write_to_memory_unified(packet)

                    if self.log and self.super_debug:
                        self.log.debug(f"AXIS5Monitor '{self.title}': "
                                     f"Observed packet {packet}")

                # Small delay to avoid oversampling
                await Timer(1, units='ps')

        except Exception as e:
            if self.log:
                self.log.error(f"AXIS5Monitor '{self.title}': Exception in _monitor_recv: {e}")
            import traceback
            self.log.error(traceback.format_exc())
            raise

    def _check_parity(self, packet):
        """
        Check parity for observed packet.

        Args:
            packet: AXIS5Packet to check
        """
        if not isinstance(packet, AXIS5Packet):
            return

        if packet.check_parity():
            self.parity_checks_passed += 1
        else:
            self.parity_errors_observed += 1
            packet.parity_error = 1

            if self.log:
                self.log.warning(f"AXIS5Monitor '{self.title}': "
                               f"Parity error observed - expected=0x{packet.calculate_parity():X}, "
                               f"actual=0x{packet.parity:X}, data=0x{packet.data:X}")

    def _check_axis5_protocol_violations(self, packet):
        """
        Check for AXIS5-specific protocol violations.

        Args:
            packet: AXIS5Packet to check
        """
        violations = []

        # Check wakeup was asserted before first transfer in a power-down scenario
        # (This is a simplified check - full implementation would track power states)

        # Check parity signal width matches data width
        if self.enable_parity:
            data_bytes = (self.field_config['data'].bits + 7) // 8
            expected_parity_bits = data_bytes
            if 'parity' in self.field_config:
                actual_parity_bits = self.field_config['parity'].bits
                if actual_parity_bits != expected_parity_bits:
                    violations.append(f"Parity width mismatch: expected {expected_parity_bits}, "
                                    f"got {actual_parity_bits}")

        # Log violations
        if violations:
            self.axis5_protocol_violations += len(violations)
            if self.log:
                for violation in violations:
                    self.log.warning(f"AXIS5Monitor '{self.title}': "
                                   f"AXIS5 Protocol violation: {violation}")

    def get_wakeup_history(self):
        """
        Get history of wakeup events.

        Returns:
            List of wakeup event dictionaries
        """
        return self._wakeup_history.copy()

    def is_wakeup_active(self):
        """Check if wakeup is currently active."""
        return self._wakeup_active

    def get_parity_stats(self):
        """
        Get parity-related statistics.

        Returns:
            Dictionary with parity statistics
        """
        total_checks = self.parity_errors_observed + self.parity_checks_passed
        return {
            'parity_enabled': self.enable_parity,
            'parity_errors': self.parity_errors_observed,
            'parity_passed': self.parity_checks_passed,
            'total_checks': total_checks,
            'error_rate': self.parity_errors_observed / max(1, total_checks)
        }

    def get_wakeup_stats(self):
        """
        Get wakeup-related statistics.

        Returns:
            Dictionary with wakeup statistics
        """
        return {
            'wakeup_enabled': self.enable_wakeup,
            'wakeup_events': self.wakeup_events,
            'wakeup_violations': self.wakeup_violations,
            'wakeup_active': self._wakeup_active,
            'wakeup_history_count': len(self._wakeup_history)
        }

    def get_stats(self):
        """Get comprehensive statistics including AXIS5 extensions."""
        base_stats = super().get_stats()

        # Add AXIS5-specific statistics
        axis5_stats = {
            'axis5_protocol_violations': self.axis5_protocol_violations,
            'parity_stats': self.get_parity_stats(),
            'wakeup_stats': self.get_wakeup_stats(),
        }

        base_stats.update(axis5_stats)
        return base_stats

    def __str__(self):
        """String representation."""
        side = "Slave" if self.is_slave else "Master"
        return (f"AXIS5Monitor '{self.title}' ({side} Side): "
                f"{self.packets_observed} packets observed, "
                f"{self.frames_observed} frames observed, "
                f"wakeup_events={self.wakeup_events}, "
                f"parity_errors={self.parity_errors_observed}, "
                f"violations={self.axis5_protocol_violations + self.protocol_violations}")
