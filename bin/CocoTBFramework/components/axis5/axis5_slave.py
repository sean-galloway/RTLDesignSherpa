# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXIS5Slave
# Purpose: AXIS5 Slave - Stream protocol slave with AMBA5 extensions
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-21

"""
AXIS5 Slave - Stream protocol slave with AMBA5 extensions

This module provides AXIS5 Slave functionality with:
- TWAKEUP: Wake-up signaling detection
- TPARITY: Data parity checking
"""

import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.utils import get_sim_time

from ..axis4.axis_slave import AXISSlave
from .axis5_packet import AXIS5Packet
from .axis5_field_configs import AXIS5FieldConfigs


class AXIS5Slave(AXISSlave):
    """
    AXIS5 Slave component for receiving AXI5-Stream protocol.

    Extends AXISSlave with AMBA5-specific features:
    - Wake-up signaling detection (TWAKEUP)
    - Parity checking (TPARITY)
    - Power management coordination
    """

    def __init__(self, dut, title, prefix, clock, field_config=None,
                 timeout_cycles=1000, mode='skid',
                 bus_name='', pkt_prefix='', multi_sig=False,
                 randomizer=None, memory_model=None, log=None,
                 super_debug=False, pipeline_debug=False,
                 signal_map=None, enable_wakeup=True, enable_parity=False,
                 **kwargs):
        """
        Initialize AXIS5 Slave.

        Args:
            dut: Device under test
            title: Component title/name
            prefix: Bus prefix (e.g., "s_axis5_", "axis5_")
            clock: Clock signal
            field_config: Field configuration (if None, creates default)
            timeout_cycles: Maximum cycles for operations
            mode: Protocol mode ('skid', 'blocking', etc.)
            bus_name: Bus/channel name
            pkt_prefix: Packet field prefix
            multi_sig: Whether using multi-signal mode
            randomizer: Optional randomizer for timing
            memory_model: Optional memory model
            log: Logger instance
            super_debug: Enable detailed debugging
            pipeline_debug: Enable pipeline debugging
            signal_map: Optional manual signal mapping
            enable_wakeup: Enable TWAKEUP detection
            enable_parity: Enable TPARITY checking
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
            field_config=field_config, timeout_cycles=timeout_cycles,
            mode=mode, bus_name=bus_name, pkt_prefix=pkt_prefix,
            multi_sig=multi_sig, randomizer=randomizer,
            memory_model=memory_model, log=log,
            super_debug=super_debug, pipeline_debug=pipeline_debug,
            signal_map=signal_map, **kwargs
        )

        # AXIS5 state
        self._wakeup_detected = False
        self._last_wakeup_time = None

        # AXIS5 statistics
        self.wakeup_events = 0
        self.parity_errors_detected = 0
        self.parity_checks_passed = 0

        # Resolve AXIS5-specific signals
        self._resolve_axis5_signals()

        # Start wakeup monitor if enabled
        if self.enable_wakeup and self.wakeup_signal is not None:
            cocotb.start_soon(self._monitor_wakeup())

        if self.log:
            self.log.info(f"AXIS5Slave '{self.title}' initialized: "
                         f"wakeup={self.enable_wakeup}, parity={self.enable_parity}")

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
        """Monitor for TWAKEUP signaling."""
        try:
            while True:
                await RisingEdge(self.clock)

                if self.wakeup_signal is not None:
                    try:
                        wakeup_val = int(self.wakeup_signal.value)
                        if wakeup_val and not self._wakeup_detected:
                            self._wakeup_detected = True
                            self._last_wakeup_time = get_sim_time(units='ns')
                            self.wakeup_events += 1

                            if self.log and self.super_debug:
                                self.log.debug(f"AXIS5Slave '{self.title}': "
                                             f"TWAKEUP detected at {self._last_wakeup_time}ns")

                        elif not wakeup_val and self._wakeup_detected:
                            self._wakeup_detected = False

                    except ValueError:
                        pass  # Signal may be X/Z

        except Exception as e:
            if self.log:
                self.log.error(f"AXIS5Slave '{self.title}': Exception in _monitor_wakeup: {e}")

    async def _monitor_recv(self):
        """
        Monitor for incoming AXIS5 transfers with parity checking.

        Extends parent _monitor_recv with parity verification.
        """
        try:
            while True:
                await RisingEdge(self.clock)

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

                    # Update statistics
                    self.packets_received += 1
                    self.total_data_bytes += packet.get_byte_count()

                    # Handle frame boundaries
                    if packet.is_last():
                        self.frames_received += 1
                        self._current_frame.append(packet)
                        await self._process_complete_frame(self._current_frame)
                        self._current_frame = []
                        self._frame_id = None
                    else:
                        self._current_frame.append(packet)
                        if self._frame_id is None:
                            self._frame_id = packet.id

                    # Write to memory model if available
                    if self.memory_model:
                        self.write_to_memory_unified(packet)

                    if self.log and self.super_debug:
                        self.log.debug(f"AXIS5Slave '{self.title}': "
                                     f"Received packet {packet}")

                # Apply ready signal timing if randomizer is available
                if self.randomizer and hasattr(self, 'ready_signal'):
                    await self._apply_ready_timing()

                # Small delay to avoid oversampling
                await Timer(1, units='ps')

        except Exception as e:
            if self.log:
                self.log.error(f"AXIS5Slave '{self.title}': Exception in _monitor_recv: {e}")
            import traceback
            self.log.error(traceback.format_exc())
            raise

    def _check_parity(self, packet):
        """
        Check parity for received packet.

        Args:
            packet: AXIS5Packet to check
        """
        if not isinstance(packet, AXIS5Packet):
            return

        if packet.check_parity():
            self.parity_checks_passed += 1
        else:
            self.parity_errors_detected += 1
            packet.parity_error = 1

            if self.log:
                self.log.warning(f"AXIS5Slave '{self.title}': "
                               f"Parity error detected - expected=0x{packet.calculate_parity():X}, "
                               f"received=0x{packet.parity:X}")

    def is_wakeup_active(self):
        """Check if wakeup is currently detected."""
        return self._wakeup_detected

    def get_last_wakeup_time(self):
        """Get timestamp of last wakeup event."""
        return self._last_wakeup_time

    def get_stats(self):
        """Get comprehensive statistics including AXIS5 extensions."""
        base_stats = super().get_stats()

        # Add AXIS5-specific statistics
        axis5_stats = {
            'wakeup_enabled': self.enable_wakeup,
            'parity_enabled': self.enable_parity,
            'wakeup_events': self.wakeup_events,
            'wakeup_active': self._wakeup_detected,
            'last_wakeup_time': self._last_wakeup_time,
            'parity_errors_detected': self.parity_errors_detected,
            'parity_checks_passed': self.parity_checks_passed,
            'parity_error_rate': (self.parity_errors_detected /
                                 max(1, self.parity_errors_detected + self.parity_checks_passed)),
        }

        base_stats.update(axis5_stats)
        return base_stats

    def __str__(self):
        """String representation."""
        return (f"AXIS5Slave '{self.title}': "
                f"{self.packets_received} packets received, "
                f"{self.frames_received} frames received, "
                f"wakeup_events={self.wakeup_events}, "
                f"parity_errors={self.parity_errors_detected}")
