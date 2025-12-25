# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXIS5Master
# Purpose: AXIS5 Master - Stream protocol master with AMBA5 extensions
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-21

"""
AXIS5 Master - Stream protocol master with AMBA5 extensions

This module provides AXIS5 Master functionality with:
- TWAKEUP: Wake-up signaling before data transfer
- TPARITY: Data parity protection
"""

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.utils import get_sim_time
from collections import deque

from ..axis4.axis_master import AXISMaster
from .axis5_packet import AXIS5Packet
from .axis5_field_configs import AXIS5FieldConfigs


class AXIS5Master(AXISMaster):
    """
    AXIS5 Master component for driving AXI5-Stream protocol.

    Extends AXISMaster with AMBA5-specific features:
    - Wake-up signaling (TWAKEUP)
    - Parity generation (TPARITY)
    - Power management coordination
    """

    def __init__(self, dut, title, prefix, clock, field_config=None,
                 timeout_cycles=1000, mode='skid',
                 bus_name='', pkt_prefix='',
                 multi_sig=False, randomizer=None, memory_model=None,
                 log=None, super_debug=False, pipeline_debug=False,
                 signal_map=None, enable_wakeup=True, enable_parity=False,
                 wakeup_cycles=3, **kwargs):
        """
        Initialize AXIS5 Master.

        Args:
            dut: Device under test
            title: Component title/name
            prefix: Bus prefix (e.g., "m_axis5_", "fub_axis5_")
            clock: Clock signal
            field_config: Field configuration (if None, creates default)
            timeout_cycles: Maximum cycles to wait for ready
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
            enable_wakeup: Enable TWAKEUP signaling
            enable_parity: Enable TPARITY generation
            wakeup_cycles: Number of cycles for wakeup signaling
            **kwargs: Additional configuration
        """
        # Store AXIS5 configuration before super().__init__
        self.enable_wakeup = enable_wakeup
        self.enable_parity = enable_parity
        self.wakeup_cycles = wakeup_cycles

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
        self._wakeup_active = False
        self._wakeup_pending = False

        # AXIS5 statistics
        self.wakeup_events = 0
        self.parity_errors_generated = 0

        # Resolve AXIS5-specific signals
        self._resolve_axis5_signals()

        if self.log:
            self.log.info(f"AXIS5Master '{self.title}' initialized: "
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

    async def send_packet(self, packet):
        """
        Send a single AXIS5 packet with wakeup and parity handling.

        Args:
            packet: AXIS5Packet to send

        Returns:
            True if successful, False if timeout
        """
        # Assert wakeup if needed
        if self.enable_wakeup and self._wakeup_pending:
            await self._assert_wakeup()
            self._wakeup_pending = False

        # Calculate and set parity if enabled
        if self.enable_parity and isinstance(packet, AXIS5Packet):
            packet.parity = packet.calculate_parity()

        # Use parent send_packet
        result = await super().send_packet(packet)

        return result

    async def _assert_wakeup(self):
        """Assert TWAKEUP signal for configured number of cycles."""
        if self.wakeup_signal is not None:
            self._wakeup_active = True
            self.wakeup_signal.value = 1

            if self.log and self.super_debug:
                self.log.debug(f"AXIS5Master '{self.title}': TWAKEUP asserted")

            # Hold wakeup for configured cycles
            for _ in range(self.wakeup_cycles):
                await RisingEdge(self.clock)

            self.wakeup_signal.value = 0
            self._wakeup_active = False
            self.wakeup_events += 1

            if self.log and self.super_debug:
                self.log.debug(f"AXIS5Master '{self.title}': TWAKEUP deasserted")

    def request_wakeup(self):
        """Request wakeup signaling before next transfer."""
        if self.enable_wakeup:
            self._wakeup_pending = True

    async def send_stream_data_with_wakeup(self, data_list, id=0, dest=0, user=0,
                                           auto_last=True, strb_list=None):
        """
        Send stream data with wakeup signaling at the start.

        Args:
            data_list: List of data values to send
            id: Stream ID for all transfers
            dest: Destination for all transfers
            user: User signal for all transfers
            auto_last: Automatically set TLAST on final transfer
            strb_list: Optional list of strobe values

        Returns:
            True if successful, False if timeout
        """
        # Request wakeup before sending
        self.request_wakeup()

        # Convert to AXIS5 packets with parity
        packets = []
        for i, data in enumerate(data_list):
            is_last = auto_last and (i == len(data_list) - 1)

            strb = None
            if strb_list and i < len(strb_list):
                strb = strb_list[i]

            packet = AXIS5Packet(
                field_config=self.field_config,
                enable_wakeup=self.enable_wakeup,
                enable_parity=self.enable_parity
            )
            packet.data = data
            packet.last = 1 if is_last else 0
            packet.id = id
            packet.dest = dest
            packet.user = user

            if strb is not None:
                packet.strb = strb
            elif 'strb' in self.field_config:
                strb_bits = self.field_config['strb'].bits
                packet.strb = (1 << strb_bits) - 1

            if self.enable_wakeup:
                packet.wakeup = 1 if (i == 0 and self._wakeup_pending) else 0

            packets.append(packet)

        # Send all packets
        for i, packet in enumerate(packets):
            if i == 0:
                # First packet triggers wakeup
                success = await self.send_packet(packet)
            else:
                success = await super().send_packet(packet)

            if not success:
                return False

        return True

    async def send_single_beat_axis5(self, data, last=1, id=0, dest=0, user=0,
                                     strb=None, wakeup=False):
        """
        Send a single AXIS5 beat/transfer.

        Args:
            data: Data value
            last: TLAST value
            id: Stream ID
            dest: Destination
            user: User signal
            strb: Strobe value (if None, auto-generate)
            wakeup: Whether to assert wakeup

        Returns:
            True if successful
        """
        packet = AXIS5Packet(
            field_config=self.field_config,
            enable_wakeup=self.enable_wakeup,
            enable_parity=self.enable_parity
        )
        packet.data = data
        packet.last = last
        packet.id = id
        packet.dest = dest
        packet.user = user

        if strb is not None:
            packet.strb = strb
        elif 'strb' in self.field_config:
            strb_bits = self.field_config['strb'].bits
            packet.strb = (1 << strb_bits) - 1

        if wakeup:
            self.request_wakeup()

        return await self.send_packet(packet)

    def inject_parity_error(self, enable=True):
        """
        Enable/disable parity error injection for testing.

        Args:
            enable: True to inject errors, False to generate correct parity
        """
        # This will be used during packet creation to flip parity
        self._inject_parity_error = enable

    def is_wakeup_active(self):
        """Check if wakeup is currently active."""
        return self._wakeup_active

    def get_stats(self):
        """Get comprehensive statistics including AXIS5 extensions."""
        base_stats = super().get_stats()

        # Add AXIS5-specific statistics
        axis5_stats = {
            'wakeup_enabled': self.enable_wakeup,
            'parity_enabled': self.enable_parity,
            'wakeup_events': self.wakeup_events,
            'parity_errors_generated': self.parity_errors_generated,
            'wakeup_active': self._wakeup_active,
            'wakeup_pending': self._wakeup_pending,
        }

        base_stats.update(axis5_stats)
        return base_stats

    def __str__(self):
        """String representation."""
        return (f"AXIS5Master '{self.title}': "
                f"{self.packets_sent} packets sent, "
                f"{self.frames_sent} frames sent, "
                f"wakeup_events={self.wakeup_events}, "
                f"wakeup={self.enable_wakeup}, parity={self.enable_parity}")
