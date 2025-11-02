# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FIFOCommandHandler
# Purpose: FIFO Command Handler - CLEANED VERSION
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
FIFO Command Handler - CLEANED VERSION

Simplified command handler that leverages existing component infrastructure
instead of reimplementing completion tracking and statistics.

Focuses on core functionality:
- Processing sequences through existing master/slave components
- Simple dependency handling when needed
- Callback management
- Basic timeout protection
"""

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.utils import get_sim_time


class FIFOCommandHandler:
    """
    Simplified command handler for FIFO transaction processing.

    Leverages existing master/slave infrastructure instead of duplicating
    completion tracking, statistics, and timeout mechanisms.
    """

    def __init__(self, master, slave, log=None):
        """
        Initialize the FIFO command handler.

        Args:
            master: FIFOMaster instance
            slave: FIFOSlave instance
            log: Logger instance
        """
        self.master = master
        self.slave = slave
        self.log = log or getattr(master, 'log', None)

        # Simple sequence tracking
        self.active_sequences = {}  # sequence_id -> sequence
        self.callbacks = []         # Completion callbacks

        # Processing control
        self.running = False
        self.timeout_cycles = 1000  # Simple timeout for basic protection

        if self.log:
            self.log.info("FIFO command handler initialized")

    async def start(self):
        """Start the command handler."""
        self.running = True
        if self.log:
            self.log.info("FIFO command handler started")
        return self

    async def stop(self):
        """Stop the command handler."""
        self.running = False
        if self.log:
            self.log.info("FIFO command handler stopped")
        return self

    def add_callback(self, callback):
        """Add a callback function for sequence completion."""
        if callback not in self.callbacks:
            self.callbacks.append(callback)
        return self

    def remove_callback(self, callback):
        """Remove a callback function."""
        if callback in self.callbacks:
            self.callbacks.remove(callback)
        return self

    async def process_sequence(self, sequence):
        """
        Process a FIFO sequence using existing component infrastructure.

        Simplified approach that relies on the master and slave components
        to handle their own timing, completion tracking, and statistics.

        Args:
            sequence: FIFOSequence to process

        Returns:
            Dictionary of responses by transaction index
        """
        sequence_id = id(sequence)
        self.active_sequences[sequence_id] = sequence

        if self.log:
            self.log.info(f"Processing sequence '{sequence.name}'")

        try:
            # Generate packets using sequence's existing infrastructure
            packets = sequence.generate_packets()

            if not packets:
                if self.log:
                    self.log.warning(f"Sequence '{sequence.name}' generated no packets")
                return {}

            response_map = {}

            # Simple sequential processing - let components handle complexity
            for i, packet in enumerate(packets):
                try:
                    # Apply any sequence-specific delay
                    delay = getattr(packet, 'sequence_delay', 0)
                    if delay > 0:
                        await self._wait_cycles(delay)

                    # Send using existing master infrastructure
                    # The master handles its own timing, queuing, and completion
                    await self.master.send(packet)

                    response_map[i] = f"Completed packet {i} from sequence '{sequence.name}'"

                    if self.log:
                        self.log.debug(f"Sent packet {i} from sequence '{sequence.name}'")

                except Exception as e:
                    error_msg = f"Error sending packet {i}: {e}"
                    response_map[i] = error_msg
                    if self.log:
                        self.log.error(error_msg)
                    continue

            # Sequence completed
            if self.log:
                self.log.info(f"Sequence '{sequence.name}' completed: {len(packets)} packets")

            # Trigger callbacks
            self._trigger_callbacks(sequence, response_map)

            return response_map

        except Exception as e:
            if self.log:
                self.log.error(f"Error processing sequence '{sequence.name}': {e}")
            raise

        finally:
            # Clean up tracking
            if sequence_id in self.active_sequences:
                del self.active_sequences[sequence_id]

    async def send_packet_with_delay(self, packet, delay_cycles=0):
        """
        Send a single packet with optional delay.

        Args:
            packet: Packet to send
            delay_cycles: Number of cycles to wait before sending

        Returns:
            True if sent successfully, False otherwise
        """
        try:
            # Apply delay if specified
            if delay_cycles > 0:
                await self._wait_cycles(delay_cycles)

            # Send using existing master infrastructure
            await self.master.send(packet)

            if self.log:
                packet_str = (packet.formatted(compact=True)
                            if hasattr(packet, 'formatted')
                            else str(packet))
                self.log.debug(f"Sent packet with {delay_cycles} cycle delay: {packet_str}")

            return True

        except Exception as e:
            if self.log:
                self.log.error(f"Error sending packet: {e}")
            return False

    async def _wait_cycles(self, cycles):
        """Wait for specified number of cycles with timeout protection."""
        if cycles <= 0:
            return

        # Simple timeout protection
        cycles = min(cycles, self.timeout_cycles)

        for _ in range(cycles):
            if not self.running:
                break
            await RisingEdge(self.master.clock)

    def _trigger_callbacks(self, sequence, response_map):
        """Trigger completion callbacks with error handling."""
        for callback in self.callbacks:
            try:
                callback({
                    'sequence': sequence,
                    'responses': response_map,
                    'status': 'completed'
                })
            except Exception as e:
                if self.log:
                    self.log.error(f"Error in completion callback: {e}")

    def set_timeout_cycles(self, cycles):
        """Set the timeout for basic protection."""
        self.timeout_cycles = cycles
        if self.log:
            self.log.info(f"Set timeout cycles to {cycles}")

    def get_stats(self):
        """
        Get comprehensive statistics using existing component infrastructure.

        Returns:
            Dictionary with statistics information
        """
        stats = {
            'running': self.running,
            'active_sequences': len(self.active_sequences),
            'timeout_cycles': self.timeout_cycles
        }

        # Get statistics from existing component infrastructure
        if hasattr(self.master, 'get_stats'):
            stats['master_stats'] = self.master.get_stats()

        if hasattr(self.slave, 'get_stats'):
            stats['slave_stats'] = self.slave.get_stats()

        return stats

    def get_status(self):
        """Alias for get_stats() for backward compatibility."""
        return self.get_stats()

    def clear_completed(self):
        """Clear any cached state (minimal since we rely on components)."""
        # Most state is handled by the components themselves
        if self.log:
            self.log.debug("Cleared command handler state")
        return self

    def __str__(self):
        active_count = len(self.active_sequences)
        status = "running" if self.running else "stopped"
        return f"FIFOCommandHandler({status}): {active_count} active sequences"
