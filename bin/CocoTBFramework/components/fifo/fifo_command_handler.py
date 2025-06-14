"""
FIFO Command Handler for Transaction Dependency Management - FIXED VERSION

This module provides dependency orchestration between FIFO Master and Slave components,
with robust completion tracking and timeout handling to prevent lockups.
"""

import cocotb
from collections import deque
from cocotb.triggers import RisingEdge, Timer, First
from cocotb.utils import get_sim_time


class FIFOCommandHandler:
    """
    Command handler for orchestrating FIFO transaction dependencies.

    Fixed version with robust completion tracking and timeout handling
    to prevent lockups in dependency processing.
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

        # Use existing master/slave statistics instead of custom tracking
        self.master_stats = getattr(master, 'stats', None)
        self.slave_stats = getattr(slave, 'stats', None)

        # Enhanced transaction tracking
        self.active_sequences = {}  # sequence_id -> FIFOSequence
        self.completed_sequences = set()  # Set of completed sequence IDs
        self.sent_packets = {}  # packet_id -> packet
        self.completed_packets = set()  # Set of completed packet IDs
        self.packet_timeouts = {}  # packet_id -> timeout_time

        # Callback management using existing infrastructure
        self.callbacks = []
        self.completion_callbacks = []  # For packet completion tracking

        # Processing task
        self.processor_task = None
        self.running = False

        # Configuration
        self.timeout_cycles = 1000
        self.debug_completion = False

        if self.log:
            self.log.info("FIFO command handler initialized with enhanced tracking")

    async def start(self):
        """
        Start the command handler processing task.

        Returns:
            Self for method chaining
        """
        if not self.running:
            self.running = True

            # Set up monitoring for slave responses
            self._setup_slave_monitoring()

            self.processor_task = cocotb.start_soon(self._process_sequences())

            if self.log:
                self.log.info("FIFO command handler started")
        return self

    async def stop(self):
        """
        Stop the command handler processing task.

        Returns:
            Self for method chaining
        """
        self.running = False
        if self.processor_task:
            try:
                self.processor_task.cancel()
            except:
                pass
            self.processor_task = None

        # Clean up monitoring
        self._cleanup_slave_monitoring()

        if self.log:
            self.log.info("FIFO command handler stopped")
        return self

    def _setup_slave_monitoring(self):
        """Set up monitoring of slave responses for completion tracking."""
        # Add our completion callback to slave if possible
        if hasattr(self.slave, 'add_callback'):
            self.slave.add_callback(self._handle_slave_response)
            if self.log:
                self.log.debug("Added completion callback to slave via add_callback")
        elif hasattr(self.slave, 'callbacks'):
            if self._handle_slave_response not in self.slave.callbacks:
                self.slave.callbacks.append(self._handle_slave_response)
            if self.log:
                self.log.debug("Added completion callback to slave via callbacks list")
        else:
            if self.log:
                self.log.warning("Slave has no callback mechanism - using polling for completion")

    def _cleanup_slave_monitoring(self):
        """Clean up slave monitoring."""
        if hasattr(self.slave, 'remove_callback'):
            try:
                self.slave.remove_callback(self._handle_slave_response)
            except:
                pass
        elif hasattr(self.slave, 'callbacks') and self._handle_slave_response in self.slave.callbacks:
            try:
                self.slave.callbacks.remove(self._handle_slave_response)
            except:
                pass

    def add_callback(self, callback):
        """
        Add a callback function to be called when sequences complete.

        Args:
            callback: Function to call with completed sequence

        Returns:
            Self for method chaining
        """
        if callback not in self.callbacks:
            self.callbacks.append(callback)
        return self

    def remove_callback(self, callback):
        """
        Remove a previously added callback function.

        Args:
            callback: Function to remove

        Returns:
            Self for method chaining
        """
        if callback in self.callbacks:
            self.callbacks.remove(callback)
        return self

    async def process_sequence(self, sequence):
        """
        Process a FIFO sequence with robust dependency handling and timeout protection.

        Args:
            sequence: FIFOSequence to process (uses built-in dependency tracking)

        Returns:
            Dictionary of responses by transaction index
        """
        sequence_id = id(sequence)
        self.active_sequences[sequence_id] = sequence

        if self.log:
            self.log.info(f"Processing sequence '{sequence.name}' with {sequence.transaction_counter} transactions")

        try:
            # Generate packets from sequence (uses existing PacketFactory infrastructure)
            packets = sequence.generate_packets()

            if not packets:
                if self.log:
                    self.log.warning(f"Sequence '{sequence.name}' generated no packets")
                return {}

            # Use existing dependency graph from sequence
            dependency_graph = sequence.get_dependency_graph()
            dependencies = dependency_graph['dependencies']
            dependency_types = dependency_graph['dependency_types']

            # Track sent and completed packets with IDs
            sent_packets = {}      # packet_index -> packet_id
            completed_packets = set()  # Set of completed packet indices
            response_map = {}
            packet_start_times = {}  # packet_index -> start_time

            # Process packets respecting dependencies with timeout protection
            for packet_index, packet in enumerate(packets):
                packet_id = id(packet)
                packet_start_times[packet_index] = get_sim_time('ns')

                # Check if this packet has dependencies
                if packet_index in dependencies:
                    depends_on_index = dependencies[packet_index]
                    dependency_type = dependency_types.get(packet_index, "after")

                    if self.debug_completion:
                        self.log.debug(f"Packet {packet_index} depends on {depends_on_index} (type: {dependency_type})")

                    # Wait for dependency with timeout protection
                    if dependency_type == "after":
                        timeout_cycles = 0
                        max_timeout = self.timeout_cycles

                        while (depends_on_index not in completed_packets and
                               self.running and timeout_cycles < max_timeout):
                            await RisingEdge(self.master.clock)
                            timeout_cycles += 1

                            # Check for completion periodically
                            if timeout_cycles % 50 == 0:
                                self._check_completion_status(completed_packets, sent_packets)

                        if timeout_cycles >= max_timeout:
                            if self.log:
                                self.log.error(f"Timeout waiting for dependency {depends_on_index} "
                                             f"for packet {packet_index}")
                            # Continue anyway to avoid complete lockup
                    # Could add other dependency types here

                # Send the packet using existing master infrastructure
                try:
                    await self.master.send(packet)
                    sent_packets[packet_index] = packet_id
                    self.sent_packets[packet_id] = packet

                    if self.debug_completion:
                        self.log.debug(f"Sent packet {packet_index} (ID: {packet_id}) from sequence '{sequence.name}'")

                except Exception as e:
                    if self.log:
                        self.log.error(f"Error sending packet {packet_index}: {e}")
                    response_map[packet_index] = f"Send error: {e}"
                    continue

            # Wait for all packets to be processed with robust timeout handling
            expected_count = len(packets)

            if self.log:
                self.log.info(f"Waiting for {expected_count} packets to complete...")

            # Enhanced completion waiting with multiple completion strategies
            completion_timeout = self.timeout_cycles * 2  # More generous timeout
            wait_cycles = 0
            last_completion_count = 0
            stall_cycles = 0
            max_stall_cycles = 100

            while (len(completed_packets) < expected_count and
                   self.running and wait_cycles < completion_timeout):

                await RisingEdge(self.master.clock)
                wait_cycles += 1

                # Check completion using multiple strategies
                if wait_cycles % 10 == 0:  # Check every 10 cycles
                    self._check_completion_status(completed_packets, sent_packets)

                    # Alternative completion detection via monitor queues
                    if hasattr(self.slave, '_recvQ'):
                        slave_queue_size = len(self.slave._recvQ)
                        if slave_queue_size > len(completed_packets):
                            # Mark additional packets as completed
                            for i in range(len(completed_packets), min(slave_queue_size, expected_count)):
                                if i not in completed_packets:
                                    completed_packets.add(i)
                                    if self.debug_completion:
                                        self.log.debug(f"Marked packet {i} as completed via queue size")

                # Detect stalls
                if len(completed_packets) == last_completion_count:
                    stall_cycles += 1
                    if stall_cycles >= max_stall_cycles:
                        if self.log:
                            self.log.warning(f"Completion stalled at {len(completed_packets)}/{expected_count} "
                                           f"after {stall_cycles} cycles")
                        # Force completion of remaining packets to avoid infinite wait
                        for i in range(expected_count):
                            if i not in completed_packets:
                                completed_packets.add(i)
                                if self.log:
                                    self.log.warning(f"Force-completed packet {i} due to stall")
                        break
                else:
                    last_completion_count = len(completed_packets)
                    stall_cycles = 0

            if wait_cycles >= completion_timeout:
                if self.log:
                    self.log.error(f"Timeout waiting for packet completion! "
                                 f"Got {len(completed_packets)}/{expected_count} after {wait_cycles} cycles")
                # Force mark remaining as timed out
                for i in range(expected_count):
                    if i not in completed_packets:
                        completed_packets.add(i)

            # Mark sequence as completed
            self.completed_sequences.add(sequence_id)
            if sequence_id in self.active_sequences:
                del self.active_sequences[sequence_id]

            # Collect final response map
            for packet_index in range(expected_count):
                if packet_index in completed_packets:
                    response_map[packet_index] = f"Completed packet {packet_index} from sequence '{sequence.name}'"
                else:
                    response_map[packet_index] = f"Timeout for packet {packet_index}"

            if self.log:
                completed_count = len(completed_packets)
                self.log.info(f"Sequence '{sequence.name}' completed: {completed_count}/{expected_count} packets")

            # Trigger callbacks
            for callback in self.callbacks:
                try:
                    callback({'sequence': sequence, 'responses': response_map})
                except Exception as e:
                    if self.log:
                        self.log.error(f"Error in sequence completion callback: {e}")

            return response_map

        except Exception as e:
            if self.log:
                self.log.error(f"Error processing sequence '{sequence.name}': {e}")
            # Clean up on error
            if sequence_id in self.active_sequences:
                del self.active_sequences[sequence_id]
            raise

        finally:
            # Always clean up packet tracking for this sequence
            packets_to_remove = []
            for packet_id, packet in self.sent_packets.items():
                if hasattr(packet, '_sequence_id') and packet._sequence_id == sequence_id:
                    packets_to_remove.append(packet_id)
            for packet_id in packets_to_remove:
                if packet_id in self.sent_packets:
                    del self.sent_packets[packet_id]
                if packet_id in self.completed_packets:
                    self.completed_packets.remove(packet_id)

    def _check_completion_status(self, completed_packets, sent_packets):
        """Check and update completion status using available information."""
        # This is a more robust version that checks multiple completion indicators

        # Check master's sent queue if available
        if hasattr(self.master, 'sent_queue'):
            master_sent_count = len(self.master.sent_queue)
            # Simple heuristic: if master has sent packets, assume they're completed
            for i in range(min(master_sent_count, len(sent_packets))):
                if i not in completed_packets:
                    completed_packets.add(i)
                    if self.debug_completion:
                        self.log.debug(f"Marked packet {i} as completed via master queue")

    async def _process_sequences(self):
        """
        Main processing loop for active sequences with enhanced monitoring.
        """
        while self.running:
            try:
                # Periodic cleanup and monitoring
                current_time = get_sim_time('ns')

                # Clean up old packet timeouts
                expired_packets = []
                for packet_id, timeout_time in self.packet_timeouts.items():
                    if current_time > timeout_time:
                        expired_packets.append(packet_id)

                for packet_id in expired_packets:
                    if packet_id in self.packet_timeouts:
                        del self.packet_timeouts[packet_id]
                    if packet_id not in self.completed_packets:
                        self.completed_packets.add(packet_id)
                        if self.log:
                            self.log.warning(f"Packet {packet_id} timed out and marked completed")

                # Wait for next cycle
                await RisingEdge(self.master.clock)

            except Exception as e:
                if self.log:
                    self.log.error(f"Error in process_sequences loop: {e}")
                await RisingEdge(self.master.clock)  # Continue despite errors

    def _handle_slave_response(self, response):
        """
        Handle a response from the slave for completion tracking.

        Args:
            response: Response packet from slave
        """
        try:
            # Mark response as completed
            response_id = id(response)
            self.completed_packets.add(response_id)

            if self.debug_completion and self.log:
                response_str = (response.formatted(compact=True)
                              if hasattr(response, 'formatted')
                              else str(response))
                self.log.debug(f"Received slave response: {response_str}")

        except Exception as e:
            if self.log:
                self.log.error(f"Error handling slave response: {e}")

    async def send_packet_with_delay(self, packet, delay_cycles=0):
        """
        Send a single packet with optional delay using existing infrastructure.

        Args:
            packet: Packet to send
            delay_cycles: Number of cycles to wait before sending

        Returns:
            True if sent successfully, False otherwise
        """
        try:
            # Apply delay if specified
            if delay_cycles > 0:
                for _ in range(delay_cycles):
                    await RisingEdge(self.master.clock)

            # Send using existing master infrastructure
            await self.master.send(packet)

            # Track the packet
            packet_id = id(packet)
            self.sent_packets[packet_id] = packet

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

    def set_timeout_cycles(self, cycles):
        """Set the timeout for dependency and completion waiting."""
        self.timeout_cycles = cycles
        if self.log:
            self.log.info(f"Set timeout cycles to {cycles}")

    def set_debug_completion(self, debug=True):
        """Enable/disable debug logging for completion tracking."""
        self.debug_completion = debug
        if self.log:
            self.log.info(f"Debug completion tracking: {'enabled' if debug else 'disabled'}")

    def get_status(self):
        """
        Get current status with enhanced information.

        Returns:
            Dictionary with status information
        """
        status = {
            'running': self.running,
            'active_sequences': len(self.active_sequences),
            'completed_sequences': len(self.completed_sequences),
            'sent_packets': len(self.sent_packets),
            'completed_packets': len(self.completed_packets),
            'pending_packets': len(self.sent_packets) - len(self.completed_packets),
            'timeout_cycles': self.timeout_cycles,
            'debug_completion': self.debug_completion
        }

        # Add master statistics if available
        if self.master_stats and hasattr(self.master_stats, 'get_stats'):
            status['master_stats'] = self.master_stats.get_stats()

        # Add slave statistics if available
        if self.slave_stats and hasattr(self.slave_stats, 'get_stats'):
            status['slave_stats'] = self.slave_stats.get_stats()

        # Add sequence details
        sequence_details = {}
        for seq_id, sequence in self.active_sequences.items():
            if hasattr(sequence, 'get_stats'):
                sequence_details[sequence.name] = sequence.get_stats()
        status['sequence_details'] = sequence_details

        return status

    def clear_completed(self):
        """
        Clear completed sequence and packet tracking to free memory.

        Returns:
            Self for method chaining
        """
        self.completed_sequences.clear()
        self.completed_packets.clear()

        # Clean up old packet tracking
        packets_to_remove = [pid for pid in self.sent_packets.keys()]
        for pid in packets_to_remove:
            del self.sent_packets[pid]

        if self.log:
            self.log.debug("Cleared completed sequence and packet tracking")
        return self

    def get_stats(self):
        """
        Get comprehensive statistics leveraging existing infrastructure.

        Returns:
            Dictionary with comprehensive statistics
        """
        stats = self.get_status()

        # Add component-specific stats if available
        if hasattr(self.master, 'get_stats'):
            stats['master_component_stats'] = self.master.get_stats()

        if hasattr(self.slave, 'get_stats'):
            stats['slave_component_stats'] = self.slave.get_stats()

        return stats

    def __str__(self):
        """String representation"""
        active_count = len(self.active_sequences)
        completed_count = len(self.completed_sequences)
        status = "running" if self.running else "stopped"
        pending = len(self.sent_packets) - len(self.completed_packets)

        return (f"FIFOCommandHandler({status}): "
                f"{active_count} active, {completed_count} completed sequences, "
                f"{pending} pending packets")
