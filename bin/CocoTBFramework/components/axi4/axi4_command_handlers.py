"""
AXI4 Command Handlers

This module provides command handlers for AXI4 interfaces to manage transactions
between different channel components. These handlers coordinate the communication
between address channels and data channels while leveraging memory models.
"""

import cocotb
from cocotb.triggers import RisingEdge, Timer

class AXI4ReadCommandHandler:
    """
    Command handler for AXI4 Read operations.

    This class coordinates the flow between AR channel (address read) and R channel (read data),
    providing similar functionality to GAXICommandHandler_APBSlave but for AXI4 read operations.
    """

    def __init__(self, ar_slave, r_master, memory_model=None, log=None):
        """
        Initialize AXI4 Read Command Handler.

        Args:
            ar_slave: AXI4 AR channel slave component that receives read requests
            r_master: AXI4 R channel master component that returns read data
            memory_model: Optional memory model for data storage (if None, will use ar_slave's model)
            log: Logger instance
        """
        self.ar_slave = ar_slave
        self.r_master = r_master
        self.memory_model = memory_model or ar_slave.memory_model
        self.log = log or ar_slave.log

        # Task handle
        self.processor_task = None
        self.running = False

        # Transaction tracking
        self.pending_transactions = {}

    async def start(self):
        """Start command handler processor task."""
        if not self.running:
            self.running = True
            self.processor_task = cocotb.start_soon(self._process_requests())
            self.log.info("AXI4ReadCommandHandler started")

    async def stop(self):
        """Stop command handler processor task."""
        self.running = False
        if self.processor_task:
            await Timer(10, units='ns')  # Allow task to complete
            self.processor_task = None
            self.log.info("AXI4ReadCommandHandler stopped")

    async def _process_requests(self):
        """
        Process read requests from AR slave and generate responses through R master.
        """
        clock = self.ar_slave.clock
        self.log.info("AXI4ReadCommandHandler: _process_requests started")

        while self.running:
            # Check for new AR transactions in the slave
            if self.ar_slave.ar_slave.received_queue:
                # Get the AR transaction
                ar_transaction = self.ar_slave.ar_slave.received_queue.popleft()
                self.log.info(f"AXI4ReadCommandHandler: Processing AR transaction: {ar_transaction}")

                # Extract key information
                if hasattr(ar_transaction, 'arid'):
                    id_value = ar_transaction.arid
                    addr = ar_transaction.araddr
                    burst_length = ar_transaction.arlen if hasattr(ar_transaction, 'arlen') else 0
                    burst_size = ar_transaction.arsize if hasattr(ar_transaction, 'arsize') else 0
                    burst_type = ar_transaction.arburst if hasattr(ar_transaction, 'arburst') else 1  # INCR

                    # Calculate addresses for burst
                    addresses = ar_transaction.get_burst_addresses() if hasattr(ar_transaction, 'get_burst_addresses') else [addr]

                    # Store details in pending transactions
                    self.pending_transactions[id_value] = {
                        'ar_transaction': ar_transaction,
                        'addresses': addresses,
                        'burst_length': burst_length,
                        'burst_size': burst_size,
                        'burst_type': burst_type,
                        'beats_completed': 0
                    }

                    self.log.info(f"Processing read request: ID={id_value}, ADDR=0x{addr:X}, LEN={burst_length}")

                    # Send read responses for all beats
                    await self._send_read_responses(id_value)

            # Wait before checking again
            await RisingEdge(clock)

    async def _send_read_responses(self, id_value):
        """
        Send read data responses for a transaction ID.

        Args:
            id_value: Transaction ID to process
        """
        if id_value not in self.pending_transactions:
            return

        transaction = self.pending_transactions[id_value]
        ar_transaction = transaction['ar_transaction']
        addresses = transaction['addresses']
        burst_length = transaction['burst_length']
        burst_size = transaction['burst_size']

        # Calculate bytes per beat based on size
        bytes_per_beat = 1 << burst_size

        # Send response for each beat in the burst
        for i in range(burst_length + 1):  # +1 because burst_length is 0-based
            if i < len(addresses):
                addr = addresses[i]

                # Read data from memory model if available
                data = 0
                if self.memory_model:
                    try:
                        # Read from memory
                        data_bytes = self.memory_model.read(addr, bytes_per_beat)
                        data = self.memory_model.bytearray_to_integer(data_bytes)
                        self.log.debug(f"Read from memory: addr=0x{addr:X}, data=0x{data:X}")
                    except Exception as e:
                        self.log.error(f"Error reading from memory: {e}")
                        # Continue with zero data on error

                # Create R channel packet
                from CocoTBFramework.components.axi4.axi4_packet import AXI4Packet

                r_packet = AXI4Packet.create_r_packet(
                    rid=id_value,
                    rdata=data,
                    rresp=0,  # OKAY
                    rlast=1 if i == burst_length else 0,
                    ruser=getattr(ar_transaction, 'aruser', 0) if hasattr(ar_transaction, 'aruser') else 0
                )

                # Send through R master
                await self.r_master.send(r_packet)

                self.log.debug(f"Sent read response: ID={id_value}, ADDR=0x{addr:X}, DATA=0x{data:X}, LAST={1 if i == burst_length else 0}")

                # Update transaction state
                transaction['beats_completed'] += 1

        # If all beats sent, remove from pending
        if transaction['beats_completed'] >= burst_length + 1:
            del self.pending_transactions[id_value]
            self.log.info(f"Completed read transaction: ID={id_value}")


class AXI4WriteCommandHandler:
    """
    Command handler for AXI4 Write operations.

    This class coordinates the flow between AW channel (address write), W channel (write data),
    and B channel (write response).
    """

    def __init__(self, aw_slave, w_slave, b_master, memory_model=None, log=None):
        """
        Initialize AXI4 Write Command Handler.

        Args:
            aw_slave: AXI4 AW channel slave component that receives write addresses
            w_slave: AXI4 W channel slave component that receives write data
            b_master: AXI4 B channel master component that returns write responses
            memory_model: Optional memory model for data storage (if None, will use aw_slave's model)
            log: Logger instance
        """
        self.aw_slave = aw_slave
        self.w_slave = w_slave
        self.b_master = b_master
        self.memory_model = memory_model or aw_slave.memory_model
        self.log = log or aw_slave.log

        # Task handle
        self.processor_task = None
        self.running = False

        # Transaction tracking
        self.pending_transactions = {}

    async def start(self):
        """Start command handler processor task."""
        if not self.running:
            self.running = True
            self.processor_task = cocotb.start_soon(self._process_requests())
            self.log.info("AXI4WriteCommandHandler started")

    async def stop(self):
        """Stop command handler processor task."""
        self.running = False
        if self.processor_task:
            await Timer(10, units='ns')  # Allow task to complete
            self.processor_task = None
            self.log.info("AXI4WriteCommandHandler stopped")

    async def _process_requests(self):
        """
        Process write requests from AW/W slaves and generate responses through B master.
        """
        clock = self.aw_slave.clock

        while self.running:
            # Process AW transactions
            await self._process_aw_transactions()

            # Process W transactions
            await self._process_w_transactions()

            # Check for completed transactions
            await self._send_write_responses()

            # Wait before checking again
            await RisingEdge(clock)

    async def _process_aw_transactions(self):
        """Process address write transactions from AW slave."""
        # Check for new AW transactions
        if (
            not hasattr(self.aw_slave, 'aw_slave')
            or not self.aw_slave.aw_slave.received_queue
        ):
            return
        # Get the AW transaction
        aw_transaction = self.aw_slave.aw_slave.received_queue.popleft()

        # Extract key information
        if hasattr(aw_transaction, 'awid'):
            id_value = aw_transaction.awid
            addr = aw_transaction.awaddr
            burst_length = aw_transaction.awlen if hasattr(aw_transaction, 'awlen') else 0
            burst_size = aw_transaction.awsize if hasattr(aw_transaction, 'awsize') else 0
            burst_type = aw_transaction.awburst if hasattr(aw_transaction, 'awburst') else 1  # INCR

            # Calculate addresses for burst
            addresses = aw_transaction.get_burst_addresses() if hasattr(aw_transaction, 'get_burst_addresses') else [addr]

            # Store in pending transactions
            self.pending_transactions[id_value] = {
                'aw_transaction': aw_transaction,
                'addresses': addresses,
                'burst_length': burst_length,
                'burst_size': burst_size,
                'burst_type': burst_type,
                'w_transactions': [],
                'complete': False
            }

            self.log.info(f"Received write address: ID={id_value}, ADDR=0x{addr:X}, LEN={burst_length}")

    async def _process_w_transactions(self):
        """Process write data transactions from W slave."""
        # Check for W transactions
        if (
            not hasattr(self.w_slave, 'w_slave')
            or not self.w_slave.w_slave.received_queue
        ):
            return
        # Try to match with pending AW transactions
        w_transaction = self.w_slave.w_slave.received_queue[0]  # Peek

        # Find matching AW transaction (simple model: assumes in-order processing)
        for id_value, transaction in self.pending_transactions.items():
            if len(transaction['w_transactions']) <= transaction['burst_length']:
                # Add this W transaction to the pending transaction
                transaction['w_transactions'].append(w_transaction)

                # Remove from queue
                self.w_slave.w_slave.received_queue.popleft()

                # Check if last beat
                if hasattr(w_transaction, 'wlast') and w_transaction.wlast:
                    transaction['complete'] = True

                # Check if all expected beats received
                if len(transaction['w_transactions']) > transaction['burst_length']:
                    transaction['complete'] = True

                # Write to memory if available
                if self.memory_model and transaction['complete']:
                    self._write_to_memory(transaction)

                self.log.debug(f"Matched write data to ID={id_value}, beats={len(transaction['w_transactions'])}/{transaction['burst_length']+1}")
                break

    def _write_to_memory(self, transaction):
        """Write transaction data to memory model."""
        if not self.memory_model:
            return

        addresses = transaction['addresses']
        w_transactions = transaction['w_transactions']

        # For each beat in the burst
        for i, w_transaction in enumerate(w_transactions):
            if i < len(addresses):
                addr = addresses[i]
                data = w_transaction.wdata
                strb = w_transaction.wstrb if hasattr(w_transaction, 'wstrb') else 0xFF

                try:
                    # Convert data to bytearray
                    data_bytes = self.memory_model.integer_to_bytearray(data, self.memory_model.bytes_per_line)

                    # Write to memory
                    self.memory_model.write(addr, data_bytes, strb)
                    self.log.debug(f"Write to memory: addr=0x{addr:X}, data=0x{data:X}, strb=0x{strb:X}")
                except Exception as e:
                    self.log.error(f"Error writing to memory: {e}")

    async def _send_write_responses(self):
        """Send write responses for completed transactions."""
        # Check for completed transactions
        completed_ids = []

        for id_value, transaction in self.pending_transactions.items():
            if transaction['complete']:
                # Send B response
                from CocoTBFramework.components.axi4.axi4_packet import AXI4Packet

                aw_transaction = transaction['aw_transaction']

                b_packet = AXI4Packet.create_b_packet(
                    bid=id_value,
                    bresp=0,  # OKAY
                    buser=getattr(aw_transaction, 'awuser', 0) if hasattr(aw_transaction, 'awuser') else 0
                )

                # Send through B master
                await self.b_master.send(b_packet)

                self.log.info(f"Sent write response: ID={id_value}")

                # Mark for removal
                completed_ids.append(id_value)

        # Remove completed transactions
        for id_value in completed_ids:
            del self.pending_transactions[id_value]
