"""
Enhanced GAXI Master and Slave Components

These enhanced components provide higher-level functionality by wrapping
the basic GAXI master/slave components.
"""
import cocotb
from cocotb.triggers import RisingEdge, Timer
from collections import deque

class EnhancedGAXIMaster:
    """
    Enhanced GAXI Master Component

    Wraps a basic GAXIMaster to provide higher-level functionality:
    - Direct memory read/write methods
    - Support for automated address sequencing
    - Integration with memory model
    - Command interface to coordinate with slave responses
    """

    def __init__(self, master, memory_model=None, log=None):
        """
        Initialize enhanced GAXI master.

        Args:
            master: Base GAXIMaster instance to wrap
            memory_model: Optional memory model for data storage
            log: Logger instance
        """
        self.master = master
        self.memory_model = memory_model or master.memory_model
        self.log = log or master.log
        self.field_config = master.field_config
        self.packet_class = master.packet_class

        # Command processor task
        self.processor_task = None
        self.response_queue = deque()
        self.command_queue = deque()
        self.running = False

    async def reset_bus(self):
        """Reset the master and clear queues."""
        await self.master.reset_bus()
        self.command_queue.clear()
        self.response_queue.clear()

    async def send(self, packet):
        # sourcery skip: hoist-statement-from-if, reintroduce-else
        """
        Send a packet through the master.

        Args:
            packet: Packet to send

        Returns:
            Response packet for read operations, None for writes
        """
        # For writes with memory model, update memory
        if packet.cmd == 1 and self.memory_model:  # Write
            addr = packet.addr
            data = packet.data

            # Convert to bytes for memory model
            data_bytes = self.memory_model.integer_to_bytearray(data, self.memory_model.bytes_per_line)
            strb = packet.strb if hasattr(packet, 'strb') else 0xFF
            # Write to memory model
            self.memory_model.write(addr, data_bytes, strb)
            self.log.debug(f"EnhancedGAXIMaster: Write to memory addr=0x{addr:08X}, data=0x{data:08X}")

        # Send through base master
        await self.master.send(packet)

        # For reads, return response
        if packet.cmd == 0:  # Read
            # Create a future to wait for the response
            # In real implementation, this would be more sophisticated,
            # connecting to the slave response queue
            return None  # Placeholder

        return None

    async def read(self, addr):  # sourcery skip: assign-if-exp, reintroduce-else
        """
        Read data from specified address.

        Args:
            addr: Address to read from

        Returns:
            Data read from address
        """
        # Create read packet
        packet = self.packet_class(self.field_config)
        packet.cmd = 0  # Read
        packet.addr = addr

        # If we have a memory model, read directly
        if self.memory_model:
            # Read from memory model
            data_bytes = self.memory_model.read(addr, self.memory_model.bytes_per_line)
            data = self.memory_model.bytearray_to_integer(data_bytes)
            packet.data = data
            self.log.debug(f"EnhancedGAXIMaster: Read from memory addr=0x{addr:08X}, data=0x{data:08X}")

        # Send through base master
        await self.master.send(packet)

        # In a real implementation, we would wait for the response
        # For now, if we have a memory model, return the data
        if self.memory_model:
            return packet.data

        return None

    async def write(self, addr, data, strb=None):
        """
        Write data to specified address.

        Args:
            addr: Address to write to
            data: Data to write
            strb: Byte strobe mask (default: all bytes enabled)

        Returns:
            None
        """
        # Create write packet
        packet = self.packet_class(self.field_config)
        packet.cmd = 1  # Write
        packet.addr = addr
        packet.data = data

        # Set strobe if provided and supported
        if strb is not None and 'strb' in self.field_config:
            packet.strb = strb

        # Send through base master
        await self.send(packet)

    async def start_processor(self):
        """Start command processor task."""
        if self.processor_task is None:
            self.running = True
            self.processor_task = cocotb.start_soon(self._command_processor())
            self.log.info("EnhancedGAXIMaster: Command processor started")

    async def stop_processor(self):
        """Stop command processor task."""
        self.running = False
        if self.processor_task is not None:
            await Timer(10, units='ns')  # Allow task to complete
            self.processor_task = None
            self.log.info("EnhancedGAXIMaster: Command processor stopped")

    async def _command_processor(self):
        """Command processor background task."""
        self.log.debug("EnhancedGAXIMaster: Command processor running")

        while self.running:
            # Check for commands to process
            if self.command_queue:
                cmd = self.command_queue.popleft()

                # Process command
                if cmd['type'] == 'read':
                    await self.read(cmd['addr'])
                elif cmd['type'] == 'write':
                    await self.write(cmd['addr'], cmd['data'], cmd.get('strb'))

                # Log command execution
                self.log.debug(f"EnhancedGAXIMaster: Processed command {cmd['type']} addr=0x{cmd['addr']:08X}")

            # Wait a bit before checking again
            await Timer(100, units='ps')


class EnhancedGAXISlave:
    """
    Enhanced GAXI Slave Component

    Wraps a basic GAXISlave to provide higher-level functionality:
    - Automatic processing of incoming transactions
    - Integration with memory model for data storage/retrieval
    - Response queue management
    - Support for custom processing callbacks
    """

    def __init__(self, slave, memory_model=None, log=None):
        """
        Initialize enhanced GAXI slave.

        Args:
            slave: Base GAXISlave instance to wrap
            memory_model: Optional memory model for data storage
            log: Logger instance
        """
        self.slave = slave
        self.memory_model = memory_model or slave.memory_model
        self.log = log or slave.log
        self.field_config = slave.field_config
        self.packet_class = slave.packet_class

        # Processor task
        self.processor_task = None
        self.running = False

        # Callbacks for custom processing
        self.read_callback = None
        self.write_callback = None

    async def reset_bus(self):
        """Reset the slave."""
        await self.slave.reset_bus()

    def set_read_callback(self, callback):
        """
        Set callback for custom read processing.

        Args:
            callback: Function to call with (addr, packet) arguments
        """
        self.read_callback = callback

    def set_write_callback(self, callback):
        """
        Set callback for custom write processing.

        Args:
            callback: Function to call with (addr, data, packet) arguments
        """
        self.write_callback = callback

    @property
    def received_queue(self):
        """Get the received packet queue from the base slave."""
        return self.slave.received_queue

    async def start_processor(self):
        """Start automatic transaction processor."""
        if self.processor_task is None:
            self.running = True
            self.processor_task = cocotb.start_soon(self._transaction_processor())
            self.log.info("EnhancedGAXISlave: Transaction processor started")

    async def stop_processor(self):
        """Stop automatic transaction processor."""
        self.running = False
        if self.processor_task is not None:
            await Timer(10, units='ns')  # Allow task to complete
            self.processor_task = None
            self.log.info("EnhancedGAXISlave: Transaction processor stopped")

    async def _transaction_processor(self):
        """
        Process incoming transactions automatically.

        For reads: Read from memory model or call custom callback
        For writes: Write to memory model or call custom callback
        """
        self.log.debug("EnhancedGAXISlave: Transaction processor running")

        while self.running:
            # Check if we have received packets to process
            if self.slave.received_queue:
                packet = self.slave.received_queue.popleft()

                addr = packet.addr

                if packet.cmd == 0:  # Read
                    # Handle read operation
                    if self.read_callback:
                        # Custom processing
                        self.read_callback(addr, packet)
                    elif self.memory_model:
                        # Default memory model processing
                        data_bytes = self.memory_model.read(addr, self.memory_model.bytes_per_line)
                        data = self.memory_model.bytearray_to_integer(data_bytes)
                        packet.data = data
                        self.log.debug(f"EnhancedGAXISlave: Read addr=0x{addr:08X}, data=0x{data:08X}")

                elif packet.cmd == 1:  # Write
                    data = packet.data
                    strb = 0xFF  # Default to all bytes enabled
                    if hasattr(packet, 'strb'):
                        strb = packet.strb

                    # Handle write operation
                    if self.write_callback:
                        # Custom processing
                        self.write_callback(addr, data, packet)
                    elif self.memory_model:
                        # Default memory model processing
                        data_bytes = self.memory_model.integer_to_bytearray(data, self.memory_model.bytes_per_line)
                        self.memory_model.write(addr, data_bytes, strb)
                        self.log.debug(f"EnhancedGAXISlave: Write addr=0x{addr:08X}, data=0x{data:08X}")

            # Wait before checking again
            await Timer(10, units='ns')


class GAXICommandHandler_APBSlave:
    """
    Simplified Command Handler for APB slave command/response interfaces

    This component:
    1. Takes packets from the GAXI command slave
    2. Creates appropriate response packets
    3. Sends them through the GAXI response master
    """

    def __init__(self, gaxi_master, gaxi_slave, cmd_field_config=None, rsp_field_config=None, log=None):
        """
        Initialize GAXI command handler for APB slave.

        Args:
            gaxi_master: GAXI response master for sending responses
            gaxi_slave: GAXI command slave for receiving commands
            cmd_field_config: Field configuration for command packets
            rsp_field_config: Field configuration for response packets
            log: Logger instance
        """
        self.gaxi_master = gaxi_master
        self.gaxi_slave = gaxi_slave
        self.log = log or gaxi_master.log

        # Store field configurations
        self.cmd_field_config = cmd_field_config or gaxi_slave.field_config
        self.rsp_field_config = rsp_field_config or gaxi_master.field_config

        # Import GAXIPacket here to avoid circular imports
        from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
        self.packet_class = GAXIPacket

        # Task handle
        self.processor_task = None
        self.running = False

        # Memory interface for read operations
        self.memory_model = gaxi_slave.memory_model

        # Response packet mapping
        self.data_field_name = 'data'
        self.err_field_name = 'err' if 'err' in self.rsp_field_config else 'ack'

    async def start(self):
        """Start command handler processor task."""
        if not self.running:
            self.running = True
            self.processor_task = cocotb.start_soon(self._process_commands())
            self.log.info("GAXICommandHandler_APBSlave: Started")

    async def stop(self):
        """Stop command handler processor task."""
        self.running = False
        await Timer(10, units='ns')  # Allow task to complete
        self.processor_task = None
        self.log.info("GAXICommandHandler_APBSlave: Stopped")

    async def _process_commands(self):
        """
        Process command packets from the GAXI slave and send responses
        through the GAXI master.
        """
        clock = self.gaxi_slave.clock

        while self.running:
            # Check if we have a command packet from the slave
            if self.gaxi_slave.received_queue:
                # Get the command packet
                cmd_packet = self.gaxi_slave.received_queue.popleft()

                # Create response packet using response field config
                rsp_packet = self.packet_class(self.rsp_field_config)

                # For reads, ensure we use data from memory if available
                if hasattr(cmd_packet, 'cmd') and cmd_packet.cmd == 0:  # Read
                    if self.memory_model:
                        # Read from memory to ensure consistent data
                        addr = cmd_packet.addr
                        data_bytes = self.memory_model.read(addr & 0xFFF, self.memory_model.bytes_per_line)
                        read_data = self.memory_model.bytearray_to_integer(data_bytes)
                        setattr(rsp_packet, self.data_field_name, read_data)
                        self.log.debug(f"Response using memory data for READ: addr=0x{addr:08X}, data=0x{read_data:08X}")
                    else:
                        # If no memory model, use data from command packet
                        setattr(rsp_packet, self.data_field_name, cmd_packet.data)
                else:  # Write
                    setattr(rsp_packet, self.data_field_name, cmd_packet.data)

                # Set error flag (usually 0)
                setattr(rsp_packet, self.err_field_name, 0)

                # Send through GAXI response master
                await self.gaxi_master.send(rsp_packet)

                self.log.info(f"Processed command and sent response: data=0x{getattr(rsp_packet, self.data_field_name):08X}")

            # Wait a clock cycle before checking again
            await RisingEdge(clock)
