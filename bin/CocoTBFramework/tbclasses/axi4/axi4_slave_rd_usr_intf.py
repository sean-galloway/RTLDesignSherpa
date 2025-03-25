"""
AXI4 Slave Read Memory Interface

This module provides a testbench interface for the memory side
of the AXI4 Slave Read module, specifically focusing on the s_axi interfaces
through which the slave module connects to a memory backend.
"""

from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.components.axi4.axi4_factories import (
    create_axi4_monitor
)
from CocoTBFramework.components.memory_model import MemoryModel


class Axi4SlaveRdMemIntf(TBBase):
    """
    Interface for the memory side of the AXI4 Slave Read module.
    This class handles interaction with the memory model connected
    to the AXI slave, verifying read transactions against expected patterns.
    """

    def __init__(self, dut, memory_model=None):
        """
        Initialize the AXI4 Slave Read Memory Interface.

        Args:
            dut: Device under test
            memory_model: Optional memory model for backing storage (will create one if None)
        """
        super().__init__(dut)

        # Extract parameters from the DUT or use defaults
        self.id_width = int(getattr(dut, 'AXI_ID_WIDTH', 8))
        self.addr_width = int(getattr(dut, 'AXI_ADDR_WIDTH', 32))
        self.data_width = int(getattr(dut, 'AXI_DATA_WIDTH', 32))
        self.user_width = int(getattr(dut, 'AXI_USER_WIDTH', 1))

        # Calculate strobe width
        self.strb_width = self.data_width // 8

        # Create memory model if not provided
        if memory_model is None:
            self.memory_model = MemoryModel(
                num_lines=32768,  # 128K memory
                bytes_per_line=self.strb_width,
                log=self.log
            )
            self.owns_memory_model = True
        else:
            self.memory_model = memory_model
            self.owns_memory_model = False
            
        # Create monitors for the slave interface to the memory
        self.s_axi_monitor = create_axi4_monitor(
            dut, "S_AXI_Monitor",
            prefix='s_axi',
            divider='',
            suffix='',
            clock=dut.aclk,
            channels=['ar', 'r'],
            id_width=self.id_width,
            addr_width=self.addr_width,
            data_width=self.data_width,
            user_width=self.user_width,
            is_slave_side=True,
            log=self.log
        )

        # Connect monitor to callbacks for tracking transactions
        self.s_axi_monitor.set_read_callback(self._handle_s_axi_read)

        # Expected read and error patterns
        self.expected_reads = {}     # Expected read transactions
        self.expected_errors = {}    # Expected error responses
        
        # Error and delay settings
        self.error_mode = False      # Generate error responses if True
        self.delay_mode = False      # Introduce delays in responses if True
        self.delay_cycles = 0        # Number of cycles to delay responses
        
        # Verification data
        self.total_errors = 0

    async def reset_interfaces(self):
        """Reset the interfaces and clear tracking data."""
        # Clear expected transaction tracking
        self.expected_reads.clear()
        self.expected_errors.clear()
        
        # Reset verification data
        self.total_errors = 0
        
        # Reset error and delay modes
        self.error_mode = False
        self.delay_mode = False
        self.delay_cycles = 0
        
        self.log.info("Memory interface reset")
        
    def _handle_s_axi_read(self, id_value, transaction):
        """
        Process a read transaction from the slave AXI interface.

        Args:
            id_value: Transaction ID
            transaction: Transaction information
        """
        # Log detected transaction
        if 'ar_transaction' in transaction:
            self.log.debug(f"Memory interface detected AR transaction: ID={id_value:X}, addr=0x{transaction['ar_transaction'].araddr:X}")

        # Verify against expected reads if transaction is complete
        if transaction.get('complete', False):
            # Collect response data
            data = [r.rdata for r in transaction.get('r_transactions', []) if hasattr(r, 'rdata')]

            # Check if this was an expected read
            if id_value in self.expected_reads:
                expected = self.expected_reads[id_value]
                expected_data = expected.get('data', [])

                # Compare data lengths
                if len(data) != len(expected_data):
                    self.log.error(f"Data length mismatch for ID={id_value:X}: expected={len(expected_data)}, received={len(data)}")
                    self.total_errors += 1
                else:
                    # Compare each data beat
                    for i, (exp, act) in enumerate(zip(expected_data, data)):
                        if exp != act:
                            self.log.error(f"Data mismatch for ID={id_value:X} at beat {i}: expected=0x{exp:X}, received=0x{act:X}")
                            self.total_errors += 1
                            break
                    else:
                        self.log.info(f"Read data verified for ID={id_value:X}: all {len(data)} beats match")

                # Mark as processed
                self.expected_reads[id_value]['processed'] = True

            elif id_value in self.expected_errors:
                # Check for error responses
                all_error_responses = all(
                    hasattr(r, 'rresp') and r.rresp in [2, 3]
                    for r in transaction.get('r_transactions', [])
                )

                if all_error_responses:
                    self.log.info(f"Verified error responses for ID={id_value:X}")
                else:
                    self.log.error(f"Expected error responses for ID={id_value:X}, but received normal responses")
                    self.total_errors += 1

                # Mark as processed
                self.expected_errors[id_value]['processed'] = True

            else:
                self.log.warning(f"Received unexpected read transaction: ID={id_value:X}")
                        
    async def initialize_memory_pattern(self):
        """Initialize memory with a test pattern (address + 0xA5A5A5A5)."""
        # Use a simple pattern: address + 0xA5A5A5A5
        for addr in range(0, 32768 * self.strb_width, self.strb_width):
            value = (addr + 0xA5A5A5A5) & ((1 << (8 * self.strb_width)) - 1)
            data_bytes = self.memory_model.integer_to_bytearray(value, self.strb_width)
            self.memory_model.write(addr, data_bytes, 0xFF)  # All bytes enabled

        self.log.info(f"Memory initialized with pattern: addr + 0xA5A5A5A5")
        
    def expect_read(self, addr, length, id_value, data=None):
        """
        Register an expected read transaction.

        Args:
            addr: Address to read from
            length: Burst length
            id_value: Transaction ID
            data: Optional expected data (calculated from pattern if None)
        """
        # Calculate expected data if not provided
        if data is None:
            data = []
            for i in range(length + 1):
                beat_addr = addr + (i * self.strb_width)
                beat_data = (beat_addr + 0xA5A5A5A5) & ((1 << (8 * self.strb_width)) - 1)
                data.append(beat_data)
                
        # Register expected transaction
        self.expected_reads[id_value] = {
            'addr': addr,
            'length': length,
            'data': data,
            'processed': False
        }
        
        self.log.debug(f"Registered expected read: ID={id_value:X}, addr=0x{addr:08X}, length={length}")
        
    def expect_error_read(self, addr, length, id_value):
        """
        Register an expected error read transaction.

        Args:
            addr: Address to read from
            length: Burst length
            id_value: Transaction ID
        """
        # Register expected error transaction
        self.expected_errors[id_value] = {
            'addr': addr,
            'length': length,
            'processed': False
        }
        
        self.log.debug(f"Registered expected error read: ID={id_value:X}, addr=0x{addr:08X}, length={length}")
        
    def set_error_mode(self, enable, error_rate=1.0):
        """
        Enable or disable error response mode.

        Args:
            enable: True to enable error mode, False to disable
            error_rate: Probability of generating an error response (0.0-1.0)
        """
        self.error_mode = enable
        self.error_rate = error_rate
        self.log.info(f"Error mode {'enabled' if enable else 'disabled'}, rate={error_rate}")
        
    def set_delay_mode(self, enable, delay_cycles=0):
        """
        Enable or disable delay mode for responses.

        Args:
            enable: True to enable delay mode, False to disable
            delay_cycles: Number of clock cycles to delay responses
        """
        self.delay_mode = enable
        self.delay_cycles = delay_cycles
        self.log.info(f"Delay mode {'enabled' if enable else 'disabled'}, cycles={delay_cycles}")
        
    def verify_all_processed(self):
        """
        Verify that all expected transactions have been processed.

        Returns:
            True if all transactions processed, False otherwise
        """
        if unprocessed_reads := [
            id_value
            for id_value, info in self.expected_reads.items()
            if not info.get('processed', False)
        ]:
            return self._helper_verify_all_processed_13(
                'Unprocessed expected reads: ', unprocessed_reads
            )
        # Check for unprocessed expected errors
        unprocessed_errors = [
            id_value for id_value, info in self.expected_errors.items()
            if not info.get('processed', False)
        ]

        if unprocessed_errors:
            return self._helper_verify_all_processed_13(
                'Unprocessed expected error reads: ', unprocessed_errors
            )
        return True

    # TODO Rename this here and in `verify_all_processed`
    def _helper_verify_all_processed_13(self, arg0, arg1):
        self.log.error(f"{arg0}{arg1}")
        self.total_errors += len(arg1)
        return False
