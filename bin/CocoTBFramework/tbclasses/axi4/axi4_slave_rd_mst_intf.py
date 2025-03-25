"""
AXI4 Slave Read Master Interface

This module provides a testbench interface for the master-facing ports
of the AXI4 Slave Read module, specifically focusing on the m_axi interfaces
for read transactions.
"""

from enum import IntFlag
import cocotb
from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.components.axi4.axi4_factories import (
    create_axi4_master, create_axi4_monitor
)
from CocoTBFramework.components.flex_randomizer import FlexRandomizer

# Error type definitions
class ErrorType(IntFlag):
    """Error types for AXI4 slave read module"""
    AR_TIMEOUT = 0b0001  # Bit 0: Address Read timeout
    R_TIMEOUT = 0b0010   # Bit 1: Read Data timeout
    R_RESP_ERROR = 0b0100  # Bit 2: Read response error (SLVERR, DECERR)


class Axi4SlaveRdMasterIntf(TBBase):
    """
    Interface for the master-facing ports of the AXI4 Slave Read module.
    This class handles the m_axi interfaces through which the slave module
    receives read requests and sends read data responses.
    """

    def __init__(self, dut):
        """
        Initialize the AXI4 Slave Read Master Interface.

        Args:
            dut: Device under test
        """
        super().__init__(dut)

        # Extract parameters from the DUT or use defaults
        self.id_width = int(getattr(dut, 'AXI_ID_WIDTH', 8))
        self.addr_width = int(getattr(dut, 'AXI_ADDR_WIDTH', 32))
        self.data_width = int(getattr(dut, 'AXI_DATA_WIDTH', 32))
        self.user_width = int(getattr(dut, 'AXI_USER_WIDTH', 1))
        self.timeout_ar = int(getattr(dut, 'TIMEOUT_AR', 1000))
        self.timeout_r = int(getattr(dut, 'TIMEOUT_R', 1000))

        # Calculate strobe width
        self.strb_width = self.data_width // 8

        # Calculate size parameter based on data width
        self.dsize = 0  # Default to byte access
        temp_width = self.data_width // 8  # Convert to bytes
        while temp_width > 1:
            temp_width >>= 1
            self.dsize += 1

        # Create randomizers for different test scenarios
        self.randomizers = self._create_randomizers()
        channels = ['ar', 'r']

        # Create AXI4 master component for the master interface (m_axi_*)
        self.m_axi_master = create_axi4_master(
            dut, "M_AXI_Master",
            prefix='m_axi',
            divider='',
            suffix='',
            clock=dut.aclk,
            channels=channels,
            id_width=self.id_width,
            addr_width=self.addr_width,
            data_width=self.data_width,
            user_width=self.user_width,
            randomizers={'ar': self.randomizers['ar_fast']},
            log=self.log
        )

        # Create monitor for the master interface
        self.m_axi_monitor = create_axi4_monitor(
            dut, "M_AXI_Monitor",
            prefix='m_axi',
            divider='',
            suffix='',
            clock=dut.aclk,
            channels=channels,
            id_width=self.id_width,
            addr_width=self.addr_width,
            data_width=self.data_width,
            user_width=self.user_width,
            is_slave_side=False,
            log=self.log
        )

        # Connect monitor to callbacks for tracking transactions
        self.m_axi_monitor.set_read_callback(self._handle_m_axi_read)

        # Transaction tracking
        self.pending_reads = {}    # Reads sent to DUT, awaiting response
        self.completed_reads = {}  # Completed read transactions
        
        # Error monitoring
        self.detected_errors = []  # List of detected errors

        # ID counter for generating unique transaction IDs
        self.next_id = 0

        # Verification data
        self.total_errors = 0
        
    def _handle_m_axi_read(self, id_value, transaction):
        """
        Process a read transaction from the master AXI interface.

        Args:
            id_value: Transaction ID
            transaction: Transaction information
        """
        if id_value in self.pending_reads:
            # Store the response
            self.pending_reads[id_value]['response'] = transaction
            
            # Mark as complete if it has the 'complete' flag
            if transaction.get('complete', False):
                self.pending_reads[id_value]['complete'] = True
                self.completed_reads[id_value] = self.pending_reads[id_value]
                self.log.info(f"Read transaction completed: ID={id_value:X}, beats={len(transaction.get('r_transactions', []))}")
                
    def _get_next_id(self):
        """
        Get the next available transaction ID.

        Returns:
            Next available ID value
        """
        id_value = self.next_id
        self.next_id = (self.next_id + 1) % (1 << self.id_width)
        return id_value

    async def reset_interfaces(self):
        """Reset the AXI4 interfaces."""
        # Reset the AXI components
        await self.m_axi_master.reset_bus()

        # Clear tracking data
        self.pending_reads.clear()
        self.completed_reads.clear()
        self.detected_errors.clear()

        # Reset ID counter
        self.next_id = 0

        # Reset verification data
        self.total_errors = 0

        self.log.info("AXI4 interfaces reset")
        
    def set_m_axi_ar_timing(self, mode):
        """
        Set the timing mode for the master AXI AR channel.

        Args:
            mode: One of 'fixed', 'always_ready', 'fast', 'slow', 'timeout'
        """
        randomizer_key = f'ar_{mode}'
        if randomizer_key in self.randomizers:
            self.m_axi_master.ar_master.set_randomizer(self.randomizers[randomizer_key])
            self.log.info(f"M_AXI AR channel timing set to {mode}")
        else:
            self.log.error(f"Unknown AR timing mode: {mode}")

    def set_m_axi_r_timing(self, mode):
        """
        Set the timing mode for the master AXI R channel.

        Args:
            mode: One of 'fixed', 'always_ready', 'fast', 'slow', 'timeout'
        """
        randomizer_key = f'r_{mode}'
        if randomizer_key in self.randomizers:
            self.m_axi_master.r_slave.set_randomizer(self.randomizers[randomizer_key])
            self.log.info(f"M_AXI R channel timing set to {mode}")
        else:
            self.log.error(f"Unknown R timing mode: {mode}")
            
    async def read(self, addr, length=0, size=None, burst=1, id_value=None):
        """
        Execute an AXI4 read transaction.

        Args:
            addr: Target address
            length: Burst length (0=1 beat, 1=2 beats, etc.)
            size: Transfer size (0=byte, 1=halfword, 2=word, 3=doubleword, etc.)
            burst: Burst type (0=FIXED, 1=INCR, 2=WRAP)
            id_value: Optional specific ID to use (None for auto-generated)

        Returns:
            Dict with transaction data or None if error
        """
        # Use default size if not specified
        if size is None:
            size = self.dsize
            
        # Generate ID if not provided
        if id_value is None:
            id_value = self._get_next_id()
            
        # Create tracking entry
        self.pending_reads[id_value] = {
            'addr': addr,
            'length': length,
            'size': size,
            'burst': burst,
            'start_time': cocotb.utils.get_sim_time('ns'),
            'complete': False
        }
            
        # Log the transaction
        self.log.info(f"Sending read request: ID={id_value:X}, addr=0x{addr:08X}, length={length}")
        
        try:
            # Send the read request through the master interface
            result = await self.m_axi_master.read(
                addr=addr,
                size=size,
                burst=burst,
                id=id_value,
                length=length
            )
            
            # Store the result
            if result:
                # Update tracking entry
                self.pending_reads[id_value].update({
                    'data': result.get('data', []),
                    'responses': result.get('responses', []),
                    'end_time': cocotb.utils.get_sim_time('ns'),
                    'duration': result.get('duration', 0),
                    'complete': True,
                    'id': id_value
                })
                
                # Move to completed reads
                self.completed_reads[id_value] = self.pending_reads[id_value]
                
                return self.completed_reads[id_value]
            else:
                self.log.error(f"Read transaction failed: ID={id_value:X}, addr=0x{addr:08X}")
                self.total_errors += 1
                return None
                
        except Exception as e:
            self.log.error(f"Exception during read transaction: {str(e)}")
            self.total_errors += 1
            return None
            
    def check_for_error(self, error_type):
        """
        Check if a specific error type has been detected.

        Args:
            error_type: Error type to check for

        Returns:
            True if the error has been detected, False otherwise
        """
        return any(e == error_type for e in self.detected_errors)
        
    def add_detected_error(self, error_type):
        """
        Add a detected error to the tracking list.

        Args:
            error_type: Error type that was detected
        """
        self.detected_errors.append(error_type)
        self.log.info(f"Error detected: {ErrorType(error_type).name}")
        
    def get_transaction_status(self, id_value):
        """
        Get the status of a transaction.

        Args:
            id_value: Transaction ID

        Returns:
            Dict with transaction status or None if not found
        """
        if id_value in self.completed_reads:
            return {
                'state': 'completed',
                'data': self.completed_reads[id_value]
            }
        elif id_value in self.pending_reads:
            return {
                'state': 'pending',
                'data': self.pending_reads[id_value]
            }
        else:
            return None

    def _create_randomizers(self):
        """Create timing randomizers for different test scenarios."""
        randomizers = {}

        fixed = 2

        # AR channel randomizers for m_axi interface
        randomizers['ar_always_ready'] = FlexRandomizer({
            'valid_delay': ([[0, 0]], [1.0])
        })

        randomizers['ar_fixed'] = FlexRandomizer({
            'valid_delay': ([[fixed, fixed]], [1.0])
        })

        randomizers['ar_fast'] = FlexRandomizer({
            'valid_delay': ([[0, 0], [1, 3]], [0.8, 0.2])
        })

        randomizers['ar_slow'] = FlexRandomizer({
            'valid_delay': ([[0, 0], [1, 10], [11, 20]], [0.2, 0.5, 0.3])
        })

        # R channel randomizers for m_axi interface
        randomizers['r_always_ready'] = FlexRandomizer({
            'ready_delay': ([[0, 0]], [1.0])
        })

        randomizers['r_fixed'] = FlexRandomizer({
            'ready_delay': ([[fixed, fixed]], [1.0])
        })

        randomizers['r_fast'] = FlexRandomizer({
            'ready_delay': ([[0, 0], [1, 3]], [0.8, 0.2])
        })

        randomizers['r_slow'] = FlexRandomizer({
            'ready_delay': ([[0, 0], [1, 10], [11, 20]], [0.2, 0.5, 0.3])
        })

        # Special randomizers for timeout testing
        # AR timeout testing - delays longer than timeout
        randomizers['ar_timeout'] = FlexRandomizer({
            'valid_delay': ([[0, 0], [self.timeout_ar, self.timeout_ar * 2]], [0.2, 0.8])
        })

        # R timeout testing - delays longer than timeout
        randomizers['r_timeout'] = FlexRandomizer({
            'ready_delay': ([[0, 0], [self.timeout_r, self.timeout_r * 2]], [0.2, 0.8])
        })

        return randomizers
