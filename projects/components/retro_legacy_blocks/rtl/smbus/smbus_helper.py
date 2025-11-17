# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: SMBusHelper
# Purpose: Human-readable SMBus register programming helper
#
# Author: sean galloway
# Created: 2025-11-15

"""
SMBus Register Programming Helper

Provides human-readable methods for configuring SMBus registers using the
RegisterMap class with auto-generated register definitions.

Example Usage:
    smbus = SMBusHelper('smbus_regmap.py', apb_data_width=32,
                        apb_addr_width=16, start_address=0x0, log=logger)
    
    # Enable master mode with PEC
    smbus.enable_master(True, pec_enable=True, fast_mode=False)
    
    # Configure for 100kHz operation at 100MHz system clock
    smbus.set_clock_divider(249)  # 100MHz / (4 * (249+1)) = 100kHz
    
    # Write byte to slave
    smbus.write_byte_data(slave_addr=0x50, command=0x10, data=0xAB)
    
    # Read word from slave
    smbus.read_word_data(slave_addr=0x50, command=0x20)
    
    # Generate APB cycles
    apb_transactions = smbus.generate_apb_cycles()
"""

from typing import List, Dict, Tuple, Optional
from bin.CocoTBFramework.tbclasses.apb.register_map import RegisterMap
from bin.CocoTBFramework.components.apb.apb_packet import APBPacket


class SMBusHelper:
    """
    SMBus Register Programming Helper
    
    Provides intuitive methods for programming SMBus registers without
    needing to know the low-level register/field names.
    """
    
    # Transaction type definitions (matching RTL)
    TRANS_QUICK_CMD = 0
    TRANS_SEND_BYTE = 1
    TRANS_RECV_BYTE = 2
    TRANS_WRITE_BYTE = 3
    TRANS_READ_BYTE = 4
    TRANS_WRITE_WORD = 5
    TRANS_READ_WORD = 6
    TRANS_BLOCK_WRITE = 7
    TRANS_BLOCK_READ = 8
    TRANS_BLOCK_PROC = 9
    
    def __init__(self, regmap_file: str, apb_data_width: int,
                 apb_addr_width: int, start_address: int, log):
        """
        Initialize SMBus helper with register map.
        
        Args:
            regmap_file: Path to generated register map file (e.g., 'smbus_regmap.py')
            apb_data_width: APB bus data width (typically 32)
            apb_addr_width: APB bus address width
            start_address: Base address of SMBus in memory map
            log: Logger instance
        """
        self.reg_map = RegisterMap(regmap_file, apb_data_width,
                                   apb_addr_width, start_address, log)
        self.log = log
        
    def enable_master(self, enable: bool = True, pec_enable: bool = False,
                     fast_mode: bool = False):
        """
        Enable or disable SMBus master mode.
        
        Args:
            enable: True to enable master mode
            pec_enable: True to enable Packet Error Checking
            fast_mode: True for 400kHz fast mode, False for 100kHz standard
        """
        self.reg_map.write('SMBUS_CONTROL', 'master_en', 1 if enable else 0)
        self.reg_map.write('SMBUS_CONTROL', 'pec_en', 1 if pec_enable else 0)
        self.reg_map.write('SMBUS_CONTROL', 'fast_mode', 1 if fast_mode else 0)
        
        speed_str = "400kHz" if fast_mode else "100kHz"
        pec_str = "PEC enabled" if pec_enable else "PEC disabled"
        self.log.info(f"Master mode {'enabled' if enable else 'disabled'} ({speed_str}, {pec_str})")
        
    def enable_slave(self, enable: bool = True, own_address: int = 0x00):
        """
        Enable or disable SMBus slave mode.
        
        Args:
            enable: True to enable slave mode
            own_address: 7-bit slave address for this device
        """
        self.reg_map.write('SMBUS_CONTROL', 'slave_en', 1 if enable else 0)
        self.reg_map.write('SMBUS_OWN_ADDR', 'own_addr', own_address & 0x7F)
        self.reg_map.write('SMBUS_OWN_ADDR', 'addr_en', 1 if enable else 0)
        
        self.log.info(f"Slave mode {'enabled' if enable else 'disabled'} " +
                     f"(own address: 0x{own_address:02X})")
        
    def set_clock_divider(self, divider: int):
        """
        Set SCL clock divider.
        
        SCL frequency = sys_clk / (4 * (divider + 1))
        For 100MHz system clock:
          - 100kHz: divider = 249 (100MHz / (4 * 250) = 100kHz)
          - 400kHz: divider = 62 (100MHz / (4 * 63) = 396.8kHz)
        
        Args:
            divider: Clock divider value (0-65535)
        """
        self.reg_map.write('SMBUS_CLK_DIV', 'clk_div', divider & 0xFFFF)
        self.log.info(f"Clock divider set to {divider}")
        
    def set_timeout(self, timeout_cycles: int):
        """
        Set timeout threshold in clock cycles.
        
        SMBus spec requires 25-35ms timeout.
        For 100MHz clock: 2,500,000 to 3,500,000 cycles
        
        Args:
            timeout_cycles: Timeout in system clock cycles (0-16777215)
        """
        self.reg_map.write('SMBUS_TIMEOUT', 'timeout', timeout_cycles & 0xFFFFFF)
        self.log.info(f"Timeout set to {timeout_cycles} cycles")
        
    def quick_command(self, slave_addr: int, rw_bit: int = 0):
        """
        Send SMBus Quick Command.
        
        Args:
            slave_addr: 7-bit slave address
            rw_bit: 0 for write, 1 for read
        """
        self.reg_map.write('SMBUS_SLAVE_ADDR', 'slave_addr', slave_addr & 0x7F)
        self.reg_map.write('SMBUS_COMMAND', 'trans_type', self.TRANS_QUICK_CMD)
        self.reg_map.write('SMBUS_COMMAND', 'start', 1)
        
        self.log.info(f"Quick command to 0x{slave_addr:02X} ({'read' if rw_bit else 'write'})")
        
    def send_byte(self, slave_addr: int, data: int):
        """
        Send single byte (no command code).
        
        Args:
            slave_addr: 7-bit slave address
            data: Data byte to send
        """
        self.reg_map.write('SMBUS_SLAVE_ADDR', 'slave_addr', slave_addr & 0x7F)
        self.reg_map.write('SMBUS_DATA', 'data', data & 0xFF)
        self.reg_map.write('SMBUS_COMMAND', 'trans_type', self.TRANS_SEND_BYTE)
        self.reg_map.write('SMBUS_COMMAND', 'start', 1)
        
        self.log.info(f"Send byte 0x{data:02X} to 0x{slave_addr:02X}")
        
    def receive_byte(self, slave_addr: int):
        """
        Receive single byte (no command code).
        
        Args:
            slave_addr: 7-bit slave address
        """
        self.reg_map.write('SMBUS_SLAVE_ADDR', 'slave_addr', slave_addr & 0x7F)
        self.reg_map.write('SMBUS_COMMAND', 'trans_type', self.TRANS_RECV_BYTE)
        self.reg_map.write('SMBUS_COMMAND', 'start', 1)
        
        self.log.info(f"Receive byte from 0x{slave_addr:02X}")
        
    def write_byte_data(self, slave_addr: int, command: int, data: int):
        """
        Write byte data (command + 1 data byte).
        
        Args:
            slave_addr: 7-bit slave address
            command: Command code byte
            data: Data byte to write
        """
        self.reg_map.write('SMBUS_SLAVE_ADDR', 'slave_addr', slave_addr & 0x7F)
        self.reg_map.write('SMBUS_COMMAND', 'cmd_code', command & 0xFF)
        self.reg_map.write('SMBUS_DATA', 'data', data & 0xFF)
        self.reg_map.write('SMBUS_COMMAND', 'trans_type', self.TRANS_WRITE_BYTE)
        self.reg_map.write('SMBUS_COMMAND', 'start', 1)
        
        self.log.info(f"Write byte 0x{data:02X} to 0x{slave_addr:02X} cmd 0x{command:02X}")
        
    def read_byte_data(self, slave_addr: int, command: int):
        """
        Read byte data (command + 1 data byte).
        
        Args:
            slave_addr: 7-bit slave address
            command: Command code byte
        """
        self.reg_map.write('SMBUS_SLAVE_ADDR', 'slave_addr', slave_addr & 0x7F)
        self.reg_map.write('SMBUS_COMMAND', 'cmd_code', command & 0xFF)
        self.reg_map.write('SMBUS_COMMAND', 'trans_type', self.TRANS_READ_BYTE)
        self.reg_map.write('SMBUS_COMMAND', 'start', 1)
        
        self.log.info(f"Read byte from 0x{slave_addr:02X} cmd 0x{command:02X}")
        
    def write_word_data(self, slave_addr: int, command: int, data: int):
        """
        Write word data (command + 2 data bytes, little-endian).
        
        Args:
            slave_addr: 7-bit slave address
            command: Command code byte
            data: 16-bit data word (little-endian)
        """
        self.reg_map.write('SMBUS_SLAVE_ADDR', 'slave_addr', slave_addr & 0x7F)
        self.reg_map.write('SMBUS_COMMAND', 'cmd_code', command & 0xFF)
        
        # Write low byte first (little-endian)
        self.reg_map.write('SMBUS_TX_FIFO', 'tx_data', data & 0xFF)
        self.reg_map.write('SMBUS_TX_FIFO', 'tx_data', (data >> 8) & 0xFF)
        
        self.reg_map.write('SMBUS_COMMAND', 'trans_type', self.TRANS_WRITE_WORD)
        self.reg_map.write('SMBUS_COMMAND', 'start', 1)
        
        self.log.info(f"Write word 0x{data:04X} to 0x{slave_addr:02X} cmd 0x{command:02X}")
        
    def read_word_data(self, slave_addr: int, command: int):
        """
        Read word data (command + 2 data bytes, little-endian).
        
        Args:
            slave_addr: 7-bit slave address
            command: Command code byte
        """
        self.reg_map.write('SMBUS_SLAVE_ADDR', 'slave_addr', slave_addr & 0x7F)
        self.reg_map.write('SMBUS_COMMAND', 'cmd_code', command & 0xFF)
        self.reg_map.write('SMBUS_COMMAND', 'trans_type', self.TRANS_READ_WORD)
        self.reg_map.write('SMBUS_COMMAND', 'start', 1)
        
        self.log.info(f"Read word from 0x{slave_addr:02X} cmd 0x{command:02X}")
        
    def block_write(self, slave_addr: int, command: int, data_list: List[int]):
        """
        Block write (command + count + N data bytes).
        
        Args:
            slave_addr: 7-bit slave address
            command: Command code byte
            data_list: List of data bytes to write (1-32 bytes)
        """
        if not data_list or len(data_list) > 32:
            raise ValueError("Block write requires 1-32 data bytes")
            
        self.reg_map.write('SMBUS_SLAVE_ADDR', 'slave_addr', slave_addr & 0x7F)
        self.reg_map.write('SMBUS_COMMAND', 'cmd_code', command & 0xFF)
        self.reg_map.write('SMBUS_BLOCK_COUNT', 'block_count', len(data_list))
        
        # Write all data to TX FIFO
        for data_byte in data_list:
            self.reg_map.write('SMBUS_TX_FIFO', 'tx_data', data_byte & 0xFF)
            
        self.reg_map.write('SMBUS_COMMAND', 'trans_type', self.TRANS_BLOCK_WRITE)
        self.reg_map.write('SMBUS_COMMAND', 'start', 1)
        
        self.log.info(f"Block write {len(data_list)} bytes to 0x{slave_addr:02X} cmd 0x{command:02X}")
        
    def block_read(self, slave_addr: int, command: int, expected_count: int = 32):
        """
        Block read (command + count + N data bytes).
        
        Args:
            slave_addr: 7-bit slave address
            command: Command code byte
            expected_count: Expected number of bytes (1-32)
        """
        if expected_count < 1 or expected_count > 32:
            raise ValueError("Block read expects 1-32 data bytes")
            
        self.reg_map.write('SMBUS_SLAVE_ADDR', 'slave_addr', slave_addr & 0x7F)
        self.reg_map.write('SMBUS_COMMAND', 'cmd_code', command & 0xFF)
        self.reg_map.write('SMBUS_BLOCK_COUNT', 'block_count', expected_count)
        self.reg_map.write('SMBUS_COMMAND', 'trans_type', self.TRANS_BLOCK_READ)
        self.reg_map.write('SMBUS_COMMAND', 'start', 1)
        
        self.log.info(f"Block read {expected_count} bytes from 0x{slave_addr:02X} cmd 0x{command:02X}")
        
    def fifo_reset(self):
        """Reset TX and RX FIFOs."""
        self.reg_map.write('SMBUS_CONTROL', 'fifo_reset', 1)
        self.reg_map.write('SMBUS_CONTROL', 'fifo_reset', 0)
        self.log.info("FIFOs reset")
        
    def soft_reset(self):
        """Perform soft reset of SMBus controller."""
        self.reg_map.write('SMBUS_CONTROL', 'soft_reset', 1)
        self.reg_map.write('SMBUS_CONTROL', 'soft_reset', 0)
        self.log.info("Soft reset performed")
        
    def enable_interrupts(self, complete: bool = False, error: bool = False,
                         tx_thresh: bool = False, rx_thresh: bool = False,
                         slave_addr: bool = False):
        """
        Enable interrupts.
        
        Args:
            complete: Enable transaction complete interrupt
            error: Enable error interrupt
            tx_thresh: Enable TX FIFO threshold interrupt
            rx_thresh: Enable RX FIFO threshold interrupt
            slave_addr: Enable slave addressed interrupt
        """
        self.reg_map.write('SMBUS_INT_ENABLE', 'complete_en', 1 if complete else 0)
        self.reg_map.write('SMBUS_INT_ENABLE', 'error_en', 1 if error else 0)
        self.reg_map.write('SMBUS_INT_ENABLE', 'tx_thresh_en', 1 if tx_thresh else 0)
        self.reg_map.write('SMBUS_INT_ENABLE', 'rx_thresh_en', 1 if rx_thresh else 0)
        self.reg_map.write('SMBUS_INT_ENABLE', 'slave_addr_en', 1 if slave_addr else 0)
        
        enabled = []
        if complete: enabled.append("complete")
        if error: enabled.append("error")
        if tx_thresh: enabled.append("tx_thresh")
        if rx_thresh: enabled.append("rx_thresh")
        if slave_addr: enabled.append("slave_addr")
        
        self.log.info(f"Interrupts enabled: {', '.join(enabled) if enabled else 'none'}")
        
    def clear_interrupts(self, complete: bool = False, error: bool = False,
                        tx_thresh: bool = False, rx_thresh: bool = False,
                        slave_addr: bool = False):
        """
        Clear interrupt status flags (write-1-to-clear).
        
        Args:
            complete: Clear transaction complete interrupt
            error: Clear error interrupt
            tx_thresh: Clear TX FIFO threshold interrupt
            rx_thresh: Clear RX FIFO threshold interrupt
            slave_addr: Clear slave addressed interrupt
        """
        if complete:
            self.reg_map.write('SMBUS_INT_STATUS', 'complete_int', 1)
        if error:
            self.reg_map.write('SMBUS_INT_STATUS', 'error_int', 1)
        if tx_thresh:
            self.reg_map.write('SMBUS_INT_STATUS', 'tx_thresh_int', 1)
        if rx_thresh:
            self.reg_map.write('SMBUS_INT_STATUS', 'rx_thresh_int', 1)
        if slave_addr:
            self.reg_map.write('SMBUS_INT_STATUS', 'slave_addr_int', 1)
            
        cleared = []
        if complete: cleared.append("complete")
        if error: cleared.append("error")
        if tx_thresh: cleared.append("tx_thresh")
        if rx_thresh: cleared.append("rx_thresh")
        if slave_addr: cleared.append("slave_addr")
        
        self.log.info(f"Interrupts cleared: {', '.join(cleared) if cleared else 'none'}")
        
    def initialize_defaults(self, system_clock_mhz: int = 100):
        """
        Initialize SMBus with sensible defaults.
        
        Args:
            system_clock_mhz: System clock frequency in MHz for calculating divider
        """
        # Set clock divider for 100kHz operation
        # divider = (sys_clk / (4 * scl_freq)) - 1
        divider = (system_clock_mhz * 1000000 // (4 * 100000)) - 1
        self.set_clock_divider(divider)
        
        # Set timeout to 25ms
        timeout_cycles = int(system_clock_mhz * 1000 * 25)  # 25ms
        self.set_timeout(timeout_cycles)
        
        # Enable master mode, disable PEC, standard speed
        self.enable_master(enable=True, pec_enable=False, fast_mode=False)
        
        # Disable slave mode
        self.enable_slave(enable=False)
        
        # Reset FIFOs
        self.fifo_reset()
        
        # Disable all interrupts
        self.enable_interrupts()
        
        self.log.info(f"SMBus initialized (100kHz @ {system_clock_mhz}MHz, master mode)")
        
    def generate_apb_cycles(self) -> List[APBPacket]:
        """
        Generate APB bus cycles for all pending register writes.
        
        Returns:
            List of APBPacket objects ready for bus transaction
        """
        return self.reg_map.generate_apb_cycles()
