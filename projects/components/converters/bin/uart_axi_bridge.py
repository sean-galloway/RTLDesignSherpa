#!/usr/bin/env python3
"""
uart_axi_bridge.py
Python interface for UART AXI Bridge on FPGA

Provides a simple Python API to perform AXI transactions via UART
"""

import serial
import sys
import time


class UARTAxiBridge:
    """
    UART to AXI Bridge Controller
    
    Communicates with FPGA UART AXI Bridge to perform read/write transactions
    on AXI4-Lite bus.
    """
    
    def __init__(self, port='/dev/ttyUSB1', baudrate=115200, timeout=1.0):
        """
        Initialize UART connection to FPGA
        
        Args:
            port: Serial port device (e.g., '/dev/ttyUSB1' on Linux, 'COM3' on Windows)
            baudrate: Baud rate (must match FPGA configuration, default 115200)
            timeout: Read timeout in seconds
        """
        try:
            self.ser = serial.Serial(port, baudrate, timeout=timeout)
            time.sleep(0.1)  # Let UART stabilize
            self.ser.reset_input_buffer()
            self.ser.reset_output_buffer()
            print(f"Connected to {port} at {baudrate} baud")
        except serial.SerialException as e:
            print(f"Error opening serial port {port}: {e}")
            raise
    
    def write(self, addr, data):
        """
        Write 32-bit data to AXI address
        
        Args:
            addr: 32-bit address (int or hex string like '0x44A00000')
            data: 32-bit data (int or hex string like '0xDEADBEEF')
        
        Returns:
            True if write acknowledged with 'OK', False otherwise
        """
        # Convert string addresses to integers
        if isinstance(addr, str):
            addr = int(addr, 16)
        if isinstance(data, str):
            data = int(data, 16)
        
        # Build command: "W <addr> <data>\n"
        cmd = f"W {addr:08X} {data:08X}\n"
        self.ser.write(cmd.encode('ascii'))
        
        # Wait for "OK\n" response
        response = self.ser.read_until(b'\n', size=10)
        return response.strip() == b'OK'
    
    def read(self, addr):
        """
        Read 32-bit data from AXI address
        
        Args:
            addr: 32-bit address (int or hex string like '0x44A00000')
        
        Returns:
            32-bit data value as integer, or None on error
        """
        # Convert string address to integer
        if isinstance(addr, str):
            addr = int(addr, 16)
        
        # Build command: "R <addr>\n"
        cmd = f"R {addr:08X}\n"
        self.ser.write(cmd.encode('ascii'))
        
        # Wait for "0xDEADBEEF\n" response
        response = self.ser.read_until(b'\n', size=20)
        response = response.strip()
        
        if response.startswith(b'0x'):
            try:
                return int(response[2:], 16)
            except ValueError:
                print(f"Error parsing response: {response}")
                return None
        else:
            print(f"Invalid response format: {response}")
            return None
    
    def write_verify(self, addr, data):
        """
        Write data and verify with readback
        
        Args:
            addr: 32-bit address
            data: 32-bit data
            
        Returns:
            True if write succeeded and readback matches
        """
        if not self.write(addr, data):
            return False
        
        readback = self.read(addr)
        return readback == data
    
    def dump_memory(self, start_addr, num_words=16):
        """
        Dump memory contents
        
        Args:
            start_addr: Starting address
            num_words: Number of 32-bit words to read
            
        Returns:
            List of tuples (address, data)
        """
        results = []
        for i in range(num_words):
            addr = start_addr + (i * 4)
            data = self.read(addr)
            if data is not None:
                results.append((addr, data))
        return results
    
    def fill_memory(self, start_addr, values):
        """
        Write multiple values to consecutive addresses
        
        Args:
            start_addr: Starting address
            values: List of 32-bit values to write
            
        Returns:
            Number of successful writes
        """
        success_count = 0
        for i, value in enumerate(values):
            addr = start_addr + (i * 4)
            if self.write(addr, value):
                success_count += 1
        return success_count
    
    def close(self):
        """Close UART connection"""
        if hasattr(self, 'ser') and self.ser.is_open:
            self.ser.close()
            print("UART connection closed")
    
    def __enter__(self):
        """Context manager entry"""
        return self
    
    def __exit__(self, exc_type, exc_val, exc_tb):
        """Context manager exit"""
        self.close()


def main():
    """Example usage and test"""
    print("UART AXI Bridge - Python Interface")
    print("=" * 50)
    
    # Connect to FPGA
    try:
        bridge = UARTAxiBridge('/dev/ttyUSB1', 115200)
    except Exception as e:
        print(f"Failed to connect: {e}")
        return 1
    
    try:
        # Write example
        print("\n[Write Transaction]")
        addr = 0x44A00000
        data = 0xDEADBEEF
        print(f"Writing 0x{data:08X} to 0x{addr:08X}...")
        success = bridge.write(addr, data)
        print(f"  Result: {'OK' if success else 'FAILED'}")
        
        # Read example
        print("\n[Read Transaction]")
        print(f"Reading from 0x{addr:08X}...")
        read_data = bridge.read(addr)
        if read_data is not None:
            print(f"  Read: 0x{read_data:08X}")
            if read_data == data:
                print("  ✓ Readback matches!")
            else:
                print("  ✗ Readback mismatch!")
        
        # Write-verify example
        print("\n[Write-Verify Transaction]")
        addr = 0x44A00004
        data = 0xCAFEBABE
        print(f"Write-verify 0x{data:08X} to 0x{addr:08X}...")
        success = bridge.write_verify(addr, data)
        print(f"  Result: {'PASS' if success else 'FAIL'}")
        
        # Burst write example
        print("\n[Burst Write]")
        base_addr = 0x44A01000
        values = [0x1000 + i for i in range(4)]
        print(f"Writing {len(values)} words to 0x{base_addr:08X}...")
        count = bridge.fill_memory(base_addr, values)
        print(f"  Wrote {count}/{len(values)} words successfully")
        
        # Memory dump example
        print("\n[Memory Dump]")
        print(f"Dumping 4 words from 0x{base_addr:08X}:")
        dump = bridge.dump_memory(base_addr, 4)
        for addr, data in dump:
            print(f"  0x{addr:08X}: 0x{data:08X}")
    
    finally:
        bridge.close()
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
