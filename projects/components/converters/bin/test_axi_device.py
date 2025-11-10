#!/usr/bin/env python3
"""
test_axi_device.py
Example script showing how to test custom AXI devices using the UART bridge

This example assumes you have a custom AXI device with control, status, 
and data registers mapped in your FPGA address space.
"""

from uart_axi_bridge import UARTAxiBridge
import sys
import time


def test_basic_device():
    """Test basic read/write operations on a custom AXI device"""
    
    print("=" * 60)
    print("Custom AXI Device Test")
    print("=" * 60)
    
    # Define your device's register map
    DEVICE_BASE = 0x44A00000
    CONTROL_REG = DEVICE_BASE + 0x00
    STATUS_REG  = DEVICE_BASE + 0x04
    DATA_REG    = DEVICE_BASE + 0x08
    ID_REG      = DEVICE_BASE + 0x0C
    
    # Connect to FPGA
    with UARTAxiBridge('/dev/ttyUSB1', 115200) as fpga:
        
        # Read device ID
        print("\n1. Reading Device ID...")
        device_id = fpga.read(ID_REG)
        if device_id is not None:
            print(f"   Device ID: 0x{device_id:08X}")
        
        # Configure device
        print("\n2. Configuring device...")
        control_value = 0x00000001  # Enable bit
        if fpga.write(CONTROL_REG, control_value):
            print(f"   Control register set to 0x{control_value:08X}")
        
        # Check status
        print("\n3. Checking device status...")
        status = fpga.read(STATUS_REG)
        if status is not None:
            print(f"   Status: 0x{status:08X}")
            if status & 0x01:
                print("   Device is READY")
            if status & 0x02:
                print("   Device is BUSY")
        
        # Write test data
        print("\n4. Writing test data...")
        test_data = 0xCAFEBABE
        if fpga.write_verify(DATA_REG, test_data):
            print(f"   Successfully wrote and verified 0x{test_data:08X}")
        else:
            print(f"   FAILED to write/verify data")
        
        # Read back data
        print("\n5. Reading back data...")
        readback = fpga.read(DATA_REG)
        if readback is not None:
            print(f"   Read: 0x{readback:08X}")
            if readback == test_data:
                print("   ✓ Data integrity check PASSED")
            else:
                print("   ✗ Data integrity check FAILED")


def test_memory_block():
    """Test a block of memory-mapped registers"""
    
    print("\n" + "=" * 60)
    print("Memory Block Test")
    print("=" * 60)
    
    MEM_BASE = 0x44A01000
    NUM_WORDS = 16
    
    with UARTAxiBridge('/dev/ttyUSB1', 115200) as fpga:
        
        # Write sequential pattern
        print(f"\n1. Writing sequential pattern to {NUM_WORDS} words...")
        test_pattern = [0x1000 + i for i in range(NUM_WORDS)]
        count = fpga.fill_memory(MEM_BASE, test_pattern)
        print(f"   Wrote {count}/{NUM_WORDS} words")
        
        # Read back and verify
        print(f"\n2. Reading back and verifying...")
        dump = fpga.dump_memory(MEM_BASE, NUM_WORDS)
        errors = 0
        for i, (addr, data) in enumerate(dump):
            expected = test_pattern[i]
            match = "✓" if data == expected else "✗"
            print(f"   [{i:2d}] 0x{addr:08X}: 0x{data:08X} {match}")
            if data != expected:
                errors += 1
        
        print(f"\n   Verification: {NUM_WORDS - errors}/{NUM_WORDS} correct")
        if errors == 0:
            print("   ✓ Memory block test PASSED")
        else:
            print(f"   ✗ Memory block test FAILED ({errors} errors)")


def test_performance():
    """Measure transaction performance"""
    
    print("\n" + "=" * 60)
    print("Performance Test")
    print("=" * 60)
    
    TEST_ADDR = 0x44A00000
    NUM_TRANSACTIONS = 100
    
    with UARTAxiBridge('/dev/ttyUSB1', 115200) as fpga:
        
        # Measure write performance
        print(f"\n1. Measuring write performance ({NUM_TRANSACTIONS} writes)...")
        start_time = time.time()
        for i in range(NUM_TRANSACTIONS):
            fpga.write(TEST_ADDR, i)
        write_time = time.time() - start_time
        write_rate = NUM_TRANSACTIONS / write_time
        print(f"   Time: {write_time:.3f} seconds")
        print(f"   Rate: {write_rate:.1f} transactions/second")
        
        # Measure read performance
        print(f"\n2. Measuring read performance ({NUM_TRANSACTIONS} reads)...")
        start_time = time.time()
        for i in range(NUM_TRANSACTIONS):
            fpga.read(TEST_ADDR)
        read_time = time.time() - start_time
        read_rate = NUM_TRANSACTIONS / read_time
        print(f"   Time: {read_time:.3f} seconds")
        print(f"   Rate: {read_rate:.1f} transactions/second")


def main():
    """Run all tests"""
    
    try:
        # Run test suite
        test_basic_device()
        test_memory_block()
        test_performance()
        
        print("\n" + "=" * 60)
        print("All tests completed!")
        print("=" * 60)
        
        return 0
        
    except serial.SerialException as e:
        print(f"\nSerial port error: {e}")
        print("Make sure:")
        print("  - FPGA is connected via USB")
        print("  - Correct serial port (/dev/ttyUSB1)")
        print("  - You have permissions (sudo usermod -a -G dialout $USER)")
        return 1
        
    except KeyboardInterrupt:
        print("\n\nTest interrupted by user")
        return 1
        
    except Exception as e:
        print(f"\nUnexpected error: {e}")
        import traceback
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())
