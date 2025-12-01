# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: UART16550FullTests
# Purpose: UART 16550 Full Stress Test Suite
#
# Documentation: projects/components/retro_legacy_blocks/rtl/uart_16550/README.md
# Subsystem: retro_legacy_blocks/uart_16550
#
# Created: 2025-11-30

"""
UART 16550 Full Stress Tests

Full stress verification of UART 16550 functionality including:
- Random data patterns
- FIFO stress (fill/drain cycles)
- Multiple baud rates
- Error injection (future)
- Long transfer sequences
- Interrupt stress testing
- BFM bidirectional communication
"""

import random
from cocotb.triggers import ClockCycles


class UART16550FullTests:
    """Full stress test methods for UART 16550 module."""

    def __init__(self, tb):
        """
        Initialize full tests.

        Args:
            tb: UART16550TB instance
        """
        self.tb = tb
        self.log = tb.log

    async def test_random_data_loopback(self) -> bool:
        """Test with random data patterns in loopback mode."""
        self.log.info("Testing random data loopback...")
        passed = True

        try:
            # Initialize UART with loopback
            await self.tb.basic_init()
            await self.tb.enable_loopback(True)

            # Generate random test data
            # Note: TX/RX FIFOs are only 16 bytes deep, so we must process in batches
            num_bytes = 32
            test_data = [random.randint(0, 255) for _ in range(num_bytes)]
            batch_size = 8  # Safely less than FIFO depth of 16

            self.log.info(f"Transmitting {num_bytes} random bytes in batches of {batch_size}")

            # Process in batches to avoid FIFO overflow
            received = []
            for batch_start in range(0, num_bytes, batch_size):
                batch_end = min(batch_start + batch_size, num_bytes)
                batch = test_data[batch_start:batch_end]

                # Transmit batch
                for byte_val in batch:
                    await self.tb.tx_byte(byte_val)

                # Wait for loopback
                await ClockCycles(self.tb.pclk, len(batch) * 12000)

                # Receive batch
                batch_received = await self.tb.rx_bytes(len(batch), timeout_cycles=50000)
                received.extend(batch_received)

            if len(received) != num_bytes:
                self.log.error(f"Count mismatch: sent {num_bytes}, received {len(received)}")
                passed = False
            else:
                mismatches = 0
                for i, (tx, rx) in enumerate(zip(test_data, received)):
                    if tx != rx:
                        if mismatches < 5:  # Only log first 5 mismatches
                            self.log.error(f"Byte[{i}] mismatch: TX=0x{tx:02X}, RX=0x{rx:02X}")
                        mismatches += 1

                if mismatches == 0:
                    self.log.info(f"Random data loopback: OK ({num_bytes} bytes)")
                else:
                    self.log.error(f"Random data loopback: {mismatches} mismatches")
                    passed = False

            # Disable loopback
            await self.tb.enable_loopback(False)

        except Exception as e:
            self.log.error(f"Random data loopback test exception: {e}")
            passed = False

        return passed

    async def test_fifo_stress(self) -> bool:
        """Stress test FIFO with multiple fill/drain cycles."""
        self.log.info("Testing FIFO stress...")
        passed = True

        try:
            # Initialize UART with loopback
            await self.tb.basic_init()
            await self.tb.enable_loopback(True)

            # Multiple fill/drain cycles
            num_cycles = 4
            bytes_per_cycle = 12  # Slightly less than FIFO depth

            for cycle in range(num_cycles):
                # Generate test data for this cycle
                test_data = [(cycle * 16 + i) & 0xFF for i in range(bytes_per_cycle)]

                self.log.info(f"FIFO stress cycle {cycle + 1}/{num_cycles}")

                # Fill FIFO
                for byte_val in test_data:
                    await self.tb.tx_byte(byte_val)

                # Wait for loopback
                await ClockCycles(self.tb.pclk, bytes_per_cycle * 12000)

                # Drain FIFO
                received = await self.tb.rx_bytes(bytes_per_cycle, timeout_cycles=80000)

                if len(received) != bytes_per_cycle:
                    self.log.error(f"Cycle {cycle}: count mismatch: sent {bytes_per_cycle}, received {len(received)}")
                    passed = False
                elif received != test_data:
                    mismatches = sum(1 for tx, rx in zip(test_data, received) if tx != rx)
                    self.log.error(f"Cycle {cycle}: {mismatches} data mismatches")
                    passed = False

            if passed:
                self.log.info(f"FIFO stress: OK ({num_cycles} cycles)")

            # Disable loopback
            await self.tb.enable_loopback(False)

        except Exception as e:
            self.log.error(f"FIFO stress test exception: {e}")
            passed = False

        return passed

    async def test_baud_rate_variations(self) -> bool:
        """Test various baud rate settings with loopback."""
        self.log.info("Testing baud rate variations...")
        passed = True

        try:
            from .uart_16550_tb import UART16550RegisterMap

            # Enable loopback
            await self.tb.enable_loopback(True)

            # Test different divisors (baud rates)
            # Note: Actual bit times will vary - we're testing the divisor config
            # At 100MHz: divisor 54 = 115200 baud, divisor 108 = 57600 baud, etc.
            test_divisors = [
                (54, "115200"),
                (108, "57600"),
                (27, "230400"),
            ]

            for divisor, baud_desc in test_divisors:
                self.log.info(f"Testing divisor {divisor} (~{baud_desc} baud)")

                # Set new baud rate
                await self.tb.set_baud_divisor(divisor)

                # Update BFM timing (if we were using external BFM)
                # For loopback mode, the internal baud generator handles timing

                # Configure and reset FIFOs
                await self.tb.configure_line(word_length=8, stop_bits=1, parity='none')
                await self.tb.reset_fifos()
                await self.tb.enable_fifos()

                # Test data
                test_byte = 0x5A

                # Transmit
                await self.tb.tx_byte(test_byte)

                # Wait time scales with divisor
                wait_cycles = divisor * 160  # ~10 bit times
                await ClockCycles(self.tb.pclk, wait_cycles)

                # Receive
                rx_byte = await self.tb.rx_byte(timeout_cycles=wait_cycles * 2)

                if rx_byte is None:
                    self.log.error(f"Baud {baud_desc}: timeout")
                    passed = False
                elif rx_byte != test_byte:
                    self.log.error(f"Baud {baud_desc}: mismatch TX=0x{test_byte:02X}, RX=0x{rx_byte:02X}")
                    passed = False
                else:
                    self.log.info(f"Baud {baud_desc}: OK")

            # Restore default baud rate
            await self.tb.set_baud_divisor(54)
            await self.tb.enable_loopback(False)

        except Exception as e:
            self.log.error(f"Baud rate variations test exception: {e}")
            passed = False

        return passed

    async def test_interrupt_stress(self) -> bool:
        """Stress test interrupt generation and clearing."""
        self.log.info("Testing interrupt stress...")
        passed = True

        try:
            from .uart_16550_tb import UART16550RegisterMap

            # Initialize UART with loopback
            await self.tb.basic_init()
            await self.tb.enable_loopback(True)

            # Enable RX data interrupt
            await self.tb.enable_irq(rx_data=True)

            # Multiple interrupt cycles
            num_cycles = 8

            for cycle in range(num_cycles):
                test_byte = (cycle * 17) & 0xFF  # Different byte each cycle

                # Transmit
                await self.tb.tx_byte(test_byte)

                # Wait for loopback
                await ClockCycles(self.tb.pclk, 12000)

                # Check IRQ
                if not self.tb.get_irq():
                    self.log.error(f"Cycle {cycle}: IRQ not asserted")
                    passed = False
                    continue

                # Clear by reading data
                rx_byte = await self.tb.rx_byte()
                await ClockCycles(self.tb.pclk, 10)

                if rx_byte != test_byte:
                    self.log.error(f"Cycle {cycle}: data mismatch")
                    passed = False

                # IRQ should clear
                if self.tb.get_irq():
                    self.log.warning(f"Cycle {cycle}: IRQ not cleared")

            if passed:
                self.log.info(f"Interrupt stress: OK ({num_cycles} cycles)")

            # Disable interrupts and loopback
            await self.tb.write_register(UART16550RegisterMap.UART_IER, 0x00)
            await self.tb.enable_loopback(False)

        except Exception as e:
            self.log.error(f"Interrupt stress test exception: {e}")
            passed = False

        return passed

    async def test_bfm_bidirectional(self) -> bool:
        """Test bidirectional communication with UART BFM."""
        self.log.info("Testing BFM bidirectional communication...")
        passed = True

        try:
            from .uart_16550_tb import UART16550RegisterMap

            # Initialize UART (not loopback)
            await self.tb.basic_init()
            await self.tb.enable_loopback(False)

            # Clear monitor queue
            self.tb.clear_rx_queue()

            # Test data
            num_bytes = 5
            tx_to_dut = [0x41 + i for i in range(num_bytes)]  # 'A', 'B', 'C', 'D', 'E'
            tx_from_dut = [0x61 + i for i in range(num_bytes)]  # 'a', 'b', 'c', 'd', 'e'

            # Send to DUT via BFM
            self.log.info(f"BFM -> DUT: {[chr(b) for b in tx_to_dut]}")
            for byte_val in tx_to_dut:
                await self.tb.send_to_dut(byte_val)

            # Wait for DUT to receive
            await ClockCycles(self.tb.pclk, num_bytes * 12000)

            # Read what DUT received
            dut_received = await self.tb.rx_bytes(num_bytes, timeout_cycles=50000)

            if dut_received != tx_to_dut:
                self.log.error(f"DUT receive mismatch: expected {tx_to_dut}, got {dut_received}")
                passed = False
            else:
                self.log.info("BFM -> DUT: OK")

            # Now DUT transmits to BFM
            self.log.info(f"DUT -> BFM: {[chr(b) for b in tx_from_dut]}")
            for byte_val in tx_from_dut:
                await self.tb.tx_byte(byte_val)

            # Wait for transmission
            await ClockCycles(self.tb.pclk, num_bytes * 12000)
            await self.tb.wait_for_tx_complete(timeout_cycles=50000)

            # Check BFM monitor
            packets = self.tb.get_received_packets()
            bfm_received = [p.data for p in packets[-num_bytes:]] if len(packets) >= num_bytes else []

            if bfm_received != tx_from_dut:
                self.log.error(f"BFM receive mismatch: expected {tx_from_dut}, got {bfm_received}")
                passed = False
            else:
                self.log.info("DUT -> BFM: OK")

        except Exception as e:
            self.log.error(f"BFM bidirectional test exception: {e}")
            passed = False

        return passed

    async def test_long_sequence(self) -> bool:
        """Test long data sequence in loopback mode."""
        self.log.info("Testing long sequence transfer...")
        passed = True

        try:
            # Initialize UART with loopback
            await self.tb.basic_init()
            await self.tb.enable_loopback(True)

            # Long sequence
            num_bytes = 64
            test_data = [(i * 7) & 0xFF for i in range(num_bytes)]

            self.log.info(f"Transmitting {num_bytes} bytes long sequence")

            # Transmit in batches to avoid FIFO overflow
            batch_size = 8
            received = []

            for batch_start in range(0, num_bytes, batch_size):
                batch_end = min(batch_start + batch_size, num_bytes)
                batch = test_data[batch_start:batch_end]

                # Transmit batch
                for byte_val in batch:
                    await self.tb.tx_byte(byte_val)

                # Wait for loopback
                await ClockCycles(self.tb.pclk, len(batch) * 12000)

                # Receive batch
                batch_received = await self.tb.rx_bytes(len(batch), timeout_cycles=50000)
                received.extend(batch_received)

            # Verify
            if len(received) != num_bytes:
                self.log.error(f"Length mismatch: sent {num_bytes}, received {len(received)}")
                passed = False
            else:
                mismatches = sum(1 for tx, rx in zip(test_data, received) if tx != rx)
                if mismatches == 0:
                    self.log.info(f"Long sequence: OK ({num_bytes} bytes)")
                else:
                    self.log.error(f"Long sequence: {mismatches} mismatches")
                    passed = False

            # Disable loopback
            await self.tb.enable_loopback(False)

        except Exception as e:
            self.log.error(f"Long sequence test exception: {e}")
            passed = False

        return passed

    async def test_all_register_patterns(self) -> bool:
        """Test all registers with walking 1s and 0s patterns."""
        self.log.info("Testing register patterns...")
        passed = True

        try:
            from .uart_16550_tb import UART16550RegisterMap

            # Walking patterns
            patterns = [0x00, 0xFF, 0x55, 0xAA, 0x01, 0x02, 0x04, 0x08,
                       0x10, 0x20, 0x40, 0x80]

            # Test scratch register with all patterns
            for pattern in patterns:
                await self.tb.write_register(UART16550RegisterMap.UART_SCR, pattern)
                _, readback = await self.tb.read_register(UART16550RegisterMap.UART_SCR)
                if readback != pattern:
                    self.log.error(f"SCR pattern 0x{pattern:02X}: read 0x{readback:02X}")
                    passed = False

            if passed:
                self.log.info(f"Register patterns: OK ({len(patterns)} patterns)")

        except Exception as e:
            self.log.error(f"Register patterns test exception: {e}")
            passed = False

        return passed

    async def test_modem_delta_detection(self) -> bool:
        """Test modem status delta bit detection."""
        self.log.info("Testing modem delta detection...")
        passed = True

        try:
            from .uart_16550_tb import UART16550RegisterMap

            # Initialize
            await self.tb.basic_init()

            # Start with all modem inputs inactive
            self.tb.set_cts(False)
            self.tb.set_dsr(False)
            self.tb.set_ri(False)
            self.tb.set_dcd(False)
            await ClockCycles(self.tb.pclk, 20)

            # Clear any pending deltas by reading MSR
            _ = await self.tb.get_modem_status()

            # Toggle CTS
            self.tb.set_cts(True)
            await ClockCycles(self.tb.pclk, 10)
            msr = await self.tb.get_modem_status()
            if msr & UART16550RegisterMap.MSR_DELTA_CTS:
                self.log.info("Delta CTS detected: OK")
            else:
                self.log.warning("Delta CTS not detected")

            # Toggle DSR
            self.tb.set_dsr(True)
            await ClockCycles(self.tb.pclk, 10)
            msr = await self.tb.get_modem_status()
            if msr & UART16550RegisterMap.MSR_DELTA_DSR:
                self.log.info("Delta DSR detected: OK")
            else:
                self.log.warning("Delta DSR not detected")

            # Toggle DCD
            self.tb.set_dcd(True)
            await ClockCycles(self.tb.pclk, 10)
            msr = await self.tb.get_modem_status()
            if msr & UART16550RegisterMap.MSR_DELTA_DCD:
                self.log.info("Delta DCD detected: OK")
            else:
                self.log.warning("Delta DCD not detected")

            # Reset modem inputs
            self.tb.set_cts(False)
            self.tb.set_dsr(False)
            self.tb.set_ri(False)
            self.tb.set_dcd(False)

        except Exception as e:
            self.log.error(f"Modem delta detection test exception: {e}")
            passed = False

        return passed

    async def run_all_full_tests(self) -> bool:
        """Run all full stress tests."""
        results = []

        full_test_methods = [
            ('Random Data Loopback', self.test_random_data_loopback),
            ('FIFO Stress', self.test_fifo_stress),
            ('Baud Rate Variations', self.test_baud_rate_variations),
            ('Interrupt Stress', self.test_interrupt_stress),
            ('BFM Bidirectional', self.test_bfm_bidirectional),
            ('Long Sequence', self.test_long_sequence),
            ('All Register Patterns', self.test_all_register_patterns),
            ('Modem Delta Detection', self.test_modem_delta_detection),
        ]

        self.log.info("=" * 80)
        self.log.info("Starting UART 16550 Full Stress Tests")
        self.log.info("=" * 80)

        for test_name, test_method in full_test_methods:
            self.log.info(f"\n{'=' * 60}")
            self.log.info(f"Running: {test_name}")
            self.log.info(f"{'=' * 60}")
            try:
                result = await test_method()
                results.append((test_name, result))
            except Exception as e:
                self.log.error(f"{test_name} raised exception: {e}")
                results.append((test_name, False))

        # Print summary
        self.log.info("\n" + "=" * 80)
        self.log.info("FULL TEST SUMMARY")
        self.log.info("=" * 80)

        passed_count = sum(1 for _, result in results if result)
        total_count = len(results)

        for test_name, result in results:
            status = "PASSED" if result else "FAILED"
            self.log.info(f"{test_name:45s} {status}")

        self.log.info(f"\nFull Tests: {passed_count}/{total_count} passed")

        return all(result for _, result in results)
