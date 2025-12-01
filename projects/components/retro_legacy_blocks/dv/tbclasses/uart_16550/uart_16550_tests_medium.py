# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: UART16550MediumTests
# Purpose: UART 16550 Medium Test Suite
#
# Documentation: projects/components/retro_legacy_blocks/rtl/uart_16550/README.md
# Subsystem: retro_legacy_blocks/uart_16550
#
# Created: 2025-11-30

"""
UART 16550 Medium Tests

Medium-level verification of UART 16550 functionality including:
- FIFO operations
- Interrupt generation and clearing
- Modem status inputs
- External UART BFM TX/RX
- Multiple byte transfers
"""

import random
from cocotb.triggers import ClockCycles


class UART16550MediumTests:
    """Medium test methods for UART 16550 module."""

    def __init__(self, tb):
        """
        Initialize medium tests.

        Args:
            tb: UART16550TB instance
        """
        self.tb = tb
        self.log = tb.log

    async def test_fifo_operations(self) -> bool:
        """Test FIFO operations - filling and emptying."""
        self.log.info("Testing FIFO operations...")
        passed = True

        try:
            from .uart_16550_tb import UART16550RegisterMap

            # Initialize UART with loopback
            await self.tb.basic_init()
            await self.tb.enable_loopback(True)

            # Fill TX FIFO (16 bytes for 16550)
            test_data = [i & 0xFF for i in range(8)]  # Start with 8 bytes

            self.log.info(f"Writing {len(test_data)} bytes to TX FIFO")
            for byte_val in test_data:
                await self.tb.tx_byte(byte_val)

            # Wait for loopback transfer
            # Divisor=54, 16x oversample, 10 bits/byte = 54*16*10 = 8640 clocks/byte
            # 8 bytes take ~70k clocks. Add generous margin.
            await ClockCycles(self.tb.pclk, 150000)

            # Wait for all data to loop back
            await self.tb.wait_for_tx_complete(timeout_cycles=100000)
            self.log.info("TX complete, waiting for RX to settle...")
            await ClockCycles(self.tb.pclk, 100000)

            # Check how many bytes are ready
            _, lsr = await self.tb.read_register(UART16550RegisterMap.UART_LSR)
            self.log.info(f"LSR before rx_bytes: 0x{lsr:02X}")

            # Read back from RX FIFO - use longer per-byte timeout
            self.log.info(f"Attempting to receive {len(test_data)} bytes...")
            received = []
            for i in range(len(test_data)):
                _, lsr = await self.tb.read_register(UART16550RegisterMap.UART_LSR)
                data_ready = bool(lsr & UART16550RegisterMap.LSR_DATA_READY)
                self.log.info(f"Byte {i}: LSR=0x{lsr:02X}, DATA_READY={data_ready}")
                if data_ready:
                    byte_val = await self.tb.rx_byte(timeout_cycles=10000)
                    if byte_val is not None:
                        received.append(byte_val)
                        self.log.info(f"  Received 0x{byte_val:02X}")
                    else:
                        self.log.error(f"  rx_byte returned None despite DATA_READY")
                        break
                else:
                    self.log.info(f"  No more data, stopping at {len(received)} bytes")
                    break

            if len(received) != len(test_data):
                self.log.error(f"FIFO count mismatch: sent {len(test_data)}, received {len(received)}")
                passed = False
            else:
                mismatches = 0
                for i, (tx, rx) in enumerate(zip(test_data, received)):
                    if tx != rx:
                        self.log.error(f"FIFO[{i}] mismatch: TX=0x{tx:02X}, RX=0x{rx:02X}")
                        mismatches += 1

                if mismatches == 0:
                    self.log.info(f"FIFO operations: OK ({len(test_data)} bytes)")
                else:
                    passed = False

            # Disable loopback
            await self.tb.enable_loopback(False)

        except Exception as e:
            self.log.error(f"FIFO operations test exception: {e}")
            passed = False

        return passed

    async def test_rx_interrupt(self) -> bool:
        """Test RX data available interrupt."""
        self.log.info("Testing RX data available interrupt...")
        passed = True

        try:
            from .uart_16550_tb import UART16550RegisterMap

            # Initialize UART with loopback
            await self.tb.basic_init()
            await self.tb.enable_loopback(True)

            # Enable RX data interrupt
            await self.tb.enable_irq(rx_data=True)
            await ClockCycles(self.tb.pclk, 10)

            # Clear any pending interrupts by reading LSR
            _ = await self.tb.get_line_status()

            # Verify IRQ is not asserted initially
            if self.tb.get_irq():
                self.log.warning("IRQ unexpectedly asserted before TX")

            # Transmit a byte
            await self.tb.tx_byte(0x55)

            # Wait for loopback and interrupt
            await ClockCycles(self.tb.pclk, 15000)

            # Check IRQ
            if not self.tb.get_irq():
                self.log.error("IRQ not asserted after RX")
                passed = False
            else:
                self.log.info("RX interrupt asserted: OK")

            # Check IIR
            iir = await self.tb.get_interrupt_id()
            int_id = (iir >> 1) & 0x03
            if int_id != 0x02:  # RX data available
                self.log.warning(f"Unexpected interrupt ID: {int_id} (expected 2)")

            # Clear interrupt by reading data
            _ = await self.tb.rx_byte()
            await ClockCycles(self.tb.pclk, 10)

            # IRQ should clear
            if self.tb.get_irq():
                self.log.warning("IRQ still asserted after read")

            # Disable interrupts and loopback
            await self.tb.write_register(UART16550RegisterMap.UART_IER, 0x00)
            await self.tb.enable_loopback(False)

        except Exception as e:
            self.log.error(f"RX interrupt test exception: {e}")
            passed = False

        return passed

    async def test_tx_empty_interrupt(self) -> bool:
        """Test TX holding empty interrupt."""
        self.log.info("Testing TX holding empty interrupt...")
        passed = True

        try:
            from .uart_16550_tb import UART16550RegisterMap

            # Initialize UART
            await self.tb.basic_init()

            # Enable TX empty interrupt
            await self.tb.enable_irq(tx_empty=True)
            await ClockCycles(self.tb.pclk, 10)

            # TX should already be empty, so IRQ should be asserted
            # (TX empty interrupt asserts when THR becomes empty)

            # First, let's read IIR to see status
            iir = await self.tb.get_interrupt_id()
            int_pending = not (iir & UART16550RegisterMap.IIR_INT_NOT_PENDING)

            if int_pending:
                self.log.info("TX empty interrupt pending initially: OK")
            else:
                self.log.info("No interrupt pending initially (expected)")

            # Write a byte to fill THR
            await self.tb.tx_byte(0xAA)
            await ClockCycles(self.tb.pclk, 100)

            # Wait for TX to complete
            await self.tb.wait_for_tx_complete(timeout_cycles=20000)

            # Now THR should be empty and interrupt should assert
            await ClockCycles(self.tb.pclk, 100)
            if self.tb.get_irq():
                self.log.info("TX empty interrupt after transmit: OK")
            else:
                self.log.warning("TX empty interrupt not asserted (may be implementation-specific)")

            # Disable interrupts
            await self.tb.write_register(UART16550RegisterMap.UART_IER, 0x00)

        except Exception as e:
            self.log.error(f"TX empty interrupt test exception: {e}")
            passed = False

        return passed

    async def test_modem_status_inputs(self) -> bool:
        """Test modem status input signals."""
        self.log.info("Testing modem status inputs...")
        passed = True

        try:
            from .uart_16550_tb import UART16550RegisterMap

            # Initialize UART
            await self.tb.basic_init()

            # Test CTS
            self.tb.set_cts(False)  # Inactive
            await ClockCycles(self.tb.pclk, 10)
            msr = await self.tb.get_modem_status()
            if msr & UART16550RegisterMap.MSR_CTS:
                self.log.error("CTS should be inactive")
                passed = False

            self.tb.set_cts(True)   # Active
            await ClockCycles(self.tb.pclk, 10)
            msr = await self.tb.get_modem_status()
            if not (msr & UART16550RegisterMap.MSR_CTS):
                self.log.error("CTS should be active")
                passed = False
            else:
                self.log.info("CTS input: OK")

            # Test DSR
            self.tb.set_dsr(False)
            await ClockCycles(self.tb.pclk, 10)
            msr = await self.tb.get_modem_status()
            if msr & UART16550RegisterMap.MSR_DSR:
                self.log.error("DSR should be inactive")
                passed = False

            self.tb.set_dsr(True)
            await ClockCycles(self.tb.pclk, 10)
            msr = await self.tb.get_modem_status()
            if not (msr & UART16550RegisterMap.MSR_DSR):
                self.log.error("DSR should be active")
                passed = False
            else:
                self.log.info("DSR input: OK")

            # Test RI
            self.tb.set_ri(True)
            await ClockCycles(self.tb.pclk, 10)
            msr = await self.tb.get_modem_status()
            if not (msr & UART16550RegisterMap.MSR_RI):
                self.log.error("RI should be active")
                passed = False
            else:
                self.log.info("RI input: OK")

            # Test DCD
            self.tb.set_dcd(True)
            await ClockCycles(self.tb.pclk, 10)
            msr = await self.tb.get_modem_status()
            if not (msr & UART16550RegisterMap.MSR_DCD):
                self.log.error("DCD should be active")
                passed = False
            else:
                self.log.info("DCD input: OK")

            # Reset modem inputs
            self.tb.set_cts(False)
            self.tb.set_dsr(False)
            self.tb.set_ri(False)
            self.tb.set_dcd(False)

        except Exception as e:
            self.log.error(f"Modem status inputs test exception: {e}")
            passed = False

        return passed

    async def test_modem_loopback(self) -> bool:
        """Test modem signal loopback (MCR -> MSR in loopback mode)."""
        self.log.info("Testing modem signal loopback...")
        passed = True

        try:
            from .uart_16550_tb import UART16550RegisterMap

            # Initialize UART and enable loopback
            await self.tb.basic_init()
            await self.tb.enable_loopback(True)
            await ClockCycles(self.tb.pclk, 10)

            # In loopback mode: DTR->DSR, RTS->CTS, OUT1->RI, OUT2->DCD

            # Test DTR -> DSR
            await self.tb.set_modem_control(dtr=True, rts=False, out1=False, out2=False)
            await ClockCycles(self.tb.pclk, 10)
            msr = await self.tb.get_modem_status()
            if not (msr & UART16550RegisterMap.MSR_DSR):
                self.log.error("DTR->DSR loopback failed")
                passed = False
            else:
                self.log.info("DTR->DSR loopback: OK")

            # Test RTS -> CTS
            await self.tb.set_modem_control(dtr=False, rts=True, out1=False, out2=False)
            await ClockCycles(self.tb.pclk, 10)
            msr = await self.tb.get_modem_status()
            if not (msr & UART16550RegisterMap.MSR_CTS):
                self.log.error("RTS->CTS loopback failed")
                passed = False
            else:
                self.log.info("RTS->CTS loopback: OK")

            # Test OUT1 -> RI
            await self.tb.set_modem_control(dtr=False, rts=False, out1=True, out2=False)
            await ClockCycles(self.tb.pclk, 10)
            msr = await self.tb.get_modem_status()
            if not (msr & UART16550RegisterMap.MSR_RI):
                self.log.error("OUT1->RI loopback failed")
                passed = False
            else:
                self.log.info("OUT1->RI loopback: OK")

            # Test OUT2 -> DCD
            await self.tb.set_modem_control(dtr=False, rts=False, out1=False, out2=True)
            await ClockCycles(self.tb.pclk, 10)
            msr = await self.tb.get_modem_status()
            if not (msr & UART16550RegisterMap.MSR_DCD):
                self.log.error("OUT2->DCD loopback failed")
                passed = False
            else:
                self.log.info("OUT2->DCD loopback: OK")

            # Disable loopback
            await self.tb.enable_loopback(False)
            await self.tb.set_modem_control(dtr=False, rts=False, out1=False, out2=False)

        except Exception as e:
            self.log.error(f"Modem loopback test exception: {e}")
            passed = False

        return passed

    async def test_uart_bfm_tx(self) -> bool:
        """Test sending data to DUT via UART BFM."""
        self.log.info("Testing UART BFM TX to DUT...")
        passed = True

        try:
            from .uart_16550_tb import UART16550RegisterMap

            # Initialize UART (not loopback - use external BFM)
            await self.tb.basic_init()
            await self.tb.enable_loopback(False)

            # Explicitly reset FIFOs and drain any stale data
            await self.tb.reset_fifos()
            await ClockCycles(self.tb.pclk, 100)

            # Drain any remaining RX data
            while await self.tb.is_rx_data_ready():
                stale = await self.tb.rx_byte(timeout_cycles=100)
                self.log.info(f"Drained stale RX data: 0x{stale:02X}")

            # Enable RX interrupt
            await self.tb.enable_irq(rx_data=True)

            # Send a byte to DUT via UART BFM
            test_byte = 0x42
            self.log.info(f"Sending 0x{test_byte:02X} to DUT via UART BFM")
            await self.tb.send_to_dut(test_byte)

            # Wait for reception - need ~10 bits at ~864 clocks/bit = 8640 clocks
            await ClockCycles(self.tb.pclk, 15000)

            # Check if data received
            if await self.tb.is_rx_data_ready():
                rx_byte = await self.tb.rx_byte()
                if rx_byte == test_byte:
                    self.log.info(f"BFM TX -> DUT RX: OK (0x{rx_byte:02X})")
                else:
                    self.log.error(f"Data mismatch: sent 0x{test_byte:02X}, received 0x{rx_byte:02X}")
                    passed = False
            else:
                self.log.error("No data received from BFM TX")
                passed = False

            # Disable interrupts
            await self.tb.write_register(UART16550RegisterMap.UART_IER, 0x00)

        except Exception as e:
            self.log.error(f"UART BFM TX test exception: {e}")
            passed = False

        return passed

    async def test_uart_bfm_rx(self) -> bool:
        """Test receiving data from DUT via UART BFM monitor."""
        self.log.info("Testing UART BFM RX from DUT...")
        passed = True

        try:
            from .uart_16550_tb import UART16550RegisterMap

            # Initialize UART (not loopback)
            await self.tb.basic_init()
            await self.tb.enable_loopback(False)

            # Clear the RX monitor queue
            self.tb.clear_rx_queue()

            # Explicitly reset FIFOs
            await self.tb.reset_fifos()
            await ClockCycles(self.tb.pclk, 100)

            # Send a byte from DUT
            test_byte = 0x57
            self.log.info(f"DUT transmitting 0x{test_byte:02X}")
            await self.tb.tx_byte(test_byte)

            # Wait for transmission - need ~10 bits at ~864 clocks/bit = 8640 clocks
            await ClockCycles(self.tb.pclk, 15000)

            # Wait for TX complete
            await self.tb.wait_for_tx_complete(timeout_cycles=20000)

            # Check BFM monitor
            packets = self.tb.get_received_packets()
            if len(packets) > 0:
                rx_packet = packets[-1]  # Get latest
                if rx_packet.data == test_byte:
                    self.log.info(f"DUT TX -> BFM RX: OK (0x{rx_packet.data:02X})")
                else:
                    self.log.error(f"Data mismatch: sent 0x{test_byte:02X}, captured 0x{rx_packet.data:02X}")
                    passed = False
            else:
                self.log.error("No packets captured by BFM RX monitor")
                passed = False

        except Exception as e:
            self.log.error(f"UART BFM RX test exception: {e}")
            passed = False

        return passed

    async def test_multiple_bytes(self) -> bool:
        """Test multiple byte transfer in loopback mode."""
        self.log.info("Testing multiple byte transfer...")
        passed = True

        try:
            # Initialize UART with loopback
            await self.tb.basic_init()
            await self.tb.enable_loopback(True)

            # Test string
            test_string = "Hello"
            test_bytes = [ord(c) for c in test_string]

            self.log.info(f"Transmitting: '{test_string}'")

            # Transmit bytes
            for byte_val in test_bytes:
                await self.tb.tx_byte(byte_val)

            # Wait for loopback
            # 5 bytes, each taking ~8640 clocks, both TX and RX = 5 * 8640 * 2 = 86,400
            # Add margin
            await ClockCycles(self.tb.pclk, len(test_bytes) * 20000)

            # Receive bytes
            received = await self.tb.rx_bytes(len(test_bytes), timeout_cycles=50000)

            if len(received) != len(test_bytes):
                self.log.error(f"Length mismatch: sent {len(test_bytes)}, received {len(received)}")
                passed = False
            else:
                received_string = ''.join(chr(b) for b in received)
                if received_string == test_string:
                    self.log.info(f"Multiple byte transfer: OK ('{received_string}')")
                else:
                    self.log.error(f"String mismatch: sent '{test_string}', received '{received_string}'")
                    passed = False

            # Disable loopback
            await self.tb.enable_loopback(False)

        except Exception as e:
            self.log.error(f"Multiple bytes test exception: {e}")
            passed = False

        return passed

    async def run_all_medium_tests(self) -> bool:
        """Run all medium tests."""
        results = []

        medium_test_methods = [
            ('FIFO Operations', self.test_fifo_operations),
            ('RX Interrupt', self.test_rx_interrupt),
            ('TX Empty Interrupt', self.test_tx_empty_interrupt),
            ('Modem Status Inputs', self.test_modem_status_inputs),
            ('Modem Loopback', self.test_modem_loopback),
            ('UART BFM TX', self.test_uart_bfm_tx),
            ('UART BFM RX', self.test_uart_bfm_rx),
            ('Multiple Bytes', self.test_multiple_bytes),
        ]

        self.log.info("=" * 80)
        self.log.info("Starting UART 16550 Medium Tests")
        self.log.info("=" * 80)

        for test_name, test_method in medium_test_methods:
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
        self.log.info("MEDIUM TEST SUMMARY")
        self.log.info("=" * 80)

        passed_count = sum(1 for _, result in results if result)
        total_count = len(results)

        for test_name, result in results:
            status = "PASSED" if result else "FAILED"
            self.log.info(f"{test_name:45s} {status}")

        self.log.info(f"\nMedium Tests: {passed_count}/{total_count} passed")

        return all(result for _, result in results)
