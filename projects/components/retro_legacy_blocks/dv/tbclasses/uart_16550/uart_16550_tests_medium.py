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
import cocotb
from cocotb.triggers import ClockCycles, RisingEdge
from CocoTBFramework.components.apb.apb_packet import APBPacket


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

    # ==================================================================
    # GH60 batch (uart_16550 issue #60 + two qc rounds): RED tests
    # against the CURRENT RTL, mechanisms traced by direct reading of
    # uart_16550_core.sv / uart_16550_config_regs.sv / uart_16550_regs.sv.
    # Same pipeline as the smbus GH58 batch. No RTL edits, no ledger.
    # ==================================================================

    async def _hard_reset(self):
        """Real DUT reset between GH60 tests - GH60-C6 confirms LSR/MSR
        sticky error bits can NEVER be cleared by software (that is
        exactly the defect), so any earlier test that provokes one
        (C6 itself, QC1) leaves w_int_rx_error permanently true for
        the rest of the session, which - being the HIGHEST-priority
        interrupt source - corrupts priority-based IIR reads in every
        later test regardless of what that later test is actually
        exercising. A soft reconfigure is not enough; only a real
        reset clears the core's sticky r_overrun_error/r_parity_error/
        r_framing_error/r_break_interrupt/r_delta_* flops."""
        await self.tb.assert_reset()
        await ClockCycles(self.tb.pclk, 10)
        await self.tb.deassert_reset()
        await ClockCycles(self.tb.pclk, 10)
        self.tb.dut.uart_rx.value = 1
        self.tb.dut.cts_n.value = 1
        self.tb.dut.dsr_n.value = 1
        self.tb.dut.ri_n.value = 1
        self.tb.dut.dcd_n.value = 1
        await ClockCycles(self.tb.pclk, 5)

    async def _drive_raw_frame(self, data, num_data_bits, parity_bit=None,
                                stop_bit=1, break_line=False):
        """Bit-bang a single UART frame directly onto dut.uart_rx, LSB
        first (matching this core's own RX/TX bit ordering). No BFM in
        the framework can produce a malformed frame (bad parity, bad
        stop bit, break) on purpose, so this is the correct mechanism
        for fault injection here - not a hand-rolled replacement for
        the normal-case UARTMaster/UARTMonitor, which are used
        everywhere a well-formed frame suffices."""
        tb = self.tb
        bit_time = tb.clks_per_bit
        if break_line:
            tb.dut.uart_rx.value = 0
            await ClockCycles(tb.pclk, bit_time * (num_data_bits + 2))
            tb.dut.uart_rx.value = 1
            await ClockCycles(tb.pclk, bit_time)
            return
        tb.dut.uart_rx.value = 0  # start bit
        await ClockCycles(tb.pclk, bit_time)
        for i in range(num_data_bits):
            tb.dut.uart_rx.value = (data >> i) & 1
            await ClockCycles(tb.pclk, bit_time)
        if parity_bit is not None:
            tb.dut.uart_rx.value = parity_bit
            await ClockCycles(tb.pclk, bit_time)
        tb.dut.uart_rx.value = 1 if stop_bit else 0
        await ClockCycles(tb.pclk, bit_time)
        tb.dut.uart_rx.value = 1  # back to idle

    async def _provoke_overrun(self):
        from .uart_16550_tb import UART16550RegisterMap
        await self.tb.configure_line(word_length=8, stop_bits=1, parity='none')
        await self.tb.enable_fifos(rx_trigger=1)
        await self.tb.reset_fifos()
        for i in range(16):
            await self._drive_raw_frame(0x40 + i, 8, stop_bit=1)
        await self._drive_raw_frame(0x99, 8, stop_bit=1)

    async def _provoke_parity_error(self):
        await self.tb.configure_line(word_length=8, stop_bits=1, parity='even')
        await self.tb.enable_fifos(rx_trigger=1)
        await self.tb.reset_fifos()
        # data=0x01 with even parity expects parity bit=1; send 0 (wrong).
        await self._drive_raw_frame(0x01, 8, parity_bit=0, stop_bit=1)

    async def _provoke_framing_error(self):
        await self.tb.configure_line(word_length=8, stop_bits=1, parity='none')
        await self.tb.enable_fifos(rx_trigger=1)
        await self.tb.reset_fifos()
        await self._drive_raw_frame(0x55, 8, stop_bit=0)

    async def _provoke_break(self):
        await self.tb.configure_line(word_length=8, stop_bits=1, parity='none')
        await self.tb.enable_fifos(rx_trigger=1)
        await self.tb.reset_fifos()
        await self._drive_raw_frame(0, 8, break_line=True)

    async def _provoke_delta_cts(self):
        self.tb.set_cts(True)
        await ClockCycles(self.tb.pclk, 200)

    async def _provoke_delta_dsr(self):
        self.tb.set_dsr(True)
        await ClockCycles(self.tb.pclk, 200)

    async def _provoke_delta_dcd(self):
        self.tb.set_dcd(True)
        await ClockCycles(self.tb.pclk, 200)

    async def _provoke_trailing_ri(self):
        self.tb.set_ri(True)
        await ClockCycles(self.tb.pclk, 200)
        self.tb.set_ri(False)
        await ClockCycles(self.tb.pclk, 200)

    async def test_gh60_c3_rbr_thr_bit_separation(self) -> bool:
        """C3: UART_DATA[7:0] must return the RECEIVED byte (16550
        RBR semantics - a driver reads RX data from the low byte
        lane; THR is write-only and must never read back).
        uart_16550_regs.sv: readback_array[0][7:0] =
        field_storage.UART_DATA.tx_data.value (the LAST THR WRITE)
        while [15:8] = hwif_in.UART_DATA.rx_data.next (the actual
        received byte) - backwards from spec."""
        self.log.info("=== GH60-C3: RBR read data must be in bits [7:0] ===")
        try:
            from .uart_16550_tb import UART16550RegisterMap
            await self._hard_reset()
            await self.tb.basic_init()
            await self.tb.enable_loopback(False)

            tx_byte, rx_byte = 0xA5, 0x3C
            await self.tb.write_register(UART16550RegisterMap.UART_DATA, tx_byte)
            await ClockCycles(self.tb.pclk, 20)

            await self._drive_raw_frame(rx_byte, 8, stop_bit=1)
            ok = await self.tb.wait_for_rx_data(timeout_cycles=20000)
            if not ok:
                self.log.error("GH60-C3: RX data never became ready")
                return False

            _, raw = await self.tb.read_register(UART16550RegisterMap.UART_DATA)
            low_byte = raw & 0xFF
            high_byte = (raw >> 8) & 0xFF

            self.log.info(f"  wrote THR=0x{tx_byte:02X}, received RX=0x{rx_byte:02X}, "
                          f"UART_DATA readback=0x{raw:04X} (low=0x{low_byte:02X}, "
                          f"high=0x{high_byte:02X})")

            if low_byte == rx_byte:
                self.log.info("GH60-C3 GREEN")
                return True

            self.log.error(
                f"GH60-C3: UART_DATA[7:0] must return the received byte "
                f"(0x{rx_byte:02X}) - got 0x{low_byte:02X} (the last THR "
                f"write, 0x{tx_byte:02X}) instead. The received byte "
                f"instead appears in bits [15:8] (0x{high_byte:02X}).")
            return False
        except Exception as e:
            self.log.error(f"GH60-C3 test error: {e}")
            return False

    async def _check_lsr_clears_on_read(self, provoke, bit_mask, ier_kind, label):
        from .uart_16550_tb import UART16550RegisterMap
        # Real reset first: C6 sub-cases run in sequence and EACH
        # provokes a DIFFERENT sticky LSR/MSR condition that (per this
        # very defect) never clears - without a hard reset, an earlier
        # sub-case's still-stuck RX-error would permanently outrank
        # everything else in the priority-encoded IIR for every later
        # sub-case, corrupting the "pending"/id check independent of
        # what THIS sub-case is exercising.
        await self._hard_reset()
        await self.tb.basic_init()
        await self.tb.enable_loopback(False)
        await self.tb.enable_irq(**{ier_kind: True})
        await provoke()
        await self.tb.wait_for_rx_data(timeout_cycles=20000)
        await ClockCycles(self.tb.pclk, 50)
        lsr1 = await self.tb.get_line_status()
        bit1 = bool(lsr1 & bit_mask)
        await ClockCycles(self.tb.pclk, 20)
        lsr2 = await self.tb.get_line_status()
        bit2 = bool(lsr2 & bit_mask)
        iir = await self.tb.get_interrupt_id()
        # RX line-status is the HIGHEST-priority source (int_id=2'b11)
        # so checking its specific id (rather than "any pending",
        # which TX-empty being permanently true would also satisfy)
        # correctly isolates whether THIS condition is still reported.
        line_status_pending = (iir & UART16550RegisterMap.IIR_INT_ID_MASK) == UART16550RegisterMap.IIR_INT_ID_MASK
        irq_after = self.tb.get_irq()
        ok = bit1 and (not bit2) and (not line_status_pending) and (not irq_after)
        self.log.info(f"  {label}: LSR read1=0x{lsr1:02X}(bit={bit1}), "
                      f"LSR read2(after 1st read)=0x{lsr2:02X}(bit={bit2}), "
                      f"IIR={iir:#04x}, line_status_pending="
                      f"{line_status_pending}, irq_after={irq_after}, ok={ok}")
        return ok

    async def _check_msr_clears_on_read(self, provoke, bit_mask, label):
        from .uart_16550_tb import UART16550RegisterMap
        await self._hard_reset()
        await self.tb.basic_init()
        await self.tb.enable_loopback(False)
        await self.tb.enable_irq(modem_status=True)
        await provoke()
        msr1 = await self.tb.get_modem_status()
        bit1 = bool(msr1 & bit_mask)
        await ClockCycles(self.tb.pclk, 20)
        msr2 = await self.tb.get_modem_status()
        bit2 = bool(msr2 & bit_mask)
        iir = await self.tb.get_interrupt_id()
        int_not_pending = bool(iir & UART16550RegisterMap.IIR_INT_NOT_PENDING)
        # Modem status is the LOWEST-priority source (int_id=2'b00) -
        # it is only reported when something IS pending AND no
        # higher-priority source is also active.
        modem_pending = (not int_not_pending) and ((iir & UART16550RegisterMap.IIR_INT_ID_MASK) == 0)
        ok = bit1 and (not bit2) and (not modem_pending)
        self.log.info(f"  {label}: MSR read1=0x{msr1:02X}(bit={bit1}), "
                      f"MSR read2(after 1st read)=0x{msr2:02X}(bit={bit2}), "
                      f"IIR={iir:#04x}, modem_pending={modem_pending}, ok={ok}")
        return ok

    async def test_gh60_c6_lsr_msr_clear_on_read(self) -> bool:
        """C6: LSR/MSR error and delta flags can never be cleared and
        their interrupts latch forever - no read-clear exists, the
        fields are W1C in the regblock, uart_16550_config_regs.sv ties
        every clr_* strobe to 1'b0 (the core itself DOES support
        clearing - clr_overrun_error etc are real ports that work -
        the wrapper just never drives them), and the still-set core
        status flags drive hwset every cycle so nothing can ever stay
        cleared. Per 16550 semantics: LSR errors clear on read of LSR,
        MSR deltas clear on read of MSR (note: the RDL currently
        declares these fields W1C, which is a different mechanism from
        real 16550 hardware read-clear, but W1C is at least clearable
        in principle - the wrapper wiring gap means NEITHER mechanism
        actually works today)."""
        self.log.info("=== GH60-C6: LSR/MSR flags must be clearable ===")
        from .uart_16550_tb import UART16550RegisterMap
        M = UART16550RegisterMap
        try:
            results = {}
            results['overrun'] = await self._check_lsr_clears_on_read(
                self._provoke_overrun, M.LSR_OVERRUN_ERROR, 'line_status', 'overrun')
            results['parity'] = await self._check_lsr_clears_on_read(
                self._provoke_parity_error, M.LSR_PARITY_ERROR, 'line_status', 'parity')
            results['framing'] = await self._check_lsr_clears_on_read(
                self._provoke_framing_error, M.LSR_FRAMING_ERROR, 'line_status', 'framing')
            results['break'] = await self._check_lsr_clears_on_read(
                self._provoke_break, M.LSR_BREAK_INT, 'line_status', 'break')
            results['delta_cts'] = await self._check_msr_clears_on_read(
                self._provoke_delta_cts, M.MSR_DELTA_CTS, 'delta_cts')
            results['delta_dsr'] = await self._check_msr_clears_on_read(
                self._provoke_delta_dsr, M.MSR_DELTA_DSR, 'delta_dsr')
            results['delta_dcd'] = await self._check_msr_clears_on_read(
                self._provoke_delta_dcd, M.MSR_DELTA_DCD, 'delta_dcd')
            results['trailing_ri'] = await self._check_msr_clears_on_read(
                self._provoke_trailing_ri, M.MSR_TRAILING_RI, 'trailing_ri')

            failures = [k for k, v in results.items() if not v]
            if not failures:
                self.log.info("GH60-C6 GREEN")
                return True

            self.log.error(
                f"GH60-C6: LSR/MSR flags never clear for: {failures} "
                f"(out of {list(results.keys())}). "
                f"uart_16550_config_regs.sv ties every clr_* input to "
                f"1'b0 while hwset is driven directly from the "
                f"still-latched core status flags.")
            return False
        except Exception as e:
            self.log.error(f"GH60-C6 test error: {e}")
            return False

    async def test_gh60_qc1_framing_error_and_break_must_assert(self) -> bool:
        """qc-1: RX_STOP computes r_rx_frame_err/r_rx_break and then
        reads them back in the SAME always_ff block for the FIFO
        write and the sticky-flag set (both non-blocking assignments
        sampling the PRE-EDGE, still-0, values), so a framing error or
        a break NEVER sets LSR[3]/LSR[4], the RX FIFO entry's error
        bits, or the line-status interrupt. Parity error is the
        control - it is set one cycle earlier in RX_PARITY, so it IS
        the up-to-date value by the time RX_STOP reads it, and works
        today."""
        self.log.info("=== GH60-QC1: framing error and break must assert ===")
        from .uart_16550_tb import UART16550RegisterMap
        M = UART16550RegisterMap
        try:
            results = {}
            cases = (
                ('framing', self._provoke_framing_error, M.LSR_FRAMING_ERROR),
                ('break', self._provoke_break, M.LSR_BREAK_INT),
                ('parity(control)', self._provoke_parity_error, M.LSR_PARITY_ERROR),
            )
            for label, provoke, bit_mask in cases:
                await self._hard_reset()
                await self.tb.basic_init()
                await self.tb.enable_loopback(False)
                await self.tb.enable_irq(line_status=True)
                await provoke()
                rx_ready = await self.tb.wait_for_rx_data(timeout_cycles=20000)
                await ClockCycles(self.tb.pclk, 20)
                # Check the interrupt state BEFORE touching LSR - real
                # 16550 semantics clear the RX-line-status interrupt
                # on a read of LSR too, so IIR/irq must be observed
                # first or this test's OWN LSR read (below) would
                # clear the very interrupt it is trying to check.
                iir = await self.tb.get_interrupt_id()
                irq = self.tb.get_irq()
                lsr = await self.tb.get_line_status()

                bit_ok = bool(lsr & bit_mask)
                fifo_err = bool(lsr & M.LSR_RX_FIFO_ERROR)
                line_status_id = (iir & M.IIR_INT_ID_MASK) == M.IIR_INT_ID_MASK
                pending = not (iir & M.IIR_INT_NOT_PENDING)
                ok = bit_ok and fifo_err and pending and line_status_id and irq
                results[label] = ok
                self.log.info(f"  {label}: rx_ready={rx_ready}, LSR=0x{lsr:02X}, "
                              f"bit_ok={bit_ok}, fifo_err={fifo_err}, "
                              f"IIR=0x{iir:02X}, pending={pending}, "
                              f"line_status_id={line_status_id}, irq={irq}, "
                              f"ok={ok}")

            failures = [k for k, v in results.items() if not v]
            if not failures:
                self.log.info("GH60-QC1 GREEN")
                return True
            self.log.error(f"GH60-QC1: {failures} did not assert "
                          f"LSR/FIFO-error/interrupt (results={results}).")
            return False
        except Exception as e:
            self.log.error(f"GH60-QC1 test error: {e}")
            return False

    async def test_gh60_qc2_short_word_rx_justification(self) -> bool:
        """qc-2: RX shifts MSB-first (`r_rx_shift <=
        {w_rx_in, r_rx_shift[7:1]}`), so at 5/6/7 data bits the
        received character lands MSB-justified with stale low bits
        instead of right-justified and zero-filled in [7:0]. TX
        already sends [N-1:0] LSB-first (`r_tx_shift[0]`, shift
        right), so a loopback round-trip at <8 bits will not read
        back what was sent today. Also confirms break detection still
        works at a short (5-bit) word length."""
        self.log.info("=== GH60-QC2: 5/6/7-bit RX must be right-justified ===")
        from .uart_16550_tb import UART16550RegisterMap
        try:
            await self._hard_reset()
            results = {}
            for nbits in (5, 6, 7):
                await self.tb.configure_line(word_length=nbits, stop_bits=1,
                                              parity='none')
                await self.tb.enable_fifos(rx_trigger=1)
                await self.tb.reset_fifos()
                await self.tb.enable_loopback(True)

                test_val = (1 << nbits) - 1
                await self.tb.tx_byte(test_val)
                ok = await self.tb.wait_for_rx_data(timeout_cycles=20000)
                await ClockCycles(self.tb.pclk, 20)
                _, raw = await self.tb.read_register(UART16550RegisterMap.UART_DATA)
                # rx_data currently lands in [15:8] (see GH60-C3) -
                # read there regardless of C3's own bit-lane defect,
                # since this test is specifically about justification
                # WITHIN the received byte, not which lane it's in.
                rx_val = (raw >> 8) & 0xFF
                match = (rx_val == test_val)
                results[f'{nbits}bit_rx'] = ok and match
                self.log.info(f"  {nbits}-bit word: sent=0x{test_val:02X}, "
                              f"rx=0x{rx_val:02X} (want right-justified, "
                              f"zero-filled), match={match}")

                await self.tb.enable_loopback(False)

            await self.tb.configure_line(word_length=5, stop_bits=1, parity='none')
            await self.tb.enable_fifos(rx_trigger=1)
            await self.tb.reset_fifos()
            await self._drive_raw_frame(0, 5, break_line=True)
            ok_break = await self.tb.wait_for_rx_data(timeout_cycles=20000)
            await ClockCycles(self.tb.pclk, 20)
            lsr = await self.tb.get_line_status()
            break_ok = bool(lsr & UART16550RegisterMap.LSR_BREAK_INT)
            results['break_at_5bit'] = break_ok
            self.log.info(f"  break@5bit: rx_ready={ok_break}, LSR=0x{lsr:02X}, "
                          f"break_ok={break_ok}")

            await self.tb.configure_line(word_length=8, stop_bits=1, parity='none')

            failures = [k for k, v in results.items() if not v]
            if not failures:
                self.log.info("GH60-QC2 GREEN")
                return True
            self.log.error(f"GH60-QC2: {failures} failed (results={results}).")
            return False
        except Exception as e:
            self.log.error(f"GH60-QC2 test error: {e}")
            return False

    async def test_gh60_qc3_1_thr_gapless_writes(self) -> bool:
        """qc3-1: w_tx_write is a FALLING-EDGE detector on the decoded
        write strobe - if the APB bridge ever holds that strobe
        continuously high across two back-to-back same-address
        writes, the second write's falling edge never fires and its
        byte is dropped. Drives two back-to-back UART_DATA writes as
        fast as the framework APB master will issue them (both
        queued via send() with no artificial delay) and checks both
        bytes appear on the wire via loopback. If the bridge cannot
        produce a truly gapless shape (PSEL/PENABLE naturally drops
        between two separate APB transactions), this is a guard
        (expected GREEN) rather than a defect-catching RED test - see
        the reported PENABLE-gap evidence in the log either way."""
        self.log.info("=== GH60-QC3-1: gapless back-to-back THR writes ===")
        from .uart_16550_tb import UART16550RegisterMap
        try:
            await self._hard_reset()
            await self.tb.basic_init()
            await self.tb.enable_loopback(True)

            byte_a, byte_b = 0x11, 0x22
            pkt_a = APBPacket(pwrite=1, paddr=UART16550RegisterMap.UART_DATA,
                               pwdata=byte_a, pstrb=0xF, pprot=0,
                               data_width=32, addr_width=12, strb_width=4)
            pkt_a.direction = 'WRITE'
            pkt_b = APBPacket(pwrite=1, paddr=UART16550RegisterMap.UART_DATA,
                               pwdata=byte_b, pstrb=0xF, pprot=0,
                               data_width=32, addr_width=12, strb_width=4)
            pkt_b.direction = 'WRITE'

            penable_gap_seen = False
            prev_penable = int(self.tb.dut.s_apb_PENABLE.value)

            async def _watch_penable():
                nonlocal penable_gap_seen, prev_penable
                for _ in range(200):
                    await RisingEdge(self.tb.pclk)
                    cur = int(self.tb.dut.s_apb_PENABLE.value)
                    if prev_penable == 1 and cur == 0:
                        penable_gap_seen = True
                    prev_penable = cur

            watcher = cocotb.start_soon(_watch_penable())
            await self.tb.apb4_master.send(pkt_a)
            await self.tb.apb4_master.send(pkt_b)
            await ClockCycles(self.tb.pclk, 100)
            await watcher.join()

            received = await self.tb.rx_bytes(2, timeout_cycles=200000)
            self.log.info(f"  wrote {[hex(byte_a), hex(byte_b)]} back-to-back "
                          f"(queued via send(), no artificial delay), "
                          f"received={[hex(b) for b in received]}, "
                          f"penable_gap_seen={penable_gap_seen}")

            await self.tb.enable_loopback(False)

            if received == [byte_a, byte_b]:
                self.log.info(
                    f"GH60-QC3-1 GREEN: both writes made it onto the wire "
                    f"(penable_gap_seen={penable_gap_seen} - "
                    f"{'the bridge naturally gapped the two transactions, so this is a guard' if penable_gap_seen else 'a genuinely gapless pair passed'})")
                return True

            self.log.error(
                f"GH60-QC3-1: gapless back-to-back UART_DATA writes lost a "
                f"byte - wrote {[hex(byte_a), hex(byte_b)]}, received "
                f"{[hex(b) for b in received]} (penable_gap_seen="
                f"{penable_gap_seen}).")
            return False
        except Exception as e:
            self.log.error(f"GH60-QC3-1 test error: {e}")
            return False

    async def test_gh60_ier_gating(self) -> bool:
        """Coordinator ask: IER must gate each interrupt source
        independently (16550 semantics: IER=0 means the corresponding
        condition never asserts irq, even though the underlying
        LSR/IIR condition is still true). uart_16550_core.sv has NO
        ier/cfg_*_ie input port at all - IER is purely decorative;
        `irq = ~int_not_pending && cfg_out2` is driven regardless of
        IER."""
        self.log.info("=== GH60-IER: interrupt enables must gate each source ===")
        from .uart_16550_tb import UART16550RegisterMap
        try:
            await self._hard_reset()
            await self.tb.basic_init()
            await self.tb.enable_loopback(True)
            await self.tb.write_register(UART16550RegisterMap.UART_IER, 0x00)
            await self.tb.set_modem_control(out2=True, loopback=True)

            await self.tb.tx_byte(0x42)
            rx_ready = await self.tb.wait_for_rx_data(timeout_cycles=20000)
            await ClockCycles(self.tb.pclk, 50)

            irq = self.tb.get_irq()
            iir = await self.tb.get_interrupt_id()
            pending = not (iir & UART16550RegisterMap.IIR_INT_NOT_PENDING)

            await self.tb.enable_loopback(False)

            self.log.info(f"  rx_ready={rx_ready}, IER=0x00, irq={irq}, "
                          f"IIR=0x{iir:02X}, pending={pending}")

            if not irq and not pending:
                self.log.info("GH60-IER GREEN")
                return True

            self.log.error(
                f"GH60-IER: with IER=0x00 (all sources disabled), RX data "
                f"still asserted irq={irq}/pending={pending} - IER has no "
                f"wiring into interrupt generation at all in "
                f"uart_16550_core.sv (no ier/cfg_*_ie input port exists; "
                f"irq is driven purely by int_not_pending && cfg_out2).")
            return False
        except Exception as e:
            self.log.error(f"GH60-IER test error: {e}")
            return False

    async def test_gh60_guard_rx_trigger_levels(self) -> bool:
        """GUARD: RX data-available interrupt must not fire before the
        configured FIFO trigger level is reached. Checks the
        PRIORITY-ENCODED int_id for the RX-DATA source specifically
        (IIR bits[2:1]==2'b10) rather than "any interrupt pending" -
        with nothing ever written to THR in this test, w_tx_fifo_empty
        is true throughout, and thanks to the already-confirmed
        GH60-IER defect (IER does not gate anything) that alone makes
        "any pending" true the whole time regardless of the RX
        trigger. int_id is still meaningful despite that: it reports
        only the HIGHEST-priority active source, and RX-data
        (priority 2) outranks TX-empty (priority 3), so int_id
        correctly distinguishes "trigger not yet reached" (reports
        TX-empty's id) from "trigger reached" (reports RX-data's id)."""
        self.log.info("=== GH60-GUARD: RX FIFO trigger levels ===")
        from .uart_16550_tb import UART16550RegisterMap
        RX_DATA_ID = 0x04  # int_id=2'b10 at IIR bits[2:1]
        try:
            await self._hard_reset()
            await self.tb.configure_line(word_length=8, stop_bits=1, parity='none')
            await self.tb.set_baud_divisor(54)
            # reset_fifos() writes FCR without preserving the trigger
            # bits (it writes FIFO_ENABLE|RX_RESET|TX_RESET only), so
            # it must run BEFORE enable_fifos() sets the trigger level,
            # not after - otherwise it silently clobbers the trigger
            # back to level-1.
            await self.tb.reset_fifos()
            await self.tb.enable_fifos(rx_trigger=4)
            await self.tb.enable_loopback(True)
            await self.tb.enable_irq(rx_data=True)

            for i in range(3):
                await self.tb.tx_byte(0x50 + i)
            await ClockCycles(self.tb.pclk, 30000)
            iir_before = await self.tb.get_interrupt_id()
            rx_id_before = (iir_before & UART16550RegisterMap.IIR_INT_ID_MASK) == RX_DATA_ID

            await self.tb.tx_byte(0x53)
            await ClockCycles(self.tb.pclk, 30000)
            iir_after = await self.tb.get_interrupt_id()
            rx_id_after = (iir_after & UART16550RegisterMap.IIR_INT_ID_MASK) == RX_DATA_ID

            await self.tb.enable_loopback(False)
            self.log.info(f"  before trigger (3 bytes staged): "
                          f"IIR=0x{iir_before:02X}, rx_data_id={rx_id_before}; "
                          f"at trigger (4 bytes): IIR=0x{iir_after:02X}, "
                          f"rx_data_id={rx_id_after}")

            ok = (not rx_id_before) and rx_id_after
            if ok:
                self.log.info("GH60-GUARD(trigger) GREEN")
                return True
            self.log.error(
                f"GH60-GUARD(trigger): expected the RX-data interrupt ID "
                f"NOT reported below the trigger level and reported at "
                f"it - got rx_id_before={rx_id_before}, "
                f"rx_id_after={rx_id_after}.")
            return False
        except Exception as e:
            self.log.error(f"GH60-GUARD(trigger) test error: {e}")
            return False

    async def test_gh60_strict_decode_missing(self) -> bool:
        """Coordinator ask (turned out to be a real finding, not a
        guard): an APB access to an unmapped address must return
        PSLVERR the way the other RLB blocks do. uart_16550_regs.sv
        (the PeakRDL-generated regblock) hardwires BOTH
        `cpuif_wr_err = '0'` (line ~1200) and `readback_err = '0'`
        inside the read-data reduce block (line ~1276) - there is no
        decode-error path at all, for either direction, so an
        unmapped write or read is silently ack'd with PSLVERR=0."""
        self.log.info("=== GH60: strict decode (unmapped -> PSLVERR) ===")
        try:
            await self.tb.basic_init()
            bad_addr = 0x100  # well past the last mapped register (0x028)
            write_packet = APBPacket(
                pwrite=1, paddr=bad_addr, pwdata=0xDEADBEEF, pstrb=0xF,
                pprot=0, data_width=32, addr_width=12, strb_width=4)
            write_packet.direction = 'WRITE'
            await self.tb.apb4_master.send(write_packet)
            for _ in range(20):
                await RisingEdge(self.tb.pclk)
                if (self.tb.dut.s_apb_PSEL.value and
                        self.tb.dut.s_apb_PENABLE.value and
                        self.tb.dut.s_apb_PREADY.value):
                    break
            pslverr = bool(self.tb.dut.s_apb_PSLVERR.value)
            await RisingEdge(self.tb.pclk)

            self.log.info(f"  write to 0x{bad_addr:03X}: PSLVERR={pslverr}")
            if pslverr:
                self.log.info("GH60-strict-decode GREEN")
                return True
            self.log.error(
                f"GH60-strict-decode: write to unmapped address "
                f"0x{bad_addr:03X} did not assert PSLVERR.")
            return False
        except Exception as e:
            self.log.error(f"GH60-strict-decode test error: {e}")
            return False

    # ==================================================================
    # GH60-R2 batch (independent review, round 2): RED tests against
    # the CURRENT RTL, mechanisms traced by direct reading of
    # uart_16550_config_regs.sv / uart_16550_core.sv. No RTL edits, no
    # ledger.
    # ==================================================================

    async def test_gh60_r2_1_thr_byte_enable_masked(self) -> bool:
        """R2-1 (HIGH): a THR write with the low byte lane masked
        (PSTRB excludes lane 0) transmits a fabricated NUL byte
        instead of nothing. uart_16550_config_regs.sv:
        `w_thr_ack_now = w_uart_data_write && w_blk_wr_ack` has no
        byte-enable term - the DATA capture (`r_thr_data <=
        regblk_wr_data[7:0] & regblk_wr_biten[7:0]`) correctly masks
        to 0x00 when biten[7:0]=0, but the PUSH decision
        (`r_thr_push`) fires regardless, so a byte-disabled write
        still queues and transmits that masked-to-zero byte."""
        self.log.info("=== GH60-R2-1: THR write byte-enable must gate the push ===")
        from .uart_16550_tb import UART16550RegisterMap
        core = self.tb.dut.u_uart_config_regs.u_uart_core
        try:
            await self._hard_reset()
            await self.tb.basic_init()
            await self.tb.enable_loopback(False)

            level_before = int(core.w_tx_fifo_count.value)
            # PSTRB=0b0010: only lane 1 (the RX-alias byte) selected -
            # lane 0 (the actual THR data byte) is NOT written.
            await self.tb.write_register(UART16550RegisterMap.UART_DATA,
                                          0x000000AB, pstrb=0b0010)
            await ClockCycles(self.tb.pclk, 30)
            level_after_masked = int(core.w_tx_fifo_count.value)

            # PSTRB=0b0001: lane 0 selected - the byte DOES go out.
            await self.tb.write_register(UART16550RegisterMap.UART_DATA,
                                          0x00000042, pstrb=0b0001)
            await ClockCycles(self.tb.pclk, 30)
            level_after_normal = int(core.w_tx_fifo_count.value)

            self.log.info(
                f"  tx_fifo_count: before={level_before}, after "
                f"PSTRB=0b0010 write of 0xAB={level_after_masked}, "
                f"after PSTRB=0b0001 write of 0x42={level_after_normal}")

            masked_ok = (level_after_masked == level_before)
            # Compared against level_after_masked (not level_before):
            # the masked write may itself have incorrectly pushed a
            # byte (that is exactly the defect under test), and this
            # second check is about whether THIS write's own +1 is
            # correct, not a re-statement of the first check.
            normal_ok = (level_after_normal == level_after_masked + 1)

            if masked_ok and normal_ok:
                self.log.info("GH60-R2-1 GREEN")
                return True

            self.log.error(
                f"GH60-R2-1: byte-disabled THR write pushed a byte "
                f"anyway - tx_fifo_count went from {level_before} to "
                f"{level_after_masked} on a PSTRB=0b0010 write "
                f"(masked_ok={masked_ok}); normal PSTRB=0b0001 write "
                f"result: {level_before}->{level_after_normal} "
                f"(normal_ok={normal_ok}).")
            return False
        except Exception as e:
            self.log.error(f"GH60-R2-1 test error: {e}")
            return False

    async def test_gh60_r2_2_fifo_disable_not_honored(self) -> bool:
        """R2-2 (MED): FCR[0]=0 (16450 character mode) must reduce TX
        to a single holding register (later writes overwrite an
        unsent byte, not queue) and RX to a single holding register
        (a second unread character sets overrun, not queue silently).
        cfg_fifo_enable has only two consumers in uart_16550_core.sv
        (sts_fifo_status and the RX-trigger interrupt condition) and
        the TX/RX datapath itself never reads it, so both FIFOs stay
        full 16-deep regardless of FCR[0]."""
        self.log.info("=== GH60-R2-2: FCR[0]=0 must actually disable the FIFOs ===")
        from .uart_16550_tb import UART16550RegisterMap
        core = self.tb.dut.u_uart_config_regs.u_uart_core
        try:
            # --- TX side: character mode, 16 back-to-back THR writes.
            await self._hard_reset()
            await self.tb.configure_line(word_length=8, stop_bits=1, parity='none')
            await self.tb.set_baud_divisor(54)
            await self.tb.reset_fifos()
            await self.tb.write_register(UART16550RegisterMap.UART_FCR, 0x00)
            await self.tb.enable_loopback(False)

            for i in range(16):
                await self.tb.write_register(UART16550RegisterMap.UART_DATA, 0x60 + i)
            await ClockCycles(self.tb.pclk, 50)
            tx_level_char_mode = int(core.w_tx_fifo_count.value)
            tx_ok = tx_level_char_mode <= 1
            self.log.info(
                f"  TX char-mode: wrote 16 bytes back-to-back, "
                f"tx_fifo_count={tx_level_char_mode} (want <=1, a "
                f"single holding register later writes overwrite), "
                f"tx_ok={tx_ok}")

            # --- RX side: character mode, two characters with no read
            # in between must set overrun on the second.
            await self._hard_reset()
            await self.tb.configure_line(word_length=8, stop_bits=1, parity='none')
            await self.tb.set_baud_divisor(54)
            await self.tb.reset_fifos()
            await self.tb.write_register(UART16550RegisterMap.UART_FCR, 0x00)
            await self.tb.enable_loopback(False)

            await self._drive_raw_frame(0x11, 8, stop_bit=1)
            await ClockCycles(self.tb.pclk, 200)
            dr1 = bool(core.sts_data_ready.value)
            await self._drive_raw_frame(0x22, 8, stop_bit=1)
            await ClockCycles(self.tb.pclk, 200)
            lsr = await self.tb.get_line_status()
            overrun_ok = bool(lsr & UART16550RegisterMap.LSR_OVERRUN_ERROR)
            self.log.info(
                f"  RX char-mode: dr_after_1st={dr1}, "
                f"LSR_after_2nd_unread=0x{lsr:02X}, overrun_ok={overrun_ok}")

            if tx_ok and overrun_ok:
                self.log.info("GH60-R2-2 GREEN")
                return True

            self.log.error(
                f"GH60-R2-2: FCR[0]=0 does not reduce the FIFOs to "
                f"single-character (16450) behavior - TX: "
                f"tx_fifo_count={tx_level_char_mode} after 16 "
                f"back-to-back writes (want <=1, tx_ok={tx_ok}); RX: a "
                f"second unread character LSR=0x{lsr:02X} "
                f"(overrun_ok={overrun_ok}).")
            return False
        except Exception as e:
            self.log.error(f"GH60-R2-2 test error: {e}")
            return False

    async def test_gh60_r2_3_lsr_error_not_per_character(self) -> bool:
        """R2-3 (MED): LSR[4:2] (parity/framing/break) are GLOBAL
        sticky flops in uart_16550_core.sv, not derived from the
        per-character tag stored in the RX FIFO entry [10:8] (LSR[7]/
        rx_fifo_error IS correctly derived per-entry from that tag;
        the specific error-TYPE bits are not). Receive a clean 'A', a
        character with a parity error, then two more clean characters
        (FIFOs enabled, trigger=4); reading RBR must return 'A' with
        LSR reporting no parity error for it, and the parity error
        must be reported on the read that returns the bad byte."""
        self.log.info("=== GH60-R2-3: LSR error bits must tag the character being read ===")
        from .uart_16550_tb import UART16550RegisterMap
        M = UART16550RegisterMap
        try:
            await self._hard_reset()
            await self.tb.configure_line(word_length=8, stop_bits=1, parity='even')
            await self.tb.set_baud_divisor(54)
            await self.tb.reset_fifos()
            await self.tb.enable_fifos(rx_trigger=4)
            await self.tb.enable_loopback(False)

            chars = [ord('A'), 0xC3, ord('C'), ord('D')]
            for idx, ch in enumerate(chars):
                correct_parity = bin(ch).count('1') % 2  # even parity bit
                if idx == 1:
                    await self._drive_raw_frame(ch, 8, parity_bit=1 - correct_parity,
                                                 stop_bit=1)
                else:
                    await self._drive_raw_frame(ch, 8, parity_bit=correct_parity,
                                                 stop_bit=1)
                await ClockCycles(self.tb.pclk, 50)

            await ClockCycles(self.tb.pclk, 200)

            results = []
            for i in range(4):
                _, raw = await self.tb.read_register(M.UART_DATA)
                byte = raw & 0xFF
                lsr = await self.tb.get_line_status()
                parity_bit = bool(lsr & M.LSR_PARITY_ERROR)
                results.append((byte, parity_bit))
                self.log.info(f"  read {i}: byte=0x{byte:02X}, "
                              f"parity_error={parity_bit} (LSR=0x{lsr:02X})")

            clean_a_ok = (results[0][0] == ord('A')) and (not results[0][1])
            bad_byte_ok = (results[1][0] == 0xC3) and results[1][1]
            others_clean = (not results[2][1]) and (not results[3][1])
            ok = clean_a_ok and bad_byte_ok and others_clean

            if ok:
                self.log.info("GH60-R2-3 GREEN")
                return True

            self.log.error(
                f"GH60-R2-3: LSR parity-error bit is not attributed to "
                f"the correct character - results={results} (want "
                f"[0]=('A'=0x41, False), [1]=(0xC3, True), others "
                f"False).")
            return False
        except Exception as e:
            self.log.error(f"GH60-R2-3 test error: {e}")
            return False

    async def test_rlb013_dlab_remap(self) -> bool:
        """RLB-013: with LCR[7] (DLAB) set, 0x00 and 0x04 are the divisor
        latches, as a standard 16550 driver expects. The dedicated offsets
        at 0x24/0x28 keep working, so both forms address the same latches,
        and a divisor write must not be mistaken for a THR push."""
        self.log.info("=== RLB-013: DLAB remapping ===")
        from .uart_16550_tb import UART16550RegisterMap
        M = UART16550RegisterMap
        try:
            await self._hard_reset()
            await self.tb.configure_line(word_length=8, stop_bits=1, parity=None)
            await self.tb.reset_fifos()
            await self.tb.enable_fifos(rx_trigger=1)

            _, lcr = await self.tb.read_register(M.UART_LCR)
            await self.tb.write_register(M.UART_LCR, (lcr & 0xFF) | M.LCR_DLAB)

            tx_before = int(self.tb.dut.u_uart_config_regs.u_uart_core.w_tx_fifo_count.value)
            await self.tb.write_register(M.UART_DATA, 0x12)   # -> DLL
            await self.tb.write_register(M.UART_IER, 0x34)    # -> DLM
            tx_after = int(self.tb.dut.u_uart_config_regs.u_uart_core.w_tx_fifo_count.value)

            _, dll_alias = await self.tb.read_register(M.UART_DATA)
            _, dlm_alias = await self.tb.read_register(M.UART_IER)
            _, dll_flat = await self.tb.read_register(M.UART_DLL)
            _, dlm_flat = await self.tb.read_register(M.UART_DLM)

            aliased_ok = ((dll_alias & 0xFF) == 0x12 and (dlm_alias & 0xFF) == 0x34)
            flat_ok = ((dll_flat & 0xFF) == 0x12 and (dlm_flat & 0xFF) == 0x34)
            no_push = (tx_after == tx_before)
            self.log.info(f"  DLAB=1: 0x00->0x{dll_alias & 0xFF:02X} 0x04->0x{dlm_alias & 0xFF:02X}; "
                          f"0x24->0x{dll_flat & 0xFF:02X} 0x28->0x{dlm_flat & 0xFF:02X}; "
                          f"tx_level {tx_before}->{tx_after}")

            # DLAB clear: 0x00 is THR again and 0x04 is IER again.
            await self.tb.write_register(M.UART_LCR, lcr & 0xFF & ~M.LCR_DLAB)
            await self.tb.write_register(M.UART_IER, M.IER_RX_DATA_AVAIL)
            _, ier_back = await self.tb.read_register(M.UART_IER)
            ier_ok = (ier_back & 0xFF) == M.IER_RX_DATA_AVAIL
            tx_pre = int(self.tb.dut.u_uart_config_regs.u_uart_core.w_tx_fifo_count.value)
            await self.tb.write_register(M.UART_DATA, 0x5A)
            await ClockCycles(self.tb.pclk, 5)
            tx_post = int(self.tb.dut.u_uart_config_regs.u_uart_core.w_tx_fifo_count.value)
            thr_ok = tx_post > tx_pre
            self.log.info(f"  DLAB=0: IER readback=0x{ier_back & 0xFF:02X}, "
                          f"THR push {tx_pre}->{tx_post}")

            ok = aliased_ok and flat_ok and no_push and ier_ok and thr_ok
            if ok:
                self.log.info("RLB-013 DLAB remapping GREEN")
                return True
            self.log.error(
                f"RLB-013 DLAB: aliased_ok={aliased_ok} flat_ok={flat_ok} "
                f"divisor_write_did_not_push={no_push} ier_ok={ier_ok} "
                f"thr_ok={thr_ok}")
            return False
        except Exception as e:
            self.log.error(f"RLB-013 DLAB test error: {e}")
            return False

    async def test_rlb013_stop_bits_and_afe(self) -> bool:
        """RLB-013: 1.5 stop bits for a 5-bit word, and auto flow control.

        A 5-bit character with LCR[2] set sends 1.5 stop bits, so the frame
        is half a bit time longer than the same character with one stop bit.
        With AFE set, CTS gates the start of a character and RTS is driven
        from the RX FIFO level rather than from MCR[1]."""
        self.log.info("=== RLB-013: 1.5 stop bits and auto flow control ===")
        from .uart_16550_tb import UART16550RegisterMap
        M = UART16550RegisterMap
        try:
            # --- 1.5 stop bits: measure the frame on the wire ---
            async def frame_bit_times(stop_bits):
                # Measure how long the transmitter is out of TX_IDLE for one
                # character. Edges on the wire cannot answer this: a data bit
                # is indistinguishable from a start bit, and the trailing idle
                # is exactly what differs between the two cases.
                await self._hard_reset()
                await self.tb.configure_line(word_length=5, stop_bits=stop_bits,
                                             parity=None)
                divisor = 8
                await self.tb.set_baud_divisor(divisor)
                await self.tb.reset_fifos()
                await self.tb.enable_fifos(rx_trigger=1)
                core = self.tb.dut.u_uart_config_regs.u_uart_core
                bit = 16 * divisor
                await self.tb.write_register(M.UART_DATA, 0x0A)
                for _ in range(60 * bit):
                    if int(core.r_tx_state.value) != 0:
                        break
                    await ClockCycles(self.tb.pclk, 1)
                n = 0
                for _ in range(60 * bit):
                    await ClockCycles(self.tb.pclk, 1)
                    n += 1
                    if int(core.r_tx_state.value) == 0:
                        break
                return n / float(bit)

            one_stop = await frame_bit_times(1)
            long_stop = await frame_bit_times(2)
            delta = long_stop - one_stop
            # 1 start + 5 data + 1 stop = 7 bit times; with 1.5 stop, 7.5.
            stop_ok = 0.25 < delta < 0.75
            self.log.info(f"  5-bit frame: 1 stop = {one_stop:.2f} bit times, "
                          f"1.5 stop = {long_stop:.2f} (delta {delta:.2f}, want ~0.5)")

            # --- AFE: CTS gates the transmitter ---
            await self._hard_reset()
            await self.tb.configure_line(word_length=8, stop_bits=1, parity=None)
            await self.tb.set_baud_divisor(54)
            await self.tb.reset_fifos()
            await self.tb.enable_fifos(rx_trigger=4)
            self.tb.set_cts(False)                    # far end says stop
            await self.tb.write_register(M.UART_MCR, 0x02 | 0x20)  # RTS + AFE
            await self.tb.write_register(M.UART_DATA, 0x41)
            await ClockCycles(self.tb.pclk, 16 * 54 * 4)
            held = int(self.tb.dut.uart_tx.value) == 1     # never left idle
            self.tb.set_cts(True)
            started = False
            for _ in range(16 * 54 * 6):
                await ClockCycles(self.tb.pclk, 1)
                if int(self.tb.dut.uart_tx.value) == 0:
                    started = True
                    break
            self.log.info(f"  AFE TX gating: held while CTS off = {held}, "
                          f"started once CTS on = {started}")

            # --- AFE: RTS follows the RX FIFO level ---
            # Start the receive half from a known-empty FIFO: the TX gating
            # phase above leaves characters in it.
            await self.tb.reset_fifos()
            await self.tb.enable_fifos(rx_trigger=4)
            await self.tb.write_register(M.UART_MCR, 0x02 | 0x20)
            core = self.tb.dut.u_uart_config_regs.u_uart_core
            cnt_empty = int(core.w_rx_fifo_count.value)
            rts_idle = self.tb.get_rts()
            for ch in (0x61, 0x62, 0x63, 0x64):
                await self._drive_raw_frame(ch, 8, parity_bit=None, stop_bit=1)
                await ClockCycles(self.tb.pclk, 20)
            cnt_full = int(core.w_rx_fifo_count.value)
            rts_full = self.tb.get_rts()
            for _ in range(4):
                await self.tb.read_register(M.UART_DATA)
                await ClockCycles(self.tb.pclk, 10)
            cnt_drained = int(core.w_rx_fifo_count.value)
            rts_drained = self.tb.get_rts()
            self.log.info(f"  AFE RTS fifo count: empty={cnt_empty} "
                          f"at_trigger={cnt_full} after_drain={cnt_drained}")
            self.log.info(f"  AFE RTS: idle={rts_idle} at_trigger={rts_full} "
                          f"after_drain={rts_drained}")
            rts_ok = rts_idle and (not rts_full) and rts_drained

            ok = stop_ok and held and started and rts_ok
            if ok:
                self.log.info("RLB-013 stop bits and AFE GREEN")
                return True
            self.log.error(
                f"RLB-013: stop_ok={stop_ok} (delta {delta:.2f} bit times, "
                f"want ~0.5) tx_held_while_cts_off={held} tx_started_on_cts={started} "
                f"rts_ok={rts_ok} (idle={rts_idle} at_trigger={rts_full} "
                f"drained={rts_drained})")
            return False
        except Exception as e:
            self.log.error(f"RLB-013 stop-bits/AFE test error: {e}")
            return False

    async def test_rlb013_dma_mode(self) -> bool:
        """RLB-013: FCR[3] selects the DMA handshake mode on rxrdy_n/txrdy_n.

        Mode 0 is one character at a time: receive is requested as soon as
        anything is in the RX FIFO. Mode 1 is block: the request waits for the
        trigger level. Both are active low."""
        self.log.info("=== RLB-013: DMA mode select ===")
        from .uart_16550_tb import UART16550RegisterMap
        M = UART16550RegisterMap
        try:
            results = {}
            for mode in (0, 1):
                await self._hard_reset()
                await self.tb.configure_line(word_length=8, stop_bits=1, parity=None)
                await self.tb.set_baud_divisor(54)
                await self.tb.reset_fifos()
                # FCR: enable, trigger level 4 (bits 7:6 = 01), DMA mode bit 3
                await self.tb.write_register(M.UART_FCR,
                                             0x01 | 0x40 | (0x08 if mode else 0x00))
                empty_rx = int(self.tb.dut.rxrdy_n.value)
                await self._drive_raw_frame(0x41, 8, parity_bit=None, stop_bit=1)
                await ClockCycles(self.tb.pclk, 200)
                one_char = int(self.tb.dut.rxrdy_n.value)
                for ch in (0x42, 0x43, 0x44):
                    await self._drive_raw_frame(ch, 8, parity_bit=None, stop_bit=1)
                    await ClockCycles(self.tb.pclk, 50)
                await ClockCycles(self.tb.pclk, 200)
                at_trigger = int(self.tb.dut.rxrdy_n.value)
                results[mode] = (empty_rx, one_char, at_trigger)
                self.log.info(f"  mode {mode}: rxrdy_n empty={empty_rx} "
                              f"one_char={one_char} at_trigger={at_trigger}")

            # Mode 0 requests on the first character; mode 1 waits for the
            # trigger level. Both are idle (high) with an empty FIFO.
            mode0_ok = results[0] == (1, 0, 0)
            mode1_ok = results[1] == (1, 1, 0)
            ok = mode0_ok and mode1_ok
            if ok:
                self.log.info("RLB-013 DMA mode GREEN")
                return True
            self.log.error(
                f"RLB-013 DMA mode: mode0={results[0]} (want empty=1, "
                f"one_char=0, at_trigger=0) mode1={results[1]} (want "
                f"empty=1, one_char=1, at_trigger=0)")
            return False
        except Exception as e:
            self.log.error(f"RLB-013 DMA mode test error: {e}")
            return False

    async def test_rlb013_character_timeout(self) -> bool:
        """RLB-013: the character-timeout interrupt.

        PC16550D: with the RX FIFO non-empty and neither a new character nor
        a read for four character times, the timeout asserts, IIR reads 0x0C
        and it clears on a read of RBR. It only exists in FIFO mode, where a
        partially filled FIFO below the trigger level would otherwise leave
        software with no interrupt to wait for."""
        self.log.info("=== RLB-013: character timeout ===")
        from .uart_16550_tb import UART16550RegisterMap
        M = UART16550RegisterMap
        try:
            await self._hard_reset()
            await self.tb.configure_line(word_length=8, stop_bits=1, parity=None)
            await self.tb.set_baud_divisor(54)
            await self.tb.reset_fifos()
            await self.tb.enable_fifos(rx_trigger=8)   # above what we will send
            await self.tb.enable_loopback(False)
            await self.tb.write_register(M.UART_IER, M.IER_RX_DATA_AVAIL)
            await self.tb.write_register(M.UART_MCR, 0x08)  # OUT2 routes irq

            # Two characters, well under the trigger level of 8.
            for ch in (ord('a'), ord('b')):
                await self._drive_raw_frame(ch, 8, parity_bit=None, stop_bit=1)
                await ClockCycles(self.tb.pclk, 20)

            # Before four character times have passed there is no interrupt.
            iir_early = await self.tb.read_register(M.UART_IIR)
            iir_early = iir_early[1] & 0xFF
            early_quiet = (iir_early & M.IIR_TIMEOUT_PENDING) == 0

            # One character time here is 10 bits x 16 ticks x 54 pclk per tick.
            char_pclk = 10 * 16 * 54
            await ClockCycles(self.tb.pclk, 5 * char_pclk)

            _, iir_late = await self.tb.read_register(M.UART_IIR)
            iir_late &= 0xFF
            irq_now = int(self.tb.dut.irq.value)
            fired = ((iir_late & M.IIR_TIMEOUT_PENDING) != 0 and
                     (iir_late & M.IIR_INT_NOT_PENDING) == 0 and
                     (iir_late & M.IIR_INT_ID_MASK) == 0x04)
            self.log.info(f"  IIR early=0x{iir_early:02X} late=0x{iir_late:02X} "
                          f"(want 0x0C) irq={irq_now}")

            # Reading the data clears it.
            _, first = await self.tb.read_register(M.UART_DATA)
            await ClockCycles(self.tb.pclk, 20)
            _, iir_after = await self.tb.read_register(M.UART_IIR)
            cleared = (iir_after & M.IIR_TIMEOUT_PENDING) == 0
            self.log.info(f"  after RBR read (0x{first & 0xFF:02X}): "
                          f"IIR=0x{iir_after & 0xFF:02X}")

            # Character mode has no timeout source.
            await self._hard_reset()
            await self.tb.configure_line(word_length=8, stop_bits=1, parity=None)
            await self.tb.set_baud_divisor(54)
            await self.tb.write_register(M.UART_FCR, 0x00)
            await self.tb.write_register(M.UART_IER, M.IER_RX_DATA_AVAIL)
            await self._drive_raw_frame(ord('c'), 8, parity_bit=None, stop_bit=1)
            await ClockCycles(self.tb.pclk, 5 * char_pclk)
            _, iir_cm = await self.tb.read_register(M.UART_IIR)
            char_mode_quiet = (iir_cm & M.IIR_TIMEOUT_PENDING) == 0

            ok = early_quiet and fired and cleared and char_mode_quiet and irq_now == 1
            if ok:
                self.log.info("RLB-013 character timeout GREEN")
                return True
            self.log.error(
                f"RLB-013: early_quiet={early_quiet} fired={fired} "
                f"irq={irq_now} cleared_on_read={cleared} "
                f"character_mode_quiet={char_mode_quiet} "
                f"(IIR early=0x{iir_early:02X} late=0x{iir_late:02X} "
                f"after=0x{iir_after & 0xFF:02X})")
            return False
        except Exception as e:
            self.log.error(f"RLB-013 character timeout test error: {e}")
            return False

    async def test_gh60_r3_1_lsr7_is_a_fifo_aggregate(self) -> bool:
        """R3-1: LSR[7] must aggregate over the WHOLE RX FIFO.

        PC16550D defines it in FIFO mode as "at least one parity error,
        framing error or break indication in the FIFO". Deriving it from
        the entry at the read pointer makes it read 0 whenever a tagged
        character is queued behind a clean one, so software that polls
        LSR[7] to decide whether to inspect the stream misses the error
        entirely. Receive a clean 'A', a parity-error character, then two
        clean ones without reading RBR: LSR[7] must be set from the moment
        the bad character lands and must stay set until that character has
        been read out. It is a FIFO-mode bit, so it must read 0 with
        FCR[0] clear."""
        self.log.info("=== GH60-R3-1: LSR[7] is an aggregate over the whole FIFO ===")
        from .uart_16550_tb import UART16550RegisterMap
        M = UART16550RegisterMap
        try:
            await self._hard_reset()
            await self.tb.configure_line(word_length=8, stop_bits=1, parity='even')
            await self.tb.set_baud_divisor(54)
            await self.tb.reset_fifos()
            await self.tb.enable_fifos(rx_trigger=4)
            await self.tb.enable_loopback(False)

            chars = [ord('A'), 0xC3, ord('C'), ord('D')]
            after_each = []
            for idx, ch in enumerate(chars):
                correct = bin(ch).count('1') % 2
                bit = (1 - correct) if idx == 1 else correct
                await self._drive_raw_frame(ch, 8, parity_bit=bit, stop_bit=1)
                await ClockCycles(self.tb.pclk, 50)
                lsr = await self.tb.get_line_status()
                after_each.append(bool(lsr & M.LSR_RX_FIFO_ERROR))
                self.log.info(f"  after char {idx} (0x{ch:02X}): LSR[7]={after_each[-1]}")

            # Set from the arrival of the bad character, and still set while
            # it sits behind the clean 'A'.
            arrival_ok = (not after_each[0]) and all(after_each[1:])

            # Now drain. LSR[7] must stay set until the tagged character has
            # been handed over, and clear once it has.
            during = []
            for i in range(4):
                _, raw = await self.tb.read_register(M.UART_DATA)
                lsr = await self.tb.get_line_status()
                during.append((raw & 0xFF, bool(lsr & M.LSR_RX_FIFO_ERROR)))
                self.log.info(f"  read {i}: byte=0x{during[-1][0]:02X}, "
                              f"LSR[7]={during[-1][1]}")

            # After reading 'A' the tagged byte is still queued -> still set.
            # After reading it -> clear, and stays clear.
            drain_ok = during[0][1] and (not during[1][1]) and \
                       (not during[2][1]) and (not during[3][1])

            # FIFO-mode bit only.
            await self._hard_reset()
            await self.tb.configure_line(word_length=8, stop_bits=1, parity='even')
            await self.tb.set_baud_divisor(54)
            await self.tb.write_register(M.UART_FCR, 0x00)
            correct = bin(0xC3).count('1') % 2
            await self._drive_raw_frame(0xC3, 8, parity_bit=1 - correct, stop_bit=1)
            await ClockCycles(self.tb.pclk, 250)
            lsr = await self.tb.get_line_status()
            char_mode_ok = not bool(lsr & M.LSR_RX_FIFO_ERROR)
            self.log.info(f"  character mode: LSR[7]={not char_mode_ok} (want False)")

            ok = arrival_ok and drain_ok and char_mode_ok
            if ok:
                self.log.info("GH60-R3-1 GREEN")
                return True
            self.log.error(
                f"GH60-R3-1: LSR[7] is not a FIFO aggregate - "
                f"after_each={after_each} (want [False, True, True, True]), "
                f"drain={during} (want LSR[7] True on the read that returns "
                f"'A', False from the read that returns 0xC3 onward), "
                f"character_mode_reads_zero={char_mode_ok}")
            return False
        except Exception as e:
            self.log.error(f"GH60-R3-1 test error: {e}")
            return False

    async def test_gh60_r2_4_continuous_break_floods_fifo(self) -> bool:
        """R2-4 (LOW/MED): RX_IDLE re-arms on a still-low line with no
        guard against re-framing mid-break, so a break held for N
        character times loads N zero characters (eventually
        overrunning the FIFO) instead of exactly one break-tagged
        character followed by silence until the line returns to
        marking and a genuine new start bit arrives."""
        self.log.info("=== GH60-R2-4: continuous break must load exactly one character ===")
        from .uart_16550_tb import UART16550RegisterMap
        core = self.tb.dut.u_uart_config_regs.u_uart_core
        try:
            await self._hard_reset()
            await self.tb.configure_line(word_length=8, stop_bits=1, parity='none')
            await self.tb.set_baud_divisor(54)
            await self.tb.enable_fifos(rx_trigger=1)
            await self.tb.reset_fifos()
            await self.tb.enable_loopback(False)

            char_time_cycles = self.tb.clks_per_bit * 10  # start+8 data+stop
            self.tb.dut.uart_rx.value = 0
            await ClockCycles(self.tb.pclk, char_time_cycles * 10)
            self.tb.dut.uart_rx.value = 1
            await ClockCycles(self.tb.pclk, char_time_cycles * 2)

            level = int(core.w_rx_fifo_count.value)
            lsr = await self.tb.get_line_status()

            self.log.info(
                f"  after a 10-character-time break: rx_fifo_count="
                f"{level} (want exactly 1), LSR=0x{lsr:02X}")

            if level == 1:
                self.log.info("GH60-R2-4 GREEN")
                return True

            self.log.error(
                f"GH60-R2-4: a continuous break held for 10 character "
                f"times loaded rx_fifo_count={level} characters (want "
                f"exactly 1) - RX_IDLE re-arms on a still-low line with "
                f"no guard against reframing mid-break.")
            return False
        except Exception as e:
            self.log.error(f"GH60-R2-4 test error: {e}")
            return False

    async def test_gh60_r2_5_tx_fifo_reset_truncates_inflight_char(self) -> bool:
        """R2-5 (LOW/MED): FCR[2] TX FIFO reset unconditionally forces
        r_tx_state <= TX_IDLE (uart_16550_core.sv ~line 330-332),
        truncating whatever character is currently being shifted out
        on the wire instead of only resetting the FIFO's counters/
        pointers. Write FCR[2]=1 while a character is mid-transmission
        (state==TX_DATA) and assert the far end still sees a
        complete, well-formed byte."""
        self.log.info("=== GH60-R2-5: TX FIFO reset must not truncate an in-flight character ===")
        from .uart_16550_tb import UART16550RegisterMap
        TX_DATA_STATE = 2  # typedef enum: TX_IDLE=0,TX_START=1,TX_DATA=2,...
        core = self.tb.dut.u_uart_config_regs.u_uart_core
        try:
            await self._hard_reset()
            await self.tb.basic_init()
            await self.tb.enable_loopback(False)
            self.tb.clear_rx_queue()

            await self.tb.write_register(UART16550RegisterMap.UART_DATA, 0x5A)

            reached_tx_data = False
            for _ in range(2000):
                await RisingEdge(self.tb.pclk)
                if int(core.r_tx_state.value) == TX_DATA_STATE:
                    reached_tx_data = True
                    break

            fcr = (UART16550RegisterMap.FCR_FIFO_ENABLE |
                   UART16550RegisterMap.FCR_TX_FIFO_RESET)
            await self.tb.write_register(UART16550RegisterMap.UART_FCR, fcr)

            await ClockCycles(self.tb.pclk, self.tb.clks_per_bit * 14)

            packets = self.tb.get_received_packets()
            wire_ok = (len(packets) >= 1 and packets[0].data == 0x5A)

            self.log.info(
                f"  reached_tx_data={reached_tx_data}, packets="
                f"{[hex(p.data) for p in packets]}, wire_ok={wire_ok}")

            if reached_tx_data and wire_ok:
                self.log.info("GH60-R2-5 GREEN")
                return True

            self.log.error(
                f"GH60-R2-5: TX FIFO reset mid-character truncated the "
                f"byte on the wire - reached_tx_data={reached_tx_data}, "
                f"received packets={[hex(p.data) for p in packets]} "
                f"(want [0x5A]).")
            return False
        except Exception as e:
            self.log.error(f"GH60-R2-5 test error: {e}")
            return False

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
            ('GH60-C3 RBR/THR bit separation', self.test_gh60_c3_rbr_thr_bit_separation),
            ('GH60-C6 LSR/MSR clear-on-read', self.test_gh60_c6_lsr_msr_clear_on_read),
            ('GH60-QC1 framing error and break must assert', self.test_gh60_qc1_framing_error_and_break_must_assert),
            ('GH60-QC2 short-word RX justification', self.test_gh60_qc2_short_word_rx_justification),
            ('GH60-QC3-1 gapless THR writes', self.test_gh60_qc3_1_thr_gapless_writes),
            ('GH60-IER interrupt enable gating', self.test_gh60_ier_gating),
            ('GH60-GUARD RX trigger levels', self.test_gh60_guard_rx_trigger_levels),
            ('GH60 strict decode missing (unmapped never PSLVERR)', self.test_gh60_strict_decode_missing),
            ('GH60-R2-1 THR byte-enable masked push', self.test_gh60_r2_1_thr_byte_enable_masked),
            ('GH60-R2-2 FCR[0] disable not honored', self.test_gh60_r2_2_fifo_disable_not_honored),
            ('GH60-R2-3 LSR error not per-character', self.test_gh60_r2_3_lsr_error_not_per_character),
            ('GH60-R2-4 continuous break floods FIFO', self.test_gh60_r2_4_continuous_break_floods_fifo),
            ('GH60-R3-1 LSR[7] is a FIFO aggregate', self.test_gh60_r3_1_lsr7_is_a_fifo_aggregate),
            ('RLB-013 character timeout', self.test_rlb013_character_timeout),
            ('RLB-013 DLAB remapping', self.test_rlb013_dlab_remap),
            ('RLB-013 1.5 stop bits and AFE', self.test_rlb013_stop_bits_and_afe),
            ('RLB-013 DMA mode select', self.test_rlb013_dma_mode),
            ('GH60-R2-5 TX FIFO reset truncates in-flight char', self.test_gh60_r2_5_tx_fifo_reset_truncates_inflight_char),
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
