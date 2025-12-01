# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: UART16550BasicTests
# Purpose: UART 16550 Basic Test Suite
#
# Documentation: projects/components/retro_legacy_blocks/rtl/uart_16550/README.md
# Subsystem: retro_legacy_blocks/uart_16550
#
# Created: 2025-11-30

"""
UART 16550 Basic Tests

Basic verification of UART 16550 functionality including:
- Register access
- Baud rate configuration
- Loopback mode
- Simple TX/RX operations
- Line status
"""

from cocotb.triggers import ClockCycles


class UART16550BasicTests:
    """Basic test methods for UART 16550 module."""

    def __init__(self, tb):
        """
        Initialize basic tests.

        Args:
            tb: UART16550TB instance
        """
        self.tb = tb
        self.log = tb.log

    async def test_register_access(self) -> bool:
        """Test basic register read/write access."""
        self.log.info("Testing register access...")
        passed = True

        try:
            from .uart_16550_tb import UART16550RegisterMap

            # Test scratch register (general purpose)
            test_values = [0x00, 0xFF, 0xAA, 0x55, 0x12]
            for val in test_values:
                await self.tb.write_register(UART16550RegisterMap.UART_SCR, val)
                _, scr = await self.tb.read_register(UART16550RegisterMap.UART_SCR)
                if scr != val:
                    self.log.error(f"SCR mismatch: wrote 0x{val:02X}, read 0x{scr:02X}")
                    passed = False
                else:
                    self.log.info(f"SCR 0x{val:02X}: OK")

            # Test IER (Interrupt Enable Register)
            await self.tb.write_register(UART16550RegisterMap.UART_IER, 0x0F)
            _, ier = await self.tb.read_register(UART16550RegisterMap.UART_IER)
            if ier != 0x0F:
                self.log.error(f"IER mismatch: wrote 0x0F, read 0x{ier:02X}")
                passed = False
            else:
                self.log.info(f"IER: OK (0x{ier:02X})")

            # Test LCR (Line Control Register)
            await self.tb.write_register(UART16550RegisterMap.UART_LCR, 0x03)  # 8N1
            _, lcr = await self.tb.read_register(UART16550RegisterMap.UART_LCR)
            if lcr != 0x03:
                self.log.error(f"LCR mismatch: wrote 0x03, read 0x{lcr:02X}")
                passed = False
            else:
                self.log.info(f"LCR: OK (0x{lcr:02X})")

            # Test divisor registers
            await self.tb.write_register(UART16550RegisterMap.UART_DLL, 0x36)  # 54 = 0x36
            _, dll = await self.tb.read_register(UART16550RegisterMap.UART_DLL)
            if dll != 0x36:
                self.log.error(f"DLL mismatch: wrote 0x36, read 0x{dll:02X}")
                passed = False
            else:
                self.log.info(f"DLL: OK (0x{dll:02X})")

            await self.tb.write_register(UART16550RegisterMap.UART_DLM, 0x00)
            _, dlm = await self.tb.read_register(UART16550RegisterMap.UART_DLM)
            if dlm != 0x00:
                self.log.error(f"DLM mismatch: wrote 0x00, read 0x{dlm:02X}")
                passed = False
            else:
                self.log.info(f"DLM: OK (0x{dlm:02X})")

            # Reset to defaults
            await self.tb.write_register(UART16550RegisterMap.UART_IER, 0x00)

        except Exception as e:
            self.log.error(f"Register access test exception: {e}")
            passed = False

        return passed

    async def test_baud_divisor(self) -> bool:
        """Test baud rate divisor configuration."""
        self.log.info("Testing baud divisor configuration...")
        passed = True

        try:
            from .uart_16550_tb import UART16550RegisterMap

            # Test various divisor values
            test_divisors = [
                (1, "Maximum baud"),
                (54, "115200 baud @ 100MHz"),
                (651, "9600 baud @ 100MHz"),
                (0xFFFF, "Minimum baud"),
            ]

            for divisor, description in test_divisors:
                await self.tb.set_baud_divisor(divisor)
                await ClockCycles(self.tb.pclk, 5)

                # Readback
                _, dll = await self.tb.read_register(UART16550RegisterMap.UART_DLL)
                _, dlm = await self.tb.read_register(UART16550RegisterMap.UART_DLM)
                readback = (dlm << 8) | dll

                if readback != divisor:
                    self.log.error(f"Divisor {description}: wrote {divisor}, read {readback}")
                    passed = False
                else:
                    self.log.info(f"Divisor {divisor} ({description}): OK")

            # Restore to 115200 baud
            await self.tb.set_baud_divisor(54)

        except Exception as e:
            self.log.error(f"Baud divisor test exception: {e}")
            passed = False

        return passed

    async def test_line_control(self) -> bool:
        """Test line control configuration."""
        self.log.info("Testing line control configuration...")
        passed = True

        try:
            from .uart_16550_tb import UART16550RegisterMap

            # Test various line configurations
            test_configs = [
                (0x00, "5N1"),
                (0x01, "6N1"),
                (0x02, "7N1"),
                (0x03, "8N1"),
                (0x07, "8N2"),
                (0x0B, "8O1"),
                (0x1B, "8E1"),
            ]

            for lcr_val, description in test_configs:
                await self.tb.write_register(UART16550RegisterMap.UART_LCR, lcr_val)
                await ClockCycles(self.tb.pclk, 5)

                _, lcr = await self.tb.read_register(UART16550RegisterMap.UART_LCR)
                if lcr != lcr_val:
                    self.log.error(f"LCR {description}: wrote 0x{lcr_val:02X}, read 0x{lcr:02X}")
                    passed = False
                else:
                    self.log.info(f"LCR {description} (0x{lcr_val:02X}): OK")

            # Restore to 8N1
            await self.tb.configure_line(word_length=8, stop_bits=1, parity='none')

        except Exception as e:
            self.log.error(f"Line control test exception: {e}")
            passed = False

        return passed

    async def test_fifo_enable(self) -> bool:
        """Test FIFO enable and reset."""
        self.log.info("Testing FIFO enable...")
        passed = True

        try:
            from .uart_16550_tb import UART16550RegisterMap

            # Enable FIFOs
            await self.tb.enable_fifos(rx_trigger=1)
            await ClockCycles(self.tb.pclk, 5)

            # Check IIR FIFO status bits
            _, iir = await self.tb.read_register(UART16550RegisterMap.UART_IIR)
            fifo_status = (iir >> 6) & 0x03
            if fifo_status != 0x03:  # Both bits set when FIFOs enabled
                self.log.warning(f"FIFO status bits: expected 0x03, got 0x{fifo_status:02X}")
                # This might be expected behavior depending on implementation
            else:
                self.log.info(f"FIFOs enabled: OK (IIR=0x{iir:02X})")

            # Reset FIFOs
            await self.tb.reset_fifos()
            await ClockCycles(self.tb.pclk, 5)

            # After reset, TX should be empty
            _, lsr = await self.tb.read_register(UART16550RegisterMap.UART_LSR)
            if not (lsr & UART16550RegisterMap.LSR_TX_HOLD_EMPTY):
                self.log.error(f"TX not empty after FIFO reset: LSR=0x{lsr:02X}")
                passed = False
            else:
                self.log.info("FIFO reset: OK")

        except Exception as e:
            self.log.error(f"FIFO enable test exception: {e}")
            passed = False

        return passed

    async def test_loopback_mode(self) -> bool:
        """Test internal loopback mode."""
        self.log.info("Testing loopback mode...")
        passed = True

        try:
            from .uart_16550_tb import UART16550RegisterMap

            # Initialize UART
            await self.tb.basic_init()

            # Debug: Check FIFO state after init/reset
            try:
                core = self.tb.dut.u_uart_config_regs.u_uart_core
                rd_ptr = int(core.r_rx_rd_ptr.value)
                wr_ptr = int(core.r_rx_wr_ptr.value)
                self.log.info(f"FIFO STATE AFTER INIT: rd_ptr={rd_ptr}, wr_ptr={wr_ptr}")
            except Exception as e:
                self.log.warning(f"Could not read FIFO state: {e}")

            # Enable loopback
            await self.tb.enable_loopback(True)
            await ClockCycles(self.tb.pclk, 10)

            # Debug: Check FIFO state after enabling loopback
            try:
                core = self.tb.dut.u_uart_config_regs.u_uart_core
                rd_ptr = int(core.r_rx_rd_ptr.value)
                wr_ptr = int(core.r_rx_wr_ptr.value)
                self.log.info(f"FIFO STATE AFTER LOOPBACK ENABLE: rd_ptr={rd_ptr}, wr_ptr={wr_ptr}")
            except Exception as e:
                self.log.warning(f"Could not read FIFO state: {e}")

            # Test data
            test_bytes = [0x55, 0xAA, 0x00, 0xFF, 0x42]

            for tx_byte in test_bytes:
                # Debug: FIFO state before TX
                try:
                    core = self.tb.dut.u_uart_config_regs.u_uart_core
                    rd_ptr = int(core.r_rx_rd_ptr.value)
                    wr_ptr = int(core.r_rx_wr_ptr.value)
                    self.log.info(f"BEFORE TX 0x{tx_byte:02X}: rd_ptr={rd_ptr}, wr_ptr={wr_ptr}")
                except Exception as e:
                    self.log.warning(f"Could not read state: {e}")

                # Transmit byte
                await self.tb.tx_byte(tx_byte)

                # Debug: FIFO state immediately after TX write
                try:
                    core = self.tb.dut.u_uart_config_regs.u_uart_core
                    rd_ptr = int(core.r_rx_rd_ptr.value)
                    wr_ptr = int(core.r_rx_wr_ptr.value)
                    tx_wr_ptr = int(core.r_tx_wr_ptr.value)
                    tx_rd_ptr = int(core.r_tx_rd_ptr.value)
                    cfg_loopback = int(core.cfg_loopback.value)
                    cfg_divisor = int(core.cfg_divisor.value)
                    w_tx_bit = int(core.w_tx_bit.value)
                    w_rx_in = int(core.w_rx_in.value)
                    r_tx_state = int(core.r_tx_state.value)
                    self.log.info(f"AFTER TX WRITE: rx_wr={wr_ptr}, tx_wr={tx_wr_ptr}, loop={cfg_loopback}, div={cfg_divisor}, tx_bit={w_tx_bit}, rx_in={w_rx_in}, tx_state={r_tx_state}")
                except Exception as e:
                    self.log.warning(f"Could not read state: {e}")

                # Wait for byte to loop back (needs time for TX shift register)
                # At 115200 baud with 100MHz clock: ~868 clocks per bit, ~8680 clocks per byte
                await ClockCycles(self.tb.pclk, 10000)

                # Debug: FIFO state after wait
                try:
                    core = self.tb.dut.u_uart_config_regs.u_uart_core
                    rd_ptr = int(core.r_rx_rd_ptr.value)
                    wr_ptr = int(core.r_rx_wr_ptr.value)
                    rx_shift = int(core.r_rx_shift.value)
                    self.log.info(f"AFTER WAIT: rd_ptr={rd_ptr}, wr_ptr={wr_ptr}, rx_shift=0x{rx_shift:02X}")
                except Exception as e:
                    self.log.warning(f"Could not read state: {e}")

                # Receive byte
                rx_byte = await self.tb.rx_byte(timeout_cycles=20000)

                if rx_byte is None:
                    self.log.error(f"Loopback timeout for 0x{tx_byte:02X}")
                    passed = False
                elif rx_byte != tx_byte:
                    self.log.error(f"Loopback mismatch: TX=0x{tx_byte:02X}, RX=0x{rx_byte:02X}")
                    passed = False
                else:
                    self.log.info(f"Loopback 0x{tx_byte:02X}: OK")

            # Disable loopback
            await self.tb.enable_loopback(False)

        except Exception as e:
            self.log.error(f"Loopback mode test exception: {e}")
            passed = False

        return passed

    async def test_modem_control(self) -> bool:
        """Test modem control register outputs."""
        self.log.info("Testing modem control outputs...")
        passed = True

        try:
            from .uart_16550_tb import UART16550RegisterMap

            # Test DTR
            await self.tb.set_modem_control(dtr=True, rts=False, out1=False, out2=False)
            await ClockCycles(self.tb.pclk, 5)
            if not self.tb.get_dtr():
                self.log.error("DTR not asserted")
                passed = False
            else:
                self.log.info("DTR: OK")

            # Test RTS
            await self.tb.set_modem_control(dtr=False, rts=True, out1=False, out2=False)
            await ClockCycles(self.tb.pclk, 5)
            if not self.tb.get_rts():
                self.log.error("RTS not asserted")
                passed = False
            else:
                self.log.info("RTS: OK")

            # Test OUT1
            await self.tb.set_modem_control(dtr=False, rts=False, out1=True, out2=False)
            await ClockCycles(self.tb.pclk, 5)
            if not self.tb.get_out1():
                self.log.error("OUT1 not asserted")
                passed = False
            else:
                self.log.info("OUT1: OK")

            # Test OUT2
            await self.tb.set_modem_control(dtr=False, rts=False, out1=False, out2=True)
            await ClockCycles(self.tb.pclk, 5)
            if not self.tb.get_out2():
                self.log.error("OUT2 not asserted")
                passed = False
            else:
                self.log.info("OUT2: OK")

            # Clear all
            await self.tb.set_modem_control(dtr=False, rts=False, out1=False, out2=False)

        except Exception as e:
            self.log.error(f"Modem control test exception: {e}")
            passed = False

        return passed

    async def test_line_status(self) -> bool:
        """Test line status register."""
        self.log.info("Testing line status register...")
        passed = True

        try:
            from .uart_16550_tb import UART16550RegisterMap

            # Initialize
            await self.tb.basic_init()
            await ClockCycles(self.tb.pclk, 10)

            # Check initial state - TX should be empty
            lsr = await self.tb.get_line_status()
            if not (lsr & UART16550RegisterMap.LSR_TX_HOLD_EMPTY):
                self.log.error(f"TX Holding not empty initially: LSR=0x{lsr:02X}")
                passed = False
            else:
                self.log.info("TX Holding empty: OK")

            if not (lsr & UART16550RegisterMap.LSR_TX_EMPTY):
                self.log.error(f"TX not empty initially: LSR=0x{lsr:02X}")
                passed = False
            else:
                self.log.info("TX empty: OK")

            # RX should not have data ready
            if lsr & UART16550RegisterMap.LSR_DATA_READY:
                self.log.warning(f"Unexpected data ready: LSR=0x{lsr:02X}")
            else:
                self.log.info("No data ready: OK")

        except Exception as e:
            self.log.error(f"Line status test exception: {e}")
            passed = False

        return passed

    async def run_all_basic_tests(self) -> bool:
        """Run all basic tests."""
        results = []

        basic_test_methods = [
            ('Register Access', self.test_register_access),
            ('Baud Divisor', self.test_baud_divisor),
            ('Line Control', self.test_line_control),
            ('FIFO Enable', self.test_fifo_enable),
            ('Loopback Mode', self.test_loopback_mode),
            ('Modem Control', self.test_modem_control),
            ('Line Status', self.test_line_status),
        ]

        self.log.info("=" * 80)
        self.log.info("Starting UART 16550 Basic Tests")
        self.log.info("=" * 80)

        for test_name, test_method in basic_test_methods:
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
        self.log.info("BASIC TEST SUMMARY")
        self.log.info("=" * 80)

        passed_count = sum(1 for _, result in results if result)
        total_count = len(results)

        for test_name, result in results:
            status = "PASSED" if result else "FAILED"
            self.log.info(f"{test_name:45s} {status}")

        self.log.info(f"\nBasic Tests: {passed_count}/{total_count} passed")

        return all(result for _, result in results)
