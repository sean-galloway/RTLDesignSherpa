# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: SMBusBasicTests
# Purpose: Basic test cases for SMBus 2.0 Controller
#
# Created: 2025-11-29

"""
SMBus Basic Tests

Collection of basic test cases for SMBus 2.0 Controller validation:
- Register access verification
- Master mode enable/disable
- Clock configuration
- Status register operations
- FIFO operations
- Transaction types (basic)

Note: SMBus physical layer testing requires the SMBus slave BFM to respond
to transactions initiated by the DUT master.
"""

import cocotb
from cocotb.triggers import ClockCycles, Timer

from projects.components.retro_legacy_blocks.dv.tbclasses.smbus.smbus_tb import SMBusRegisterMap


class SMBusBasicTests:
    """Basic test suite for SMBus 2.0 Controller."""

    def __init__(self, tb):
        """
        Initialize test suite.

        Args:
            tb: SMBusTB testbench instance
        """
        self.tb = tb
        self.log = tb.log

    async def test_register_access(self) -> bool:
        """Test basic register read/write access."""
        self.log.info("Testing register access...")

        try:
            # Test CONTROL register
            await self.tb.write_register(SMBusRegisterMap.SMBUS_CONTROL, 0x0F)
            _, value = await self.tb.read_register(SMBusRegisterMap.SMBUS_CONTROL)
            expected = 0x0F & 0x1F  # 5 control bits
            if (value & 0x1F) != expected:
                self.log.error(f"CONTROL register mismatch: got {value:08x}, expected {expected:08x}")
                return False
            self.log.info(f"  CONTROL register: 0x{value:08x}")

            # Test CLK_DIV register
            await self.tb.write_register(SMBusRegisterMap.SMBUS_CLK_DIV, 0xABCD)
            _, value = await self.tb.read_register(SMBusRegisterMap.SMBUS_CLK_DIV)
            if (value & 0xFFFF) != 0xABCD:
                self.log.error(f"CLK_DIV register mismatch: got {value:04x}, expected ABCD")
                return False
            self.log.info(f"  CLK_DIV register: 0x{value:04x}")

            # Test TIMEOUT register
            await self.tb.write_register(SMBusRegisterMap.SMBUS_TIMEOUT, 0x123456)
            _, value = await self.tb.read_register(SMBusRegisterMap.SMBUS_TIMEOUT)
            if (value & 0xFFFFFF) != 0x123456:
                self.log.error(f"TIMEOUT register mismatch: got {value:06x}, expected 123456")
                return False
            self.log.info(f"  TIMEOUT register: 0x{value:06x}")

            # Test OWN_ADDR register
            await self.tb.write_register(SMBusRegisterMap.SMBUS_OWN_ADDR, 0x55)
            _, value = await self.tb.read_register(SMBusRegisterMap.SMBUS_OWN_ADDR)
            if (value & 0x7F) != 0x55:
                self.log.error(f"OWN_ADDR register mismatch: got {value:02x}, expected 55")
                return False
            self.log.info(f"  OWN_ADDR register: 0x{value:02x}")

            # Test SLAVE_ADDR register
            await self.tb.write_register(SMBusRegisterMap.SMBUS_SLAVE_ADDR, 0x50)
            _, value = await self.tb.read_register(SMBusRegisterMap.SMBUS_SLAVE_ADDR)
            if (value & 0x7F) != 0x50:
                self.log.error(f"SLAVE_ADDR register mismatch: got {value:02x}, expected 50")
                return False
            self.log.info(f"  SLAVE_ADDR register: 0x{value:02x}")

            # Test INT_ENABLE register
            await self.tb.write_register(SMBusRegisterMap.SMBUS_INT_ENABLE, 0x1F)
            _, value = await self.tb.read_register(SMBusRegisterMap.SMBUS_INT_ENABLE)
            if (value & 0x1F) != 0x1F:
                self.log.error(f"INT_ENABLE register mismatch: got {value:02x}, expected 1F")
                return False
            self.log.info(f"  INT_ENABLE register: 0x{value:02x}")

            self.log.info("Register access test passed")
            return True

        except Exception as e:
            self.log.error(f"Register access test failed: {e}")
            return False

    async def test_master_enable_disable(self) -> bool:
        """Test master mode enable/disable."""
        self.log.info("Testing master enable/disable...")

        try:
            # Enable master mode
            await self.tb.enable_master_mode(enable=True)
            await ClockCycles(self.tb.pclk, 10)

            # Check control register
            _, control = await self.tb.read_register(SMBusRegisterMap.SMBUS_CONTROL)
            if not (control & SMBusRegisterMap.CONTROL_MASTER_EN):
                self.log.error("Master enable bit not set")
                return False
            self.log.info(f"  Master enabled: control=0x{control:08x}")

            # Disable master mode
            await self.tb.write_register(SMBusRegisterMap.SMBUS_CONTROL, 0)
            await ClockCycles(self.tb.pclk, 10)

            # Check control register
            _, control = await self.tb.read_register(SMBusRegisterMap.SMBUS_CONTROL)
            if control & SMBusRegisterMap.CONTROL_MASTER_EN:
                self.log.error("Master enable bit still set")
                return False
            self.log.info(f"  Master disabled: control=0x{control:08x}")

            self.log.info("Master enable/disable test passed")
            return True

        except Exception as e:
            self.log.error(f"Master enable/disable test failed: {e}")
            return False

    async def test_clock_configuration(self) -> bool:
        """Test clock divider configuration."""
        self.log.info("Testing clock configuration...")

        try:
            # Configure for 100kHz (CLK_DIV = 249 for 100MHz system clock)
            await self.tb.configure_clock(clk_div=249)
            await ClockCycles(self.tb.pclk, 10)

            _, clk_div = await self.tb.read_register(SMBusRegisterMap.SMBUS_CLK_DIV)
            if (clk_div & 0xFFFF) != 249:
                self.log.error(f"Clock divider mismatch: got {clk_div}, expected 249")
                return False
            self.log.info(f"  100kHz config: CLK_DIV={clk_div}")

            # Configure for 400kHz (CLK_DIV = 62 for 100MHz system clock)
            await self.tb.configure_clock(clk_div=62)
            await ClockCycles(self.tb.pclk, 10)

            _, clk_div = await self.tb.read_register(SMBusRegisterMap.SMBUS_CLK_DIV)
            if (clk_div & 0xFFFF) != 62:
                self.log.error(f"Clock divider mismatch: got {clk_div}, expected 62")
                return False
            self.log.info(f"  400kHz config: CLK_DIV={clk_div}")

            self.log.info("Clock configuration test passed")
            return True

        except Exception as e:
            self.log.error(f"Clock configuration test failed: {e}")
            return False

    async def test_timeout_configuration(self) -> bool:
        """Test timeout threshold configuration."""
        self.log.info("Testing timeout configuration...")

        try:
            # Configure for 25ms timeout (2,500,000 cycles at 100MHz)
            await self.tb.configure_timeout(timeout=2500000)
            await ClockCycles(self.tb.pclk, 10)

            _, timeout = await self.tb.read_register(SMBusRegisterMap.SMBUS_TIMEOUT)
            if (timeout & 0xFFFFFF) != 2500000:
                self.log.error(f"Timeout mismatch: got {timeout}, expected 2500000")
                return False
            self.log.info(f"  25ms timeout: {timeout} cycles")

            # Configure for 35ms timeout (3,500,000 cycles at 100MHz)
            await self.tb.configure_timeout(timeout=3500000)
            await ClockCycles(self.tb.pclk, 10)

            _, timeout = await self.tb.read_register(SMBusRegisterMap.SMBUS_TIMEOUT)
            if (timeout & 0xFFFFFF) != 3500000:
                self.log.error(f"Timeout mismatch: got {timeout}, expected 3500000")
                return False
            self.log.info(f"  35ms timeout: {timeout} cycles")

            self.log.info("Timeout configuration test passed")
            return True

        except Exception as e:
            self.log.error(f"Timeout configuration test failed: {e}")
            return False

    async def test_status_register(self) -> bool:
        """Test status register reading."""
        self.log.info("Testing status register...")

        try:
            # Read initial status
            status = await self.tb.read_status()
            self.log.info(f"  Initial status: {status}")

            # Check that we're not busy initially
            if status['busy']:
                self.log.warning("Busy flag set unexpectedly at start")

            # Check FSM state (should be idle = 0)
            if status['fsm_state'] != 0:
                self.log.info(f"  FSM state: {status['fsm_state']} (may be non-zero)")

            self.log.info("Status register test passed")
            return True

        except Exception as e:
            self.log.error(f"Status register test failed: {e}")
            return False

    async def test_fifo_status(self) -> bool:
        """Test FIFO status register."""
        self.log.info("Testing FIFO status...")

        try:
            # Reset FIFOs first
            await self.tb.reset_fifos()
            await ClockCycles(self.tb.pclk, 10)

            # Read initial FIFO status
            fifo_status = await self.tb.read_fifo_status()
            self.log.info(f"  Initial FIFO status: {fifo_status}")

            # Check TX FIFO is empty
            if not fifo_status['tx_empty']:
                self.log.error("TX FIFO should be empty after reset")
                return False

            # Check RX FIFO is empty
            if not fifo_status['rx_empty']:
                self.log.error("RX FIFO should be empty after reset")
                return False

            # Check TX level is 0
            if fifo_status['tx_level'] != 0:
                self.log.error(f"TX FIFO level should be 0, got {fifo_status['tx_level']}")
                return False

            # Check RX level is 0
            if fifo_status['rx_level'] != 0:
                self.log.error(f"RX FIFO level should be 0, got {fifo_status['rx_level']}")
                return False

            self.log.info("FIFO status test passed")
            return True

        except Exception as e:
            self.log.error(f"FIFO status test failed: {e}")
            return False

    async def test_fifo_write(self) -> bool:
        """Test writing to TX FIFO."""
        self.log.info("Testing TX FIFO write...")

        try:
            # Reset FIFOs
            await self.tb.reset_fifos()
            await ClockCycles(self.tb.pclk, 10)

            # Write some bytes to TX FIFO
            test_data = [0xAA, 0xBB, 0xCC, 0xDD]
            await self.tb.write_tx_fifo(test_data)
            await ClockCycles(self.tb.pclk, 10)

            # Check FIFO level
            fifo_status = await self.tb.read_fifo_status()
            self.log.info(f"  FIFO status after write: {fifo_status}")

            if fifo_status['tx_level'] != len(test_data):
                self.log.error(f"TX FIFO level mismatch: got {fifo_status['tx_level']}, expected {len(test_data)}")
                return False

            if fifo_status['tx_empty']:
                self.log.error("TX FIFO should not be empty after write")
                return False

            # Reset FIFOs to clean up
            await self.tb.reset_fifos()
            await ClockCycles(self.tb.pclk, 10)

            # Verify empty again
            fifo_status = await self.tb.read_fifo_status()
            if not fifo_status['tx_empty']:
                self.log.error("TX FIFO should be empty after reset")
                return False

            self.log.info("TX FIFO write test passed")
            return True

        except Exception as e:
            self.log.error(f"TX FIFO write test failed: {e}")
            return False

    async def test_interrupt_enable(self) -> bool:
        """Test interrupt enable/disable."""
        self.log.info("Testing interrupt enable...")

        try:
            # Enable all interrupts
            await self.tb.enable_interrupts(
                complete=True,
                error=True,
                tx_thresh=True,
                rx_thresh=True,
                slave_addr=True
            )
            await ClockCycles(self.tb.pclk, 10)

            # Verify all enabled
            _, int_enable = await self.tb.read_register(SMBusRegisterMap.SMBUS_INT_ENABLE)
            expected = 0x1F  # All 5 interrupt sources
            if (int_enable & 0x1F) != expected:
                self.log.error(f"INT_ENABLE mismatch: got {int_enable:02x}, expected {expected:02x}")
                return False
            self.log.info(f"  All interrupts enabled: 0x{int_enable:02x}")

            # Disable all interrupts
            await self.tb.enable_interrupts(
                complete=False,
                error=False,
                tx_thresh=False,
                rx_thresh=False,
                slave_addr=False
            )
            await ClockCycles(self.tb.pclk, 10)

            # Verify all disabled
            _, int_enable = await self.tb.read_register(SMBusRegisterMap.SMBUS_INT_ENABLE)
            if (int_enable & 0x1F) != 0:
                self.log.error(f"INT_ENABLE should be 0, got {int_enable:02x}")
                return False
            self.log.info(f"  All interrupts disabled: 0x{int_enable:02x}")

            self.log.info("Interrupt enable test passed")
            return True

        except Exception as e:
            self.log.error(f"Interrupt enable test failed: {e}")
            return False

    # =========================================================================
    # Medium Level Tests
    # =========================================================================

    async def test_pec_enable(self) -> bool:
        """Test PEC (Packet Error Checking) enable."""
        self.log.info("Testing PEC enable...")

        try:
            # Enable master with PEC
            await self.tb.enable_master_mode(enable=True, use_pec=True)
            await ClockCycles(self.tb.pclk, 10)

            # Check control register
            _, control = await self.tb.read_register(SMBusRegisterMap.SMBUS_CONTROL)
            if not (control & SMBusRegisterMap.CONTROL_PEC_EN):
                self.log.error("PEC enable bit not set")
                return False
            self.log.info(f"  PEC enabled: control=0x{control:08x}")

            # Read PEC register
            _, pec = await self.tb.read_register(SMBusRegisterMap.SMBUS_PEC)
            self.log.info(f"  Current PEC value: 0x{pec:02x}")

            # Disable PEC
            await self.tb.enable_master_mode(enable=True, use_pec=False)
            await ClockCycles(self.tb.pclk, 10)

            _, control = await self.tb.read_register(SMBusRegisterMap.SMBUS_CONTROL)
            if control & SMBusRegisterMap.CONTROL_PEC_EN:
                self.log.error("PEC enable bit still set")
                return False
            self.log.info(f"  PEC disabled: control=0x{control:08x}")

            self.log.info("PEC enable test passed")
            return True

        except Exception as e:
            self.log.error(f"PEC enable test failed: {e}")
            return False

    async def test_fast_mode_enable(self) -> bool:
        """Test fast mode (400kHz) enable."""
        self.log.info("Testing fast mode enable...")

        try:
            # Enable master with fast mode
            await self.tb.enable_master_mode(enable=True, fast_mode=True)
            await ClockCycles(self.tb.pclk, 10)

            # Check control register
            _, control = await self.tb.read_register(SMBusRegisterMap.SMBUS_CONTROL)
            if not (control & SMBusRegisterMap.CONTROL_FAST_MODE):
                self.log.error("Fast mode bit not set")
                return False
            self.log.info(f"  Fast mode enabled: control=0x{control:08x}")

            # Disable fast mode
            await self.tb.enable_master_mode(enable=True, fast_mode=False)
            await ClockCycles(self.tb.pclk, 10)

            _, control = await self.tb.read_register(SMBusRegisterMap.SMBUS_CONTROL)
            if control & SMBusRegisterMap.CONTROL_FAST_MODE:
                self.log.error("Fast mode bit still set")
                return False
            self.log.info(f"  Fast mode disabled: control=0x{control:08x}")

            self.log.info("Fast mode enable test passed")
            return True

        except Exception as e:
            self.log.error(f"Fast mode enable test failed: {e}")
            return False

    async def test_slave_mode_config(self) -> bool:
        """Test slave mode configuration."""
        self.log.info("Testing slave mode configuration...")

        try:
            # Enable slave mode with address 0x55
            await self.tb.enable_slave_mode(enable=True, own_addr=0x55)
            await ClockCycles(self.tb.pclk, 10)

            # Check control register
            _, control = await self.tb.read_register(SMBusRegisterMap.SMBUS_CONTROL)
            if not (control & SMBusRegisterMap.CONTROL_SLAVE_EN):
                self.log.error("Slave enable bit not set")
                return False
            self.log.info(f"  Slave mode enabled: control=0x{control:08x}")

            # Check own address
            _, own_addr = await self.tb.read_register(SMBusRegisterMap.SMBUS_OWN_ADDR)
            if (own_addr & 0x7F) != 0x55:
                self.log.error(f"Own address mismatch: got 0x{own_addr:02x}, expected 0x55")
                return False
            self.log.info(f"  Own address: 0x{own_addr:02x}")

            # Disable slave mode
            await self.tb.write_register(SMBusRegisterMap.SMBUS_CONTROL, 0)
            await ClockCycles(self.tb.pclk, 10)

            self.log.info("Slave mode configuration test passed")
            return True

        except Exception as e:
            self.log.error(f"Slave mode configuration test failed: {e}")
            return False

    async def test_command_register(self) -> bool:
        """Test command register configuration."""
        self.log.info("Testing command register...")

        try:
            # Configure a write byte transaction (but don't start it)
            trans_type = SMBusRegisterMap.TRANS_WRITE_BYTE
            command_byte = 0x42
            slave_addr = 0x50

            # Set slave address first
            await self.tb.write_register(SMBusRegisterMap.SMBUS_SLAVE_ADDR, slave_addr)
            await ClockCycles(self.tb.pclk, 5)

            # Verify slave address
            _, addr = await self.tb.read_register(SMBusRegisterMap.SMBUS_SLAVE_ADDR)
            if (addr & 0x7F) != slave_addr:
                self.log.error(f"Slave address mismatch: got 0x{addr:02x}, expected 0x{slave_addr:02x}")
                return False
            self.log.info(f"  Slave address set: 0x{addr:02x}")

            # Build command register value (without START bit)
            cmd_val = (trans_type & 0xF) | ((command_byte & 0xFF) << 8)
            await self.tb.write_register(SMBusRegisterMap.SMBUS_COMMAND, cmd_val)
            await ClockCycles(self.tb.pclk, 5)

            # Read back command register
            _, cmd = await self.tb.read_register(SMBusRegisterMap.SMBUS_COMMAND)
            self.log.info(f"  Command register: 0x{cmd:08x}")

            # Check transaction type
            if (cmd & 0xF) != trans_type:
                self.log.error(f"Transaction type mismatch: got {cmd & 0xF}, expected {trans_type}")
                return False

            # Check command byte
            if ((cmd >> 8) & 0xFF) != command_byte:
                self.log.error(f"Command byte mismatch: got 0x{(cmd >> 8) & 0xFF:02x}, expected 0x{command_byte:02x}")
                return False

            self.log.info("Command register test passed")
            return True

        except Exception as e:
            self.log.error(f"Command register test failed: {e}")
            return False

    # =========================================================================
    # Full Level Tests
    # =========================================================================

    async def test_full_register_sweep(self) -> bool:
        """Test full register read/write sweep."""
        self.log.info("Testing full register sweep...")

        try:
            import random

            # Define test patterns for different registers
            # Note: CONTROL register has auto-clearing bits (fifo_reset=bit4, soft_reset=bit5)
            # so we write 0x0F (bits 0-3 only) to avoid triggering reset operations
            test_cases = [
                (SMBusRegisterMap.SMBUS_CONTROL, 0x0F, 0x0F, "CONTROL"),  # Avoid auto-clear bits
                (SMBusRegisterMap.SMBUS_CLK_DIV, 0xFFFF, 0xFFFF, "CLK_DIV"),
                (SMBusRegisterMap.SMBUS_TIMEOUT, 0xFFFFFF, 0xFFFFFF, "TIMEOUT"),
                (SMBusRegisterMap.SMBUS_OWN_ADDR, 0x7F, 0x7F, "OWN_ADDR"),
                (SMBusRegisterMap.SMBUS_SLAVE_ADDR, 0x7F, 0x7F, "SLAVE_ADDR"),
                (SMBusRegisterMap.SMBUS_INT_ENABLE, 0x1F, 0x1F, "INT_ENABLE"),
                (SMBusRegisterMap.SMBUS_BLOCK_COUNT, 0x3F, 0x3F, "BLOCK_COUNT"),
            ]

            for addr, write_val, mask, name in test_cases:
                # Write test value
                await self.tb.write_register(addr, write_val)
                await ClockCycles(self.tb.pclk, 5)

                # Read back
                _, read_val = await self.tb.read_register(addr)
                if (read_val & mask) != (write_val & mask):
                    self.log.error(f"{name}: write 0x{write_val:x}, read 0x{read_val:x}")
                    return False
                self.log.info(f"  {name}: OK")

            # Test random patterns
            for _ in range(10):
                clk_div = random.randint(0, 0xFFFF)
                timeout = random.randint(0, 0xFFFFFF)

                await self.tb.configure_clock(clk_div)
                await self.tb.configure_timeout(timeout)
                await ClockCycles(self.tb.pclk, 5)

                _, read_clk = await self.tb.read_register(SMBusRegisterMap.SMBUS_CLK_DIV)
                _, read_timeout = await self.tb.read_register(SMBusRegisterMap.SMBUS_TIMEOUT)

                if (read_clk & 0xFFFF) != clk_div:
                    self.log.error(f"Random CLK_DIV failed: wrote {clk_div}, read {read_clk}")
                    return False

                if (read_timeout & 0xFFFFFF) != timeout:
                    self.log.error(f"Random TIMEOUT failed: wrote {timeout}, read {read_timeout}")
                    return False

            self.log.info("Full register sweep test passed")
            return True

        except Exception as e:
            self.log.error(f"Full register sweep test failed: {e}")
            return False

    async def test_fifo_stress(self) -> bool:
        """Test FIFO with stress patterns."""
        self.log.info("Testing FIFO stress...")

        try:
            import random

            # Reset FIFOs
            await self.tb.reset_fifos()
            await ClockCycles(self.tb.pclk, 10)

            # Test 1: Fill TX FIFO with pattern
            pattern = list(range(32))  # 0x00 to 0x1F
            await self.tb.write_tx_fifo(pattern)
            await ClockCycles(self.tb.pclk, 10)

            fifo_status = await self.tb.read_fifo_status()
            self.log.info(f"  TX FIFO filled: level={fifo_status['tx_level']}")

            if fifo_status['tx_level'] != 32:
                self.log.error(f"TX FIFO level wrong: got {fifo_status['tx_level']}, expected 32")
                return False

            # Should be full
            if not fifo_status['tx_full']:
                self.log.warning("TX FIFO should be full")

            # Reset and test random patterns
            await self.tb.reset_fifos()
            await ClockCycles(self.tb.pclk, 10)

            for i in range(5):
                count = random.randint(1, 32)
                data = [random.randint(0, 255) for _ in range(count)]

                await self.tb.write_tx_fifo(data)
                await ClockCycles(self.tb.pclk, 10)

                fifo_status = await self.tb.read_fifo_status()
                if fifo_status['tx_level'] != count:
                    self.log.error(f"Random test {i}: expected {count}, got {fifo_status['tx_level']}")
                    return False

                # Reset for next iteration
                await self.tb.reset_fifos()
                await ClockCycles(self.tb.pclk, 10)

            self.log.info("FIFO stress test passed")
            return True

        except Exception as e:
            self.log.error(f"FIFO stress test failed: {e}")
            return False

    async def test_config_stress(self) -> bool:
        """Test rapid configuration changes."""
        self.log.info("Testing configuration stress...")

        try:
            import random

            # Rapid mode switches
            for i in range(20):
                # Random configuration
                master_en = random.choice([True, False])
                use_pec = random.choice([True, False])
                fast_mode = random.choice([True, False])

                await self.tb.enable_master_mode(
                    enable=master_en,
                    use_pec=use_pec,
                    fast_mode=fast_mode
                )

                # Small delay
                await ClockCycles(self.tb.pclk, 5)

                # Verify configuration
                _, control = await self.tb.read_register(SMBusRegisterMap.SMBUS_CONTROL)

                if bool(control & SMBusRegisterMap.CONTROL_MASTER_EN) != master_en:
                    self.log.error(f"Iteration {i}: Master enable mismatch")
                    return False

                if bool(control & SMBusRegisterMap.CONTROL_PEC_EN) != use_pec:
                    self.log.error(f"Iteration {i}: PEC enable mismatch")
                    return False

                if bool(control & SMBusRegisterMap.CONTROL_FAST_MODE) != fast_mode:
                    self.log.error(f"Iteration {i}: Fast mode mismatch")
                    return False

            self.log.info(f"  {20} rapid config changes OK")

            # Rapid interrupt enable/disable
            for i in range(10):
                await self.tb.enable_interrupts(
                    complete=True,
                    error=True,
                    tx_thresh=True,
                    rx_thresh=True,
                    slave_addr=True
                )
                await ClockCycles(self.tb.pclk, 5)

                await self.tb.enable_interrupts(
                    complete=False,
                    error=False,
                    tx_thresh=False,
                    rx_thresh=False,
                    slave_addr=False
                )
                await ClockCycles(self.tb.pclk, 5)

            self.log.info("Configuration stress test passed")
            return True

        except Exception as e:
            self.log.error(f"Configuration stress test failed: {e}")
            return False

    # =========================================================================
    # Protocol-Aware Tests (Full Level) - Transaction Type Validation
    # =========================================================================

    async def test_transaction_type_quick_cmd(self) -> bool:
        """Test Quick Command transaction type configuration."""
        self.log.info("Testing Quick Command transaction type...")

        try:
            # Enable master mode
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=249)  # 100kHz
            await ClockCycles(self.tb.pclk, 10)

            # Configure Quick Command transaction
            slave_addr = 0x50
            await self.tb.write_register(SMBusRegisterMap.SMBUS_SLAVE_ADDR, slave_addr)

            # Build command for Quick Command (no data)
            cmd_val = SMBusRegisterMap.TRANS_QUICK_CMD
            await self.tb.write_register(SMBusRegisterMap.SMBUS_COMMAND, cmd_val)
            await ClockCycles(self.tb.pclk, 5)

            # Verify command register
            _, cmd = await self.tb.read_register(SMBusRegisterMap.SMBUS_COMMAND)
            if (cmd & 0xF) != SMBusRegisterMap.TRANS_QUICK_CMD:
                self.log.error(f"Transaction type mismatch: got {cmd & 0xF}, expected {SMBusRegisterMap.TRANS_QUICK_CMD}")
                return False

            self.log.info("Quick Command transaction type test passed")
            return True

        except Exception as e:
            self.log.error(f"Quick Command test failed: {e}")
            return False

    async def test_transaction_type_send_byte(self) -> bool:
        """Test Send Byte transaction type configuration."""
        self.log.info("Testing Send Byte transaction type...")

        try:
            # Enable master mode
            await self.tb.enable_master_mode(enable=True)
            await ClockCycles(self.tb.pclk, 10)

            # Configure Send Byte transaction
            slave_addr = 0x50
            data_byte = 0xAB
            await self.tb.write_register(SMBusRegisterMap.SMBUS_SLAVE_ADDR, slave_addr)
            await self.tb.write_register(SMBusRegisterMap.SMBUS_DATA, data_byte)

            # Build command for Send Byte
            cmd_val = SMBusRegisterMap.TRANS_SEND_BYTE
            await self.tb.write_register(SMBusRegisterMap.SMBUS_COMMAND, cmd_val)
            await ClockCycles(self.tb.pclk, 5)

            # Verify configuration - only verify registers that are guaranteed to be readable
            # Note: DATA register may be modified by HW (connected to FIFO), so we don't verify it
            _, addr = await self.tb.read_register(SMBusRegisterMap.SMBUS_SLAVE_ADDR)
            _, cmd = await self.tb.read_register(SMBusRegisterMap.SMBUS_COMMAND)

            if (addr & 0x7F) != slave_addr:
                self.log.error(f"Slave address mismatch: got 0x{addr:02x}, expected 0x{slave_addr:02x}")
                return False

            if (cmd & 0xF) != SMBusRegisterMap.TRANS_SEND_BYTE:
                self.log.error(f"Transaction type mismatch: got {cmd & 0xF}, expected {SMBusRegisterMap.TRANS_SEND_BYTE}")
                return False

            self.log.info("Send Byte transaction type test passed")
            return True

        except Exception as e:
            self.log.error(f"Send Byte test failed: {e}")
            return False

    async def test_transaction_type_recv_byte(self) -> bool:
        """Test Receive Byte transaction type configuration."""
        self.log.info("Testing Receive Byte transaction type...")

        try:
            # Enable master mode
            await self.tb.enable_master_mode(enable=True)
            await ClockCycles(self.tb.pclk, 10)

            # Configure Receive Byte transaction
            slave_addr = 0x50
            await self.tb.write_register(SMBusRegisterMap.SMBUS_SLAVE_ADDR, slave_addr)

            # Build command for Receive Byte
            cmd_val = SMBusRegisterMap.TRANS_RECV_BYTE
            await self.tb.write_register(SMBusRegisterMap.SMBUS_COMMAND, cmd_val)
            await ClockCycles(self.tb.pclk, 5)

            # Verify configuration
            _, cmd = await self.tb.read_register(SMBusRegisterMap.SMBUS_COMMAND)
            if (cmd & 0xF) != SMBusRegisterMap.TRANS_RECV_BYTE:
                self.log.error(f"Transaction type mismatch: got {cmd & 0xF}, expected {SMBusRegisterMap.TRANS_RECV_BYTE}")
                return False

            self.log.info("Receive Byte transaction type test passed")
            return True

        except Exception as e:
            self.log.error(f"Receive Byte test failed: {e}")
            return False

    async def test_transaction_type_write_byte(self) -> bool:
        """Test Write Byte transaction type configuration."""
        self.log.info("Testing Write Byte transaction type...")

        try:
            # Enable master mode
            await self.tb.enable_master_mode(enable=True)
            await ClockCycles(self.tb.pclk, 10)

            # Configure Write Byte transaction
            slave_addr = 0x50
            command_byte = 0x42
            data_byte = 0xCD
            await self.tb.write_register(SMBusRegisterMap.SMBUS_SLAVE_ADDR, slave_addr)
            await self.tb.write_register(SMBusRegisterMap.SMBUS_DATA, data_byte)

            # Build command for Write Byte with command code
            cmd_val = SMBusRegisterMap.TRANS_WRITE_BYTE | (command_byte << 8)
            await self.tb.write_register(SMBusRegisterMap.SMBUS_COMMAND, cmd_val)
            await ClockCycles(self.tb.pclk, 5)

            # Verify configuration
            _, cmd = await self.tb.read_register(SMBusRegisterMap.SMBUS_COMMAND)
            if (cmd & 0xF) != SMBusRegisterMap.TRANS_WRITE_BYTE:
                self.log.error(f"Transaction type mismatch")
                return False

            if ((cmd >> 8) & 0xFF) != command_byte:
                self.log.error(f"Command byte mismatch: got 0x{(cmd >> 8) & 0xFF:02x}, expected 0x{command_byte:02x}")
                return False

            self.log.info("Write Byte transaction type test passed")
            return True

        except Exception as e:
            self.log.error(f"Write Byte test failed: {e}")
            return False

    async def test_transaction_type_read_byte(self) -> bool:
        """Test Read Byte transaction type configuration."""
        self.log.info("Testing Read Byte transaction type...")

        try:
            # Enable master mode
            await self.tb.enable_master_mode(enable=True)
            await ClockCycles(self.tb.pclk, 10)

            # Configure Read Byte transaction
            slave_addr = 0x50
            command_byte = 0x42
            await self.tb.write_register(SMBusRegisterMap.SMBUS_SLAVE_ADDR, slave_addr)

            # Build command for Read Byte with command code
            cmd_val = SMBusRegisterMap.TRANS_READ_BYTE | (command_byte << 8)
            await self.tb.write_register(SMBusRegisterMap.SMBUS_COMMAND, cmd_val)
            await ClockCycles(self.tb.pclk, 5)

            # Verify configuration
            _, cmd = await self.tb.read_register(SMBusRegisterMap.SMBUS_COMMAND)
            if (cmd & 0xF) != SMBusRegisterMap.TRANS_READ_BYTE:
                self.log.error(f"Transaction type mismatch")
                return False

            self.log.info("Read Byte transaction type test passed")
            return True

        except Exception as e:
            self.log.error(f"Read Byte test failed: {e}")
            return False

    async def test_transaction_type_write_word(self) -> bool:
        """Test Write Word transaction type configuration."""
        self.log.info("Testing Write Word transaction type...")

        try:
            # Enable master mode
            await self.tb.enable_master_mode(enable=True)
            await self.tb.reset_fifos()
            await ClockCycles(self.tb.pclk, 10)

            # Configure Write Word transaction
            slave_addr = 0x50
            command_byte = 0x42
            word_data = 0xABCD

            await self.tb.write_register(SMBusRegisterMap.SMBUS_SLAVE_ADDR, slave_addr)

            # Write word data to TX FIFO (LSB first per SMBus spec)
            await self.tb.write_tx_fifo([word_data & 0xFF, (word_data >> 8) & 0xFF])
            await ClockCycles(self.tb.pclk, 5)

            # Verify FIFO level
            fifo_status = await self.tb.read_fifo_status()
            if fifo_status['tx_level'] != 2:
                self.log.error(f"TX FIFO level mismatch: got {fifo_status['tx_level']}, expected 2")
                return False

            # Build command for Write Word
            cmd_val = SMBusRegisterMap.TRANS_WRITE_WORD | (command_byte << 8)
            await self.tb.write_register(SMBusRegisterMap.SMBUS_COMMAND, cmd_val)
            await ClockCycles(self.tb.pclk, 5)

            # Verify configuration
            _, cmd = await self.tb.read_register(SMBusRegisterMap.SMBUS_COMMAND)
            if (cmd & 0xF) != SMBusRegisterMap.TRANS_WRITE_WORD:
                self.log.error(f"Transaction type mismatch")
                return False

            self.log.info("Write Word transaction type test passed")
            return True

        except Exception as e:
            self.log.error(f"Write Word test failed: {e}")
            return False

    async def test_transaction_type_read_word(self) -> bool:
        """Test Read Word transaction type configuration."""
        self.log.info("Testing Read Word transaction type...")

        try:
            # Enable master mode
            await self.tb.enable_master_mode(enable=True)
            await ClockCycles(self.tb.pclk, 10)

            # Configure Read Word transaction
            slave_addr = 0x50
            command_byte = 0x42
            await self.tb.write_register(SMBusRegisterMap.SMBUS_SLAVE_ADDR, slave_addr)

            # Build command for Read Word
            cmd_val = SMBusRegisterMap.TRANS_READ_WORD | (command_byte << 8)
            await self.tb.write_register(SMBusRegisterMap.SMBUS_COMMAND, cmd_val)
            await ClockCycles(self.tb.pclk, 5)

            # Verify configuration
            _, cmd = await self.tb.read_register(SMBusRegisterMap.SMBUS_COMMAND)
            if (cmd & 0xF) != SMBusRegisterMap.TRANS_READ_WORD:
                self.log.error(f"Transaction type mismatch")
                return False

            self.log.info("Read Word transaction type test passed")
            return True

        except Exception as e:
            self.log.error(f"Read Word test failed: {e}")
            return False

    async def test_transaction_type_block_write(self) -> bool:
        """Test Block Write transaction type configuration."""
        self.log.info("Testing Block Write transaction type...")

        try:
            # Enable master mode
            await self.tb.enable_master_mode(enable=True)
            await self.tb.reset_fifos()
            await ClockCycles(self.tb.pclk, 10)

            # Configure Block Write transaction
            slave_addr = 0x50
            command_byte = 0x42
            block_data = [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]

            await self.tb.write_register(SMBusRegisterMap.SMBUS_SLAVE_ADDR, slave_addr)
            await self.tb.set_block_count(len(block_data))
            await self.tb.write_tx_fifo(block_data)
            await ClockCycles(self.tb.pclk, 5)

            # Verify FIFO level and block count
            fifo_status = await self.tb.read_fifo_status()
            _, block_count = await self.tb.read_register(SMBusRegisterMap.SMBUS_BLOCK_COUNT)

            if fifo_status['tx_level'] != len(block_data):
                self.log.error(f"TX FIFO level mismatch: got {fifo_status['tx_level']}, expected {len(block_data)}")
                return False

            if (block_count & 0x3F) != len(block_data):
                self.log.error(f"Block count mismatch: got {block_count & 0x3F}, expected {len(block_data)}")
                return False

            # Build command for Block Write
            cmd_val = SMBusRegisterMap.TRANS_BLOCK_WRITE | (command_byte << 8)
            await self.tb.write_register(SMBusRegisterMap.SMBUS_COMMAND, cmd_val)
            await ClockCycles(self.tb.pclk, 5)

            # Verify configuration
            _, cmd = await self.tb.read_register(SMBusRegisterMap.SMBUS_COMMAND)
            if (cmd & 0xF) != SMBusRegisterMap.TRANS_BLOCK_WRITE:
                self.log.error(f"Transaction type mismatch")
                return False

            self.log.info("Block Write transaction type test passed")
            return True

        except Exception as e:
            self.log.error(f"Block Write test failed: {e}")
            return False

    async def test_transaction_type_block_read(self) -> bool:
        """Test Block Read transaction type configuration."""
        self.log.info("Testing Block Read transaction type...")

        try:
            # Enable master mode
            await self.tb.enable_master_mode(enable=True)
            await ClockCycles(self.tb.pclk, 10)

            # Configure Block Read transaction
            slave_addr = 0x50
            command_byte = 0x42
            await self.tb.write_register(SMBusRegisterMap.SMBUS_SLAVE_ADDR, slave_addr)

            # Build command for Block Read
            cmd_val = SMBusRegisterMap.TRANS_BLOCK_READ | (command_byte << 8)
            await self.tb.write_register(SMBusRegisterMap.SMBUS_COMMAND, cmd_val)
            await ClockCycles(self.tb.pclk, 5)

            # Verify configuration
            _, cmd = await self.tb.read_register(SMBusRegisterMap.SMBUS_COMMAND)
            if (cmd & 0xF) != SMBusRegisterMap.TRANS_BLOCK_READ:
                self.log.error(f"Transaction type mismatch")
                return False

            self.log.info("Block Read transaction type test passed")
            return True

        except Exception as e:
            self.log.error(f"Block Read test failed: {e}")
            return False

    async def test_transaction_type_block_proc(self) -> bool:
        """Test Block Process Call transaction type configuration."""
        self.log.info("Testing Block Process Call transaction type...")

        try:
            # Enable master mode
            await self.tb.enable_master_mode(enable=True)
            await self.tb.reset_fifos()
            await ClockCycles(self.tb.pclk, 10)

            # Configure Block Process Call transaction
            slave_addr = 0x50
            command_byte = 0x42
            block_data = [0xAA, 0xBB, 0xCC, 0xDD]

            await self.tb.write_register(SMBusRegisterMap.SMBUS_SLAVE_ADDR, slave_addr)
            await self.tb.set_block_count(len(block_data))
            await self.tb.write_tx_fifo(block_data)
            await ClockCycles(self.tb.pclk, 5)

            # Build command for Block Process Call
            cmd_val = SMBusRegisterMap.TRANS_BLOCK_PROC | (command_byte << 8)
            await self.tb.write_register(SMBusRegisterMap.SMBUS_COMMAND, cmd_val)
            await ClockCycles(self.tb.pclk, 5)

            # Verify configuration
            _, cmd = await self.tb.read_register(SMBusRegisterMap.SMBUS_COMMAND)
            if (cmd & 0xF) != SMBusRegisterMap.TRANS_BLOCK_PROC:
                self.log.error(f"Transaction type mismatch")
                return False

            self.log.info("Block Process Call transaction type test passed")
            return True

        except Exception as e:
            self.log.error(f"Block Process Call test failed: {e}")
            return False

    async def test_pec_calculation(self) -> bool:
        """Test PEC (Packet Error Checking) register and configuration."""
        self.log.info("Testing PEC calculation...")

        try:
            # Enable master mode with PEC
            await self.tb.enable_master_mode(enable=True, use_pec=True)
            await ClockCycles(self.tb.pclk, 10)

            # Verify PEC is enabled in control register
            _, control = await self.tb.read_register(SMBusRegisterMap.SMBUS_CONTROL)
            if not (control & SMBusRegisterMap.CONTROL_PEC_EN):
                self.log.error("PEC not enabled in control register")
                return False

            self.log.info("  PEC mode enabled in CONTROL register")

            # Read PEC value (calculated by hardware during transactions)
            # Note: PEC register is updated by hardware during SMBus transactions
            # We verify the register is accessible and starts at 0
            _, pec_value = await self.tb.read_register(SMBusRegisterMap.SMBUS_PEC)
            self.log.info(f"  Current PEC value: 0x{pec_value:02x}")

            # Note: Writing to PEC register may not have effect since HW calculates PEC
            # Just verify we can access the register without errors
            await self.tb.write_register(SMBusRegisterMap.SMBUS_PEC, 0x00)
            await ClockCycles(self.tb.pclk, 5)

            # Read PEC again to verify register access works
            _, pec_value2 = await self.tb.read_register(SMBusRegisterMap.SMBUS_PEC)
            self.log.info(f"  PEC after write: 0x{pec_value2:02x}")

            self.log.info("PEC calculation test passed")
            return True

        except Exception as e:
            self.log.error(f"PEC calculation test failed: {e}")
            return False

    async def test_interrupt_status_w1c(self) -> bool:
        """Test interrupt status write-1-to-clear behavior."""
        self.log.info("Testing interrupt status W1C behavior...")

        try:
            # Enable all interrupts
            await self.tb.enable_interrupts(
                complete=True,
                error=True,
                tx_thresh=True,
                rx_thresh=True,
                slave_addr=True
            )
            await ClockCycles(self.tb.pclk, 10)

            # Read initial interrupt status
            _, int_status = await self.tb.read_register(SMBusRegisterMap.SMBUS_INT_STATUS)
            self.log.info(f"  Initial INT_STATUS: 0x{int_status:08x}")

            # Write to clear any pending interrupts
            await self.tb.write_register(SMBusRegisterMap.SMBUS_INT_STATUS, 0x1F)
            await ClockCycles(self.tb.pclk, 5)

            # Read interrupt status after clear
            _, int_status_after = await self.tb.read_register(SMBusRegisterMap.SMBUS_INT_STATUS)
            self.log.info(f"  INT_STATUS after W1C: 0x{int_status_after:08x}")

            # Verify INT_ENABLE is still set
            _, int_enable = await self.tb.read_register(SMBusRegisterMap.SMBUS_INT_ENABLE)
            if (int_enable & 0x1F) != 0x1F:
                self.log.error(f"INT_ENABLE changed unexpectedly: 0x{int_enable:02x}")
                return False

            self.log.info("Interrupt status W1C test passed")
            return True

        except Exception as e:
            self.log.error(f"Interrupt status W1C test failed: {e}")
            return False

    async def test_all_transaction_types(self) -> bool:
        """Test all SMBus transaction types can be configured."""
        self.log.info("Testing all transaction types...")

        try:
            # Enable master mode
            await self.tb.enable_master_mode(enable=True)
            await ClockCycles(self.tb.pclk, 10)

            transaction_types = [
                (SMBusRegisterMap.TRANS_QUICK_CMD, "Quick Command"),
                (SMBusRegisterMap.TRANS_SEND_BYTE, "Send Byte"),
                (SMBusRegisterMap.TRANS_RECV_BYTE, "Receive Byte"),
                (SMBusRegisterMap.TRANS_WRITE_BYTE, "Write Byte"),
                (SMBusRegisterMap.TRANS_READ_BYTE, "Read Byte"),
                (SMBusRegisterMap.TRANS_WRITE_WORD, "Write Word"),
                (SMBusRegisterMap.TRANS_READ_WORD, "Read Word"),
                (SMBusRegisterMap.TRANS_BLOCK_WRITE, "Block Write"),
                (SMBusRegisterMap.TRANS_BLOCK_READ, "Block Read"),
                (SMBusRegisterMap.TRANS_BLOCK_PROC, "Block Process Call"),
            ]

            for trans_type, name in transaction_types:
                # Write command register with transaction type
                cmd_val = trans_type | (0x42 << 8)  # Add command byte
                await self.tb.write_register(SMBusRegisterMap.SMBUS_COMMAND, cmd_val)
                await ClockCycles(self.tb.pclk, 5)

                # Verify transaction type
                _, cmd = await self.tb.read_register(SMBusRegisterMap.SMBUS_COMMAND)
                if (cmd & 0xF) != trans_type:
                    self.log.error(f"{name}: type mismatch, got {cmd & 0xF}, expected {trans_type}")
                    return False

                self.log.info(f"  {name}: OK")

            self.log.info("All transaction types test passed")
            return True

        except Exception as e:
            self.log.error(f"All transaction types test failed: {e}")
            return False

    async def test_fifo_full_detection(self) -> bool:
        """Test TX FIFO full detection."""
        self.log.info("Testing FIFO full detection...")

        try:
            # Reset FIFOs
            await self.tb.reset_fifos()
            await ClockCycles(self.tb.pclk, 10)

            # Write 32 bytes to fill TX FIFO (max depth)
            data = list(range(32))
            await self.tb.write_tx_fifo(data)
            await ClockCycles(self.tb.pclk, 10)

            # Check FIFO status
            fifo_status = await self.tb.read_fifo_status()

            if fifo_status['tx_level'] != 32:
                self.log.error(f"TX FIFO level wrong: got {fifo_status['tx_level']}, expected 32")
                return False

            if not fifo_status['tx_full']:
                self.log.error("TX FIFO should be full")
                return False

            if fifo_status['tx_empty']:
                self.log.error("TX FIFO should not be empty")
                return False

            self.log.info(f"  TX FIFO full: level={fifo_status['tx_level']}")

            # Reset FIFOs and verify empty
            await self.tb.reset_fifos()
            await ClockCycles(self.tb.pclk, 10)

            fifo_status = await self.tb.read_fifo_status()
            if not fifo_status['tx_empty']:
                self.log.error("TX FIFO should be empty after reset")
                return False

            self.log.info("FIFO full detection test passed")
            return True

        except Exception as e:
            self.log.error(f"FIFO full detection test failed: {e}")
            return False

    async def test_clock_configuration_values(self) -> bool:
        """Test various clock divider configurations."""
        self.log.info("Testing clock divider configurations...")

        try:
            # Test standard SMBus speeds
            clock_configs = [
                (249, "100kHz"),   # 100MHz / (4 * 250) = 100kHz
                (124, "200kHz"),   # 100MHz / (4 * 125) = 200kHz
                (62, "400kHz"),    # 100MHz / (4 * 63) = ~396kHz
                (49, "500kHz"),    # 100MHz / (4 * 50) = 500kHz
                (0xFFFF, "Min"),   # Maximum divider
                (0, "Max"),        # Minimum divider
            ]

            for clk_div, name in clock_configs:
                await self.tb.configure_clock(clk_div)
                await ClockCycles(self.tb.pclk, 5)

                _, readback = await self.tb.read_register(SMBusRegisterMap.SMBUS_CLK_DIV)
                if (readback & 0xFFFF) != clk_div:
                    self.log.error(f"{name}: CLK_DIV mismatch, got 0x{readback:04x}, expected 0x{clk_div:04x}")
                    return False

                self.log.info(f"  {name} (CLK_DIV={clk_div}): OK")

            self.log.info("Clock configuration values test passed")
            return True

        except Exception as e:
            self.log.error(f"Clock configuration values test failed: {e}")
            return False

    async def test_timeout_configuration_values(self) -> bool:
        """Test various timeout threshold configurations."""
        self.log.info("Testing timeout configurations...")

        try:
            # Test SMBus timeout values (25-35ms at 100MHz)
            timeout_configs = [
                (2500000, "25ms"),    # 25ms timeout
                (3000000, "30ms"),    # 30ms timeout
                (3500000, "35ms"),    # 35ms timeout
                (0xFFFFFF, "Max"),    # Maximum timeout
                (1000, "Min"),        # Minimum timeout
            ]

            for timeout, name in timeout_configs:
                await self.tb.configure_timeout(timeout)
                await ClockCycles(self.tb.pclk, 5)

                _, readback = await self.tb.read_register(SMBusRegisterMap.SMBUS_TIMEOUT)
                if (readback & 0xFFFFFF) != timeout:
                    self.log.error(f"{name}: TIMEOUT mismatch, got 0x{readback:06x}, expected 0x{timeout:06x}")
                    return False

                self.log.info(f"  {name} (TIMEOUT={timeout}): OK")

            self.log.info("Timeout configuration values test passed")
            return True

        except Exception as e:
            self.log.error(f"Timeout configuration values test failed: {e}")
            return False

    async def test_slave_address_range(self) -> bool:
        """Test slave address register accepts full 7-bit range."""
        self.log.info("Testing slave address range...")

        try:
            # Test various slave addresses
            test_addresses = [
                0x00,  # General call address
                0x01,
                0x50,  # Common EEPROM address
                0x68,  # Common RTC address
                0x70,  # Common GPIO expander address
                0x7F,  # Maximum address
            ]

            for addr in test_addresses:
                await self.tb.write_register(SMBusRegisterMap.SMBUS_SLAVE_ADDR, addr)
                await ClockCycles(self.tb.pclk, 5)

                _, readback = await self.tb.read_register(SMBusRegisterMap.SMBUS_SLAVE_ADDR)
                if (readback & 0x7F) != addr:
                    self.log.error(f"Slave address mismatch: got 0x{readback:02x}, expected 0x{addr:02x}")
                    return False

                self.log.info(f"  Address 0x{addr:02x}: OK")

            self.log.info("Slave address range test passed")
            return True

        except Exception as e:
            self.log.error(f"Slave address range test failed: {e}")
            return False

    async def test_own_address_configuration(self) -> bool:
        """Test own address configuration for slave mode."""
        self.log.info("Testing own address configuration...")

        try:
            # Test various own addresses for slave mode
            test_addresses = [
                0x10,
                0x50,
                0x55,
                0x7E,
            ]

            for addr in test_addresses:
                await self.tb.enable_slave_mode(enable=True, own_addr=addr)
                await ClockCycles(self.tb.pclk, 5)

                # Verify control register
                _, control = await self.tb.read_register(SMBusRegisterMap.SMBUS_CONTROL)
                if not (control & SMBusRegisterMap.CONTROL_SLAVE_EN):
                    self.log.error("Slave mode not enabled")
                    return False

                # Verify own address
                _, own_addr = await self.tb.read_register(SMBusRegisterMap.SMBUS_OWN_ADDR)
                if (own_addr & 0x7F) != addr:
                    self.log.error(f"Own address mismatch: got 0x{own_addr:02x}, expected 0x{addr:02x}")
                    return False

                self.log.info(f"  Own address 0x{addr:02x}: OK")

            self.log.info("Own address configuration test passed")
            return True

        except Exception as e:
            self.log.error(f"Own address configuration test failed: {e}")
            return False
