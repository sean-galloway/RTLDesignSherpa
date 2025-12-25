# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXIS5MasterTB
# Purpose: AXIS5 Master Testbench with AMBA5 extensions
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-21

"""
AXIS5 Master Testbench

Testbench for testing axis5_master.sv module using the CocoTB framework's
AXIS5 components. The axis5_master is a skid buffer that converts FUB-side
signals to standard AXIS5 master interface with TWAKEUP and TPARITY support.

Architecture:
    fub_axis5_* (input) -> [axis5_master] -> m_axis5_* (output)
                               |
                             busy (status)

Based on AXIS4 testbench patterns with AXIS5 extension testing.
"""
import os
import random

import cocotb
from cocotb.triggers import RisingEdge

# Framework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

# AXIS5 specific imports
from CocoTBFramework.components.axis5.axis5_factories import (
    create_axis5_master,
    create_axis5_slave,
    create_axis5_monitor
)
from CocoTBFramework.components.axis5.axis5_packet import AXIS5Packet
from CocoTBFramework.components.axis5.axis5_field_configs import AXIS5FieldConfigs


class AXIS5MasterTB(TBBase):
    """
    AXIS5 Master testbench for testing axis5_master.sv RTL module.

    Tests the skid buffer functionality that converts FUB-side AXIS5
    signals to standard AXIS5 master interface with TWAKEUP and TPARITY.
    """

    def __init__(self, dut, aclk=None, aresetn=None):
        super().__init__(dut)

        # Get test parameters from environment
        self.TEST_SKID_DEPTH = self.convert_to_int(os.environ.get('TEST_SKID_DEPTH', '4'))
        self.TEST_DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.TEST_ID_WIDTH = self.convert_to_int(os.environ.get('TEST_ID_WIDTH', '8'))
        self.TEST_DEST_WIDTH = self.convert_to_int(os.environ.get('TEST_DEST_WIDTH', '4'))
        self.TEST_USER_WIDTH = self.convert_to_int(os.environ.get('TEST_USER_WIDTH', '1'))
        self.TEST_CLK_PERIOD = self.convert_to_int(os.environ.get('TEST_CLK_PERIOD', '10'))
        self.ENABLE_WAKEUP = self.convert_to_int(os.environ.get('TEST_ENABLE_WAKEUP', '1')) == 1
        self.ENABLE_PARITY = self.convert_to_int(os.environ.get('TEST_ENABLE_PARITY', '0')) == 1
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TIMEOUT_CYCLES = self.convert_to_int(os.environ.get('TIMEOUT_CYCLES', '1000'))

        # Initialize random generator
        random.seed(self.SEED)

        # Setup clock and reset signals
        self.aclk = aclk
        self.aclk_name = aclk._name if aclk else 'aclk'
        self.aresetn = aresetn

        # Calculate derived parameters
        self.STRB_WIDTH = self.TEST_DATA_WIDTH // 8

        # Log configuration
        msg = '\n'
        msg += '='*80 + "\n"
        msg += ' AXIS5 Master Test Configuration:\n'
        msg += '-'*80 + "\n"
        msg += f' SKID Depth:    {self.TEST_SKID_DEPTH}\n'
        msg += f' Data Width:    {self.TEST_DATA_WIDTH}\n'
        msg += f' ID Width:      {self.TEST_ID_WIDTH}\n'
        msg += f' DEST Width:    {self.TEST_DEST_WIDTH}\n'
        msg += f' USER Width:    {self.TEST_USER_WIDTH}\n'
        msg += f' STRB Width:    {self.STRB_WIDTH}\n'
        msg += f' Enable Wakeup: {self.ENABLE_WAKEUP}\n'
        msg += f' Enable Parity: {self.ENABLE_PARITY}\n'
        msg += f' Clock Period:  {self.TEST_CLK_PERIOD} ns\n'
        msg += f' Seed:          {self.SEED}\n'
        msg += '='*80 + "\n"
        self.log.info(msg)

        # Create memory model for data verification
        bytes_per_line = max(4, (self.TEST_DATA_WIDTH + 7) // 8)
        self.memory_model = MemoryModel(
            num_lines=1024,
            bytes_per_line=bytes_per_line,
            log=self.log
        )

        # Create randomizer for traffic patterns
        self.randomizer = FlexRandomizer(
            constraints={
                'packet_delay': ([(1, 10)], [1]),
                'frame_delay': ([(5, 20)], [1]),
                'wakeup_trigger': ([(0, 0), (1, 1)], [9, 1]),  # 10% wakeup probability
            }
        )

        # Statistics
        self.packets_sent_fub = 0
        self.packets_received_master = 0
        self.frames_sent = 0
        self.frames_received = 0
        self.wakeup_events = 0
        self.parity_errors = 0
        self.busy_cycles = 0

        # Test components will be created in setup_components()
        self.fub_master = None
        self.axis_slave = None
        self.axis_monitor = None

    def setup_components(self):
        """Setup AXIS5 components for testing."""

        # Create FUB-side master (feeds input to axis5_master RTL)
        self.fub_master_components = create_axis5_master(
            dut=self.dut,
            clock=self.aclk,
            prefix="fub_axis5_",
            data_width=self.TEST_DATA_WIDTH,
            id_width=self.TEST_ID_WIDTH,
            dest_width=self.TEST_DEST_WIDTH,
            user_width=self.TEST_USER_WIDTH,
            enable_wakeup=self.ENABLE_WAKEUP,
            enable_parity=self.ENABLE_PARITY,
            log=self.log,
            super_debug=True
        )
        self.fub_master = self.fub_master_components['interface']

        # Create AXIS5 slave (receives output from axis5_master RTL)
        self.axis_slave_components = create_axis5_slave(
            dut=self.dut,
            clock=self.aclk,
            prefix="m_axis5_",
            data_width=self.TEST_DATA_WIDTH,
            id_width=self.TEST_ID_WIDTH,
            dest_width=self.TEST_DEST_WIDTH,
            user_width=self.TEST_USER_WIDTH,
            enable_wakeup=self.ENABLE_WAKEUP,
            enable_parity=self.ENABLE_PARITY,
            log=self.log,
            randomizer=self.randomizer,
            super_debug=True
        )
        self.axis_slave = self.axis_slave_components['interface']

        # Create monitor to observe master output
        self.axis_monitor_components = create_axis5_monitor(
            dut=self.dut,
            clock=self.aclk,
            prefix="m_axis5_",
            data_width=self.TEST_DATA_WIDTH,
            id_width=self.TEST_ID_WIDTH,
            dest_width=self.TEST_DEST_WIDTH,
            user_width=self.TEST_USER_WIDTH,
            is_slave=False,
            enable_wakeup=self.ENABLE_WAKEUP,
            enable_parity=self.ENABLE_PARITY,
            log=self.log,
            super_debug=True
        )
        self.axis_monitor = self.axis_monitor_components['interface']

        # Initialize reset_occurring attribute
        if not hasattr(self.fub_master, 'reset_occurring'):
            self.fub_master.reset_occurring = False
        if not hasattr(self.axis_slave, 'reset_occurring'):
            self.axis_slave.reset_occurring = False

        # Start monitoring tasks
        cocotb.start_soon(self.axis_slave._monitor_recv())
        cocotb.start_soon(self.axis_monitor._monitor_recv())

        self.log.info("AXIS5 Master testbench components created successfully")

    async def assert_reset(self):
        """Assert reset and initialize components."""
        self.aresetn.value = 0
        await self.wait_clocks(self.aclk_name, 5)
        self.log.info("Reset asserted")

    async def deassert_reset(self):
        """Deassert reset."""
        self.aresetn.value = 1
        await self.wait_clocks(self.aclk_name, 5)

        if hasattr(self.fub_master, 'reset_bus'):
            await self.fub_master.reset_bus()
        if hasattr(self.axis_slave, 'reset_bus'):
            await self.axis_slave.reset_bus()

        self.log.info("Reset deasserted and bus interfaces reset")

    async def setup_clocks_and_reset(self):
        """Setup clocks and perform reset sequence."""
        await self.start_clock(self.aclk_name, self.TEST_CLK_PERIOD, 'ns')
        await self.assert_reset()
        await self.deassert_reset()

    async def run_basic_transfer_test(self, num_packets=10):
        """Test basic packet transfer through the axis5_master."""
        self.log.info(f"Starting basic transfer test with {num_packets} packets")

        self.axis_slave._set_ready(1)

        for i in range(num_packets):
            data = 0x10000000 + i

            packet = AXIS5Packet(
                enable_wakeup=self.ENABLE_WAKEUP,
                enable_parity=self.ENABLE_PARITY
            )
            packet.data = data
            packet.last = 1
            packet.id = i % (2**self.TEST_ID_WIDTH) if self.TEST_ID_WIDTH > 0 else 0
            packet.dest = i % (2**self.TEST_DEST_WIDTH) if self.TEST_DEST_WIDTH > 0 else 0
            packet.user = i % (2**self.TEST_USER_WIDTH) if self.TEST_USER_WIDTH > 0 else 0

            success = await self.fub_master.send_packet(packet)
            assert success, f"Failed to send packet {i}"
            self.packets_sent_fub += 1

        await self.wait_clocks(self.aclk_name, 50)

        slave_stats = self.axis_slave.get_stats()
        packets_received = slave_stats.get('packets_received', 0)
        self.log.info(f"Slave received {packets_received} packets")

        assert packets_received >= num_packets, "Not all packets received by slave"
        self.log.info("Basic transfer test completed successfully")

    async def run_wakeup_test(self, num_wakeups=5):
        """Test TWAKEUP signal behavior."""
        if not self.ENABLE_WAKEUP:
            self.log.info("Wakeup not enabled, skipping wakeup test")
            return

        self.log.info(f"Starting wakeup test with {num_wakeups} wakeup events")

        self.axis_slave._set_ready(1)

        for i in range(num_wakeups):
            # Request wakeup before sending
            self.fub_master.request_wakeup()

            # Send a packet
            packet = AXIS5Packet(
                enable_wakeup=self.ENABLE_WAKEUP,
                enable_parity=self.ENABLE_PARITY
            )
            packet.data = 0x50000000 + i
            packet.last = 1
            packet.wakeup = 1

            success = await self.fub_master.send_packet(packet)
            assert success, f"Failed to send packet {i} with wakeup"

            # Wait for wakeup to complete
            await self.wait_clocks(self.aclk_name, 10)

        # Verify wakeup events
        slave_stats = self.axis_slave.get_stats()
        wakeup_events = slave_stats.get('wakeup_events', 0)
        self.log.info(f"Slave detected {wakeup_events} wakeup events")

        self.log.info("Wakeup test completed successfully")

    async def run_parity_test(self, num_packets=10):
        """Test TPARITY signal behavior."""
        if not self.ENABLE_PARITY:
            self.log.info("Parity not enabled, skipping parity test")
            return

        self.log.info(f"Starting parity test with {num_packets} packets")

        self.axis_slave._set_ready(1)

        # Test correct parity
        for i in range(num_packets):
            packet = AXIS5Packet(
                enable_wakeup=self.ENABLE_WAKEUP,
                enable_parity=self.ENABLE_PARITY
            )
            packet.data = 0x60000000 + i
            packet.last = 1
            packet.parity = packet.calculate_parity()

            success = await self.fub_master.send_packet(packet)
            assert success, f"Failed to send packet {i} with parity"

        await self.wait_clocks(self.aclk_name, 50)

        # Verify parity checks
        slave_stats = self.axis_slave.get_stats()
        parity_passed = slave_stats.get('parity_checks_passed', 0)
        parity_errors = slave_stats.get('parity_errors_detected', 0)

        self.log.info(f"Parity checks passed: {parity_passed}, errors: {parity_errors}")
        assert parity_errors == 0, "Unexpected parity errors detected"

        self.log.info("Parity test completed successfully")

    async def run_parity_error_injection_test(self, num_errors=3):
        """Test parity error detection."""
        if not self.ENABLE_PARITY:
            self.log.info("Parity not enabled, skipping error injection test")
            return

        self.log.info(f"Starting parity error injection test with {num_errors} errors")

        self.axis_slave._set_ready(1)

        for i in range(num_errors):
            packet = AXIS5Packet(
                enable_wakeup=self.ENABLE_WAKEUP,
                enable_parity=self.ENABLE_PARITY
            )
            packet.data = 0x70000000 + i
            packet.last = 1
            # Inject bad parity (invert correct parity)
            correct_parity = packet.calculate_parity()
            packet.parity = ~correct_parity & ((1 << self.STRB_WIDTH) - 1)

            success = await self.fub_master.send_packet(packet)
            assert success, f"Failed to send packet {i} with bad parity"

        await self.wait_clocks(self.aclk_name, 50)

        # Verify parity errors were detected
        slave_stats = self.axis_slave.get_stats()
        parity_errors = slave_stats.get('parity_errors_detected', 0)

        self.log.info(f"Parity errors detected: {parity_errors}")
        assert parity_errors >= num_errors, f"Expected {num_errors} parity errors, got {parity_errors}"

        self.log.info("Parity error injection test completed successfully")

    async def run_frame_transfer_test(self, num_frames=5, frame_size=4):
        """Test frame transfer with TLAST boundaries."""
        self.log.info(f"Starting frame transfer test: {num_frames} frames, {frame_size} beats each")

        self.axis_slave.apply_backpressure(probability=0.2, min_cycles=1, max_cycles=3)

        for frame_id in range(num_frames):
            for beat in range(frame_size):
                data = (frame_id << 16) | beat

                packet = AXIS5Packet(
                    enable_wakeup=self.ENABLE_WAKEUP,
                    enable_parity=self.ENABLE_PARITY
                )
                packet.data = data
                packet.last = 1 if beat == frame_size - 1 else 0
                packet.id = frame_id

                if self.ENABLE_PARITY:
                    packet.parity = packet.calculate_parity()

                success = await self.fub_master.send_packet(packet)
                assert success, f"Failed to send beat {beat} of frame {frame_id}"

            self.frames_sent += 1
            await self.wait_clocks(self.aclk_name, 10)

        await self.wait_clocks(self.aclk_name, 100)

        slave_stats = self.axis_slave.get_stats()
        frames_received = slave_stats.get('frames_received', 0)
        self.log.info(f"Slave received {frames_received} frames")

        assert frames_received >= num_frames, "Not all frames received"
        self.log.info("Frame transfer test completed successfully")

    async def run_backpressure_test(self, num_packets=20):
        """Test operation under various backpressure conditions."""
        self.log.info(f"Starting backpressure test with {num_packets} packets")

        self.axis_slave.apply_backpressure(probability=0.7, min_cycles=1, max_cycles=5)

        for i in range(num_packets):
            packet = AXIS5Packet(
                enable_wakeup=self.ENABLE_WAKEUP,
                enable_parity=self.ENABLE_PARITY
            )
            packet.data = 0x20000000 + i
            packet.last = 1

            if self.ENABLE_PARITY:
                packet.parity = packet.calculate_parity()

            success = await self.fub_master.send_packet(packet)
            assert success, f"Failed to send packet {i} under backpressure"

            delay = random.randint(1, 5)
            await self.wait_clocks(self.aclk_name, delay)

        await self.wait_clocks(self.aclk_name, 200)

        slave_stats = self.axis_slave.get_stats()
        packets_received = slave_stats.get('packets_received', 0)
        assert packets_received >= num_packets, f"Packets lost: {packets_received}/{num_packets}"

        self.log.info("Backpressure test completed successfully")

    def generate_final_report(self):
        """Generate final test report."""
        try:
            fub_stats = self.fub_master.get_stats() if self.fub_master else {}
            slave_stats = self.axis_slave.get_stats() if self.axis_slave else {}
            monitor_stats = self.axis_monitor.get_stats() if self.axis_monitor else {}

            self.log.info("=== FINAL AXIS5 MASTER TEST REPORT ===")
            self.log.info(f"FUB Master Stats: {fub_stats}")
            self.log.info(f"AXIS5 Slave Stats: {slave_stats}")
            self.log.info(f"AXIS5 Monitor Stats: {monitor_stats}")
            self.log.info(f"Packets sent (FUB): {self.packets_sent_fub}")
            self.log.info(f"Frames sent: {self.frames_sent}")
            self.log.info(f"Wakeup events: {self.wakeup_events}")
            self.log.info(f"Parity errors: {self.parity_errors}")

            # AXIS5-specific validation
            wakeup_events = slave_stats.get('wakeup_events', 0)
            parity_errors = slave_stats.get('parity_errors_detected', 0)
            parity_passed = slave_stats.get('parity_checks_passed', 0)

            self.log.info(f"AXIS5 Validation: wakeup_events={wakeup_events}, "
                         f"parity_passed={parity_passed}, parity_errors={parity_errors}")

            return True

        except Exception as e:
            self.log.error(f"Error generating final report: {e}")
            return False
