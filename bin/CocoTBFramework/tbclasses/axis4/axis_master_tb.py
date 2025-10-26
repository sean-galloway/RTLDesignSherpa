# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXISMasterTB
# Purpose: AXIS Master Testbench
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXIS Master Testbench

Testbench for testing axis_master.sv module using the CocoTB framework's
AXIS components. The axis_master is a skid buffer that converts FUB-side
signals to standard AXIS master interface.

Architecture:
    fub_axis_* (input) -> [axis_master] -> m_axis_* (output)
                              |
                            busy (status)

Based on AXI4 testbench patterns but simplified for AXIS stream testing.
"""
import os
import random

# Framework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

# AXIS specific imports
from CocoTBFramework.components.axis4.axis_factories import create_axis_master, create_axis_slave, create_axis_monitor
from CocoTBFramework.components.axis4.axis_packet import AXISPacket, create_axis_packet
from CocoTBFramework.components.axis4.axis_field_configs import AXISFieldConfigs


class AXISMasterTB(TBBase):
    """
    AXIS Master testbench for testing axis_master.sv RTL module.

    Tests the skid buffer functionality that converts FUB-side AXIS
    signals to standard AXIS master interface.
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
        msg += ' AXIS Master Test Configuration:\n'
        msg += '-'*80 + "\n"
        msg += f' SKID Depth:   {self.TEST_SKID_DEPTH}\n'
        msg += f' Data Width:   {self.TEST_DATA_WIDTH}\n'
        msg += f' ID Width:     {self.TEST_ID_WIDTH}\n'
        msg += f' DEST Width:   {self.TEST_DEST_WIDTH}\n'
        msg += f' USER Width:   {self.TEST_USER_WIDTH}\n'
        msg += f' STRB Width:   {self.STRB_WIDTH}\n'
        msg += f' Clock Period: {self.TEST_CLK_PERIOD} ns\n'
        msg += f' Seed:         {self.SEED}\n'
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
                'packet_delay': ([(1, 10)], [1]),  # 1-10 cycles delay between packets
                'frame_delay': ([(5, 20)], [1]),   # 5-20 cycles delay between frames
            }
        )

        # Statistics
        self.packets_sent_fub = 0
        self.packets_received_master = 0
        self.frames_sent = 0
        self.frames_received = 0
        self.busy_cycles = 0

        # Test components will be created in setup_components()
        self.fub_master = None
        self.axis_slave = None
        self.axis_monitor = None

    def setup_components(self):
        """Setup AXIS components for testing."""

        # Create FUB-side master (feeds input to axis_master RTL)
        self.fub_master_components = create_axis_master(
            dut=self.dut,
            clock=self.aclk,
            prefix="fub_axis_",
            data_width=self.TEST_DATA_WIDTH,
            id_width=self.TEST_ID_WIDTH,
            dest_width=self.TEST_DEST_WIDTH,
            user_width=self.TEST_USER_WIDTH,
            log=self.log,
            super_debug=True
        )
        self.fub_master = self.fub_master_components['interface']

        # Create AXIS slave (receives output from axis_master RTL)
        self.axis_slave_components = create_axis_slave(
            dut=self.dut,
            clock=self.aclk,
            prefix="m_axis_",
            data_width=self.TEST_DATA_WIDTH,
            id_width=self.TEST_ID_WIDTH,
            dest_width=self.TEST_DEST_WIDTH,
            user_width=self.TEST_USER_WIDTH,
            log=self.log,
            randomizer=self.randomizer,
            super_debug=True
        )
        self.axis_slave = self.axis_slave_components['interface']

        # Create monitor to observe master output
        self.axis_monitor_components = create_axis_monitor(
            dut=self.dut,
            clock=self.aclk,
            prefix="m_axis_",
            data_width=self.TEST_DATA_WIDTH,
            id_width=self.TEST_ID_WIDTH,
            dest_width=self.TEST_DEST_WIDTH,
            user_width=self.TEST_USER_WIDTH,
            is_slave=False,  # Monitor master side
            log=self.log,
            randomizer=self.randomizer,
            super_debug=True
        )
        self.axis_monitor = self.axis_monitor_components['interface']

        # Initialize reset_occurring attribute if missing (workaround for GAXI compatibility)
        if not hasattr(self.fub_master, 'reset_occurring'):
            self.fub_master.reset_occurring = False
        if not hasattr(self.axis_slave, 'reset_occurring'):
            self.axis_slave.reset_occurring = False

        # Start monitoring tasks for slave and monitor components
        import cocotb
        cocotb.start_soon(self.axis_slave._monitor_recv())
        cocotb.start_soon(self.axis_monitor._monitor_recv())

        self.log.info("AXIS Master testbench components created successfully and monitoring started")

    async def assert_reset(self):
        """Assert reset and initialize components"""
        self.aresetn.value = 0
        await self.wait_clocks(self.aclk_name, 5)
        self.log.info("Reset asserted")

    async def deassert_reset(self):
        """Deassert reset"""
        self.aresetn.value = 1
        await self.wait_clocks(self.aclk_name, 5)

        # Reset the bus interfaces after hardware reset is deasserted
        if hasattr(self.fub_master, 'reset_bus'):
            await self.fub_master.reset_bus()
        if hasattr(self.axis_slave, 'reset_bus'):
            await self.axis_slave.reset_bus()

        self.log.info("Reset deasserted and bus interfaces reset")

    async def run_basic_transfer_test(self, num_packets=10):
        """Test basic packet transfer through the axis_master."""
        self.log.info(f"Starting basic transfer test with {num_packets} packets")

        # Configure slave to be always ready (using GAXISlave method)
        self.axis_slave._set_ready(1)

        # Debug: Check initial signal values
        await self.wait_clocks(self.aclk_name, 1)
        try:
            fub_tready = int(self.dut.fub_axis_tready.value)
            m_tvalid = int(self.dut.m_axis_tvalid.value)
            m_tready = int(self.dut.m_axis_tready.value)
            self.log.info(f"Initial signals: fub_tready={fub_tready}, m_tvalid={m_tvalid}, m_tready={m_tready}")
        except Exception as e:
            self.log.warning(f"Could not read initial signals: {e}")

        # Send packets through FUB side
        for i in range(num_packets):
            data = 0x10000000 + i
            # Create packet using GAXIMaster API
            packet = self.fub_master.create_packet(
                data=data,
                last=1,
                id=i % (2**self.TEST_ID_WIDTH if self.TEST_ID_WIDTH > 0 else 1),
                dest=i % (2**self.TEST_DEST_WIDTH if self.TEST_DEST_WIDTH > 0 else 1),
                user=i % (2**self.TEST_USER_WIDTH if self.TEST_USER_WIDTH > 0 else 1)
            )
            success = await self.fub_master.send(packet)
            assert success, f"Failed to send packet {i}"
            self.packets_sent_fub += 1

            # Debug: Check signals after packet transmission
            await self.wait_clocks(self.aclk_name, 2)
            try:
                fub_tvalid = int(self.dut.fub_axis_tvalid.value)
                fub_tready = int(self.dut.fub_axis_tready.value)
                m_tvalid = int(self.dut.m_axis_tvalid.value)
                m_tready = int(self.dut.m_axis_tready.value)
                if i < 3:  # Only log first 3 packets to avoid spam
                    self.log.info(f"After packet {i}: fub_tvalid={fub_tvalid}, fub_tready={fub_tready}, m_tvalid={m_tvalid}, m_tready={m_tready}")
            except Exception as e:
                self.log.warning(f"Could not read signals after packet {i}: {e}")

        # Wait for all transfers to complete
        await self.wait_clocks(self.aclk_name, 50)

        # Verify packets were received
        slave_stats = self.axis_slave.get_stats()
        monitor_stats = self.axis_monitor.get_stats()

        self.log.info(f"Slave stats keys: {list(slave_stats.keys())}")
        self.log.info(f"Monitor stats keys: {list(monitor_stats.keys())}")

        # Debug: Check observed_packets field
        slave_observed = slave_stats.get('observed_packets', 0)
        monitor_observed = monitor_stats.get('observed_packets', 0)

        self.log.info(f"Slave observed_packets: {slave_observed}")
        self.log.info(f"Monitor observed_packets: {monitor_observed}")

        # Use appropriate keys based on what's actually available
        packets_received = slave_stats.get('packets_received', slave_stats.get('packet_count', slave_observed))
        packets_observed = monitor_stats.get('packets_observed', monitor_stats.get('packet_count', monitor_observed))

        self.log.info(f"Slave received {packets_received} packets")
        self.log.info(f"Monitor observed {packets_observed} packets")

        assert packets_received >= num_packets, "Not all packets received by slave"
        assert packets_observed >= num_packets, "Not all packets observed by monitor"

        self.log.info("Basic transfer test completed successfully")

    async def run_frame_transfer_test(self, num_frames=5, frame_size=4):
        """Test frame transfer with TLAST boundaries."""
        self.log.info(f"Starting frame transfer test: {num_frames} frames, {frame_size} beats each")

        # Configure slave with some backpressure
        self.axis_slave.apply_backpressure(probability=0.2, min_cycles=1, max_cycles=3)

        for frame_id in range(num_frames):
            frame_data = []
            for beat in range(frame_size):
                data = (frame_id << 16) | beat
                frame_data.append(data)

            # Send frame as individual packets using GAXIMaster API
            success = True
            for beat_idx, data in enumerate(frame_data):
                packet = self.fub_master.create_packet(
                    data=data,
                    last=1 if beat_idx == len(frame_data) - 1 else 0,
                    id=frame_id,
                    dest=frame_id % (2**self.TEST_DEST_WIDTH if self.TEST_DEST_WIDTH > 0 else 1),
                    user=0x1
                )
                packet_success = await self.fub_master.send(packet)
                if not packet_success:
                    success = False
                    break
            assert success, f"Failed to send frame {frame_id}"
            self.frames_sent += 1

            # Wait between frames
            await self.wait_clocks(self.aclk_name, 10)

        # Wait for all frames to complete
        await self.wait_clocks(self.aclk_name, 100)

        # Verify frame reception
        slave_stats = self.axis_slave.get_stats()
        self.log.info(f"Slave received {slave_stats['frames_received']} frames")

        assert slave_stats['frames_received'] >= num_frames, "Not all frames received"

        self.log.info("Frame transfer test completed successfully")

    async def run_backpressure_test(self, num_packets=20):
        """Test operation under various backpressure conditions."""
        self.log.info(f"Starting backpressure test with {num_packets} packets")

        # Apply aggressive backpressure
        self.axis_slave.apply_backpressure(probability=0.7, min_cycles=1, max_cycles=5)

        # Send packets with random spacing
        for i in range(num_packets):
            data = 0x20000000 + i
            # Create packet using GAXIMaster API
            packet = self.fub_master.create_packet(
                data=data,
                last=1,
                id=i % (2**self.TEST_ID_WIDTH if self.TEST_ID_WIDTH > 0 else 1)
            )
            success = await self.fub_master.send(packet)
            assert success, f"Failed to send packet {i} under backpressure"

            # Random delay between packets
            delay = random.randint(1, 5)
            await self.wait_clocks(self.aclk_name, delay)

        # Wait for completion
        await self.wait_clocks(self.aclk_name, 200)

        # Check slave received all packets
        slave_stats = self.axis_slave.get_stats()
        received_packets = slave_stats.get('received_transactions', slave_stats.get('slave_stats', {}).get('received_transactions', 0))
        assert received_packets >= num_packets, f"Packets lost under backpressure: {received_packets}/{num_packets}"

        self.log.info("Backpressure test completed successfully")

    async def run_skid_buffer_stress_test(self):
        """Test skid buffer behavior under stress."""
        self.log.info("Starting skid buffer stress test")

        # Apply maximum backpressure to fill the skid buffer
        self.axis_slave.apply_backpressure(probability=0.9, min_cycles=5, max_cycles=10)

        # Send burst of packets to fill the buffer
        burst_size = self.TEST_SKID_DEPTH * 2
        for i in range(burst_size):
            data = 0x30000000 + i
            # Create packet using GAXIMaster API
            packet = self.fub_master.create_packet(
                data=data,
                last=1,
                id=i
            )
            success = await self.fub_master.send(packet)
            assert success, f"Failed to send packet {i} in burst"

        # Wait for partial completion
        await self.wait_clocks(self.aclk_name, 50)

        # Reduce backpressure and continue
        self.axis_slave.apply_backpressure(probability=0.3, min_cycles=1, max_cycles=2)

        # Send more packets
        for i in range(burst_size, burst_size + 10):
            data = 0x30000000 + i
            # Create packet using GAXIMaster API
            packet = self.fub_master.create_packet(
                data=data,
                last=1,
                id=i
            )
            success = await self.fub_master.send(packet)
            assert success, f"Failed to send packet {i} after burst"

        # Wait for all to complete
        await self.wait_clocks(self.aclk_name, 200)

        self.log.info("Skid buffer stress test completed successfully")

    async def run_busy_signal_test(self):
        """Test busy signal behavior."""
        self.log.info("Starting busy signal test")

        # Configure heavy backpressure to trigger busy
        self.axis_slave.apply_backpressure(probability=1.0, min_cycles=10, max_cycles=20)

        # Send packets and monitor busy signal
        busy_asserted = False
        busy_deasserted = False

        # Send a few packets to trigger busy
        for i in range(5):
            data = 0x40000000 + i
            # Create packet using GAXIMaster API
            packet = self.fub_master.create_packet(data=data, last=1)
            await self.fub_master.send(packet)
            await self.wait_clocks(self.aclk_name, 1)

            # Check busy signal
            try:
                busy_val = int(self.dut.busy.value)
                if busy_val == 1:
                    busy_asserted = True
                    self.log.info(f"Busy signal asserted at packet {i}")
            except:
                self.log.warning("Could not read busy signal")

        # Remove backpressure
        self.axis_slave._set_ready(1)

        # Wait and check busy deassertion
        for _ in range(50):
            await self.wait_clocks(self.aclk_name, 1)
            try:
                busy_val = int(self.dut.busy.value)
                if busy_val == 0 and busy_asserted:
                    busy_deasserted = True
                    self.log.info("Busy signal deasserted")
                    break
            except:
                pass

        self.log.info(f"Busy test: asserted={busy_asserted}, deasserted={busy_deasserted}")
        self.log.info("Busy signal test completed")

    def generate_final_report(self):
        """Generate final test report."""
        try:
            # Get component statistics
            fub_stats = self.fub_master.get_stats() if self.fub_master else {}
            slave_stats = self.axis_slave.get_stats() if self.axis_slave else {}
            monitor_stats = self.axis_monitor.get_stats() if self.axis_monitor else {}

            self.log.info("=== FINAL AXIS MASTER TEST REPORT ===")
            self.log.info(f"FUB Master Stats: {fub_stats}")
            self.log.info(f"AXIS Slave Stats: {slave_stats}")
            self.log.info(f"AXIS Monitor Stats: {monitor_stats}")
            self.log.info(f"Packets sent (FUB): {self.packets_sent_fub}")
            self.log.info(f"Frames sent: {self.frames_sent}")

            # Basic validation using actual stats keys
            master_sent = fub_stats.get('master_stats', {}).get('transactions_sent', 0)
            slave_received = slave_stats.get('observed_packets', 0)
            monitor_observed = monitor_stats.get('observed_packets', 0)

            self.log.info(f"Validation: master_sent={master_sent}, slave_received={slave_received}, monitor_observed={monitor_observed}")

            success = (
                master_sent > 0 and
                slave_received > 0 and
                monitor_observed > 0
            )

            if success:
                self.log.info("✓ Final report validation PASSED")
            else:
                self.log.error("✗ Final report validation FAILED")

            return success

        except Exception as e:
            self.log.error(f"Error generating final report: {e}")
            return False