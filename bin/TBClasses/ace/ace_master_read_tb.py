# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXI4ACEMasterReadTB
# Purpose: AXI4-ACE Read Master Testbench
#
# Documentation: cocotb-framework PyPI package
# Subsystem: framework
#
# Author: sean galloway
# Created: 2026-10-05

"""
AXI4-ACE Read Master Testbench

Simple testbench for testing AXI4-ACE read master functionality using the
CocoTB framework's AXI4/ACE components. Focuses on AR and R channel
validation, ARSNOOP passthrough, and the auto-pulsed RACK acknowledge.

The DUT (axi4ace_master_rd) is a pure skid-buffer transport; every AR field
including ARSNOOP[3:0] must appear unchanged on the m_axi_ output side, and
m_axi_rack must pulse one cycle after each RLAST handshake.
"""
import os
import random

import cocotb
from cocotb.triggers import Event, RisingEdge, with_timeout

# Framework imports
from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.gaxi.gaxi_monitor import GAXIMonitor

# ACE specific imports
from CocoTBFramework.components.ace.ace_factories import create_axi4ace_master_rd
from CocoTBFramework.components.ace.ace_field_configs import AXI4ACEFieldConfigHelper
from CocoTBFramework.components.ace.ace_transaction import ACETransactionType

# AXI4 responder and compliance checker
from CocoTBFramework.components.axi4.axi4_factories import create_axi4_slave_rd, print_compliance_reports_from_components
from CocoTBFramework.components.axi4.axi4_compliance_checker import AXI4ComplianceChecker


class AXI4ACEMasterReadTB(TBBase):
    """
    Simple AXI4-ACE Read Master testbench for baseline testing.

    Tests basic read functionality using AR and R channels with the
    axi4ace_master_rd RTL module, validates ARSNOOP passthrough, and checks
    the m_axi_rack auto-pulse behavior.
    """

    def __init__(self, dut, aclk=None, aresetn=None):
        super().__init__(dut)

        # Get test parameters from environment
        self.TEST_ID_WIDTH = self.convert_to_int(os.environ.get('TEST_ID_WIDTH', '8'))
        self.TEST_ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '32'))
        self.TEST_DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.TEST_USER_WIDTH = self.convert_to_int(os.environ.get('TEST_USER_WIDTH', '1'))
        self.TEST_CLK_PERIOD = self.convert_to_int(os.environ.get('TEST_CLK_PERIOD', '10'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TIMEOUT_CYCLES = self.convert_to_int(os.environ.get('TIMEOUT_CYCLES', '1000'))

        # ACE read modules have no stub variants: always individual signals.
        self.use_multi_sig = True

        # Initialize random generator
        random.seed(self.SEED)

        # Setup clock and reset signals
        self.aclk = aclk
        self.aclk_name = aclk._name if aclk else 'aclk'
        self.aresetn = aresetn

        # Set limits based on widths
        self.MAX_ADDR = (2**self.TEST_ADDR_WIDTH) - 1
        self.MAX_DATA = (2**self.TEST_DATA_WIDTH) - 1
        self.MAX_ID = (2**self.TEST_ID_WIDTH) - 1

        # Log configuration
        msg = '\n'
        msg += '='*80 + "\n"
        msg += ' AXI4-ACE Read Master Test Configuration:\n'
        msg += '-'*80 + "\n"
        msg += f' ID Width:     {self.TEST_ID_WIDTH}\n'
        msg += f' Addr Width:   {self.TEST_ADDR_WIDTH}\n'
        msg += f' Data Width:   {self.TEST_DATA_WIDTH}\n'
        msg += f' User Width:   {self.TEST_USER_WIDTH}\n'
        msg += f' Clock Period: {self.TEST_CLK_PERIOD} ns\n'
        msg += f' Max Addr:     0x{self.MAX_ADDR:X}\n'
        msg += f' Max Data:     0x{self.MAX_DATA:X}\n'
        msg += f' Max ID:       {self.MAX_ID}\n'
        msg += f' Seed:         {self.SEED}\n'
        msg += '='*80 + "\n"
        self.log.info(msg)

        # Create memory model for the responder side
        bytes_per_line = max(4, (self.TEST_DATA_WIDTH + 7) // 8)
        self.memory_model = MemoryModel(
            num_lines=65536,
            bytes_per_line=bytes_per_line,
            log=self.log
        )

        # Initialize memory with test patterns
        self._initialize_memory_patterns()

        # Create AXI4-ACE master read (AR + R channels) on the DUT input side
        try:
            self.master_components = create_axi4ace_master_rd(
                dut=dut,
                clock=self.aclk,
                prefix='fub_axi_',
                log=self.log,
                id_width=self.TEST_ID_WIDTH,
                addr_width=self.TEST_ADDR_WIDTH,
                data_width=self.TEST_DATA_WIDTH,
                user_width=self.TEST_USER_WIDTH,
                memory_model=self.memory_model,
                multi_sig=True
            )

            # Access individual components
            self.ar_master = self.master_components['AR']  # Drives AR channel
            self.r_slave = self.master_components['R']     # Receives R channel
            self.ace_master = self.master_components['interface']

            self.log.info("AXI4-ACE Master Read components created")
        except Exception as e:
            self.log.error(f"Failed to create ACE master components: {e}")
            raise

        # Create AXI4 slave responder on the DUT master interface side
        try:
            self.slave_components = create_axi4_slave_rd(
                dut=dut,
                clock=self.aclk,
                prefix='m_axi_',
                log=self.log,
                id_width=self.TEST_ID_WIDTH,
                addr_width=self.TEST_ADDR_WIDTH,
                data_width=self.TEST_DATA_WIDTH,
                user_width=self.TEST_USER_WIDTH,
                memory_model=self.memory_model,
                multi_sig=True
            )

            # Access individual components
            self.ar_slave = self.slave_components['AR']    # Receives AR requests
            self.r_master = self.slave_components['R']     # Drives R responses

            self.log.info("AXI4 Slave Read responder components created")
        except Exception as e:
            self.log.error(f"Failed to create slave responder components: {e}")
            raise

        # Output-side AR monitor with ACE field config so ARSNOOP is captured.
        try:
            self.output_ar_monitor = GAXIMonitor(
                dut=dut,
                title="ACE_Output_AR_Monitor",
                prefix='m_axi_',
                clock=self.aclk,
                field_config=AXI4ACEFieldConfigHelper.create_ar_field_config(
                    self.TEST_ID_WIDTH, self.TEST_ADDR_WIDTH, self.TEST_USER_WIDTH
                ),
                pkt_prefix="ar",
                multi_sig=True,
                protocol_type='axi4ace_ar_master',
                log=self.log
            )
            self.output_ar_monitor.enable_completed_packet_tracking()
            self.log.info("Output-side AR monitor created")
        except Exception as e:
            self.log.error(f"Failed to create output AR monitor: {e}")
            raise

        # AXI4 compliance checker on the output side
        self.axi4_compliance_checker = AXI4ComplianceChecker.create_if_enabled(
            dut=dut,
            clock=self.aclk,
            prefix='m_axi_',
            log=self.log,
            data_width=self.TEST_DATA_WIDTH,
            id_width=self.TEST_ID_WIDTH,
            addr_width=self.TEST_ADDR_WIDTH,
            user_width=self.TEST_USER_WIDTH,
            multi_sig=True
        )

        # Statistics tracking
        self.stats = {
            'total_reads': 0,
            'successful_reads': 0,
            'failed_reads': 0,
            'timeout_errors': 0,
            'response_errors': 0,
            'data_mismatches': 0,
            'single_reads': 0,
            'burst_reads': 0,
            'snoop_mismatches': 0,
            'rack_checks': 0,
            'test_duration': 0
        }

        # Create randomizer configurations for different test profiles
        self.randomizer_configs = self._create_randomizer_configs()
        self.set_timing_profile('normal')

        self.log.info("AXI4-ACE Read Master testbench initialized successfully")

    def _initialize_memory_patterns(self):
        """Initialize memory with known test patterns"""
        self.log.info("Initializing memory with test patterns...")

        bytes_per_word = self.TEST_DATA_WIDTH // 8

        # Pattern 1: Incremental data starting at 0x1000
        base_addr = 0x1000
        for i in range(64):
            addr = base_addr + (i * bytes_per_word)
            data = 0x10000000 + i
            data_bytes = self.memory_model.integer_to_bytearray(data, bytes_per_word)
            self.memory_model.write(addr, data_bytes)

        # Pattern 2: Address-based pattern at 0x2000
        base_addr = 0x2000
        for i in range(32):
            addr = base_addr + (i * bytes_per_word)
            data = addr & self.MAX_DATA
            data_bytes = self.memory_model.integer_to_bytearray(data, bytes_per_word)
            self.memory_model.write(addr, data_bytes)

        # Pattern 3: Fixed patterns at 0x3000
        test_patterns = [0xDEADBEEF, 0xCAFEBABE, 0x12345678, 0xABCDEF00]
        base_addr = 0x3000
        for i, pattern in enumerate(test_patterns * 8):
            addr = base_addr + (i * bytes_per_word)
            data = pattern & self.MAX_DATA
            data_bytes = self.memory_model.integer_to_bytearray(data, bytes_per_word)
            self.memory_model.write(addr, data_bytes)

        self.log.info("Memory patterns initialized")

    def _create_randomizer_configs(self):
        """Create randomizer configurations for different test profiles"""
        configs = {
            'fast': {
                'master_delay': ([(0, 0), (1, 2)], [0.8, 0.2]),
                'slave_delay': ([(0, 1), (1, 2)], [0.7, 0.3])
            },
            'normal': {
                'master_delay': ([(0, 2), (3, 5)], [0.6, 0.4]),
                'slave_delay': ([(1, 3), (4, 6)], [0.6, 0.4])
            },
            'slow': {
                'master_delay': ([(2, 5), (6, 10)], [0.5, 0.5]),
                'slave_delay': ([(3, 7), (8, 12)], [0.5, 0.5])
            },
            'backtoback': {
                'master_delay': ([(0, 0)], [1.0]),
                'slave_delay': ([(0, 0)], [1.0])
            },
            'stress': {
                'master_delay': ([(0, 0), (1, 3), (4, 8)], [0.5, 0.3, 0.2]),
                'slave_delay': ([(0, 1), (2, 5), (6, 10)], [0.4, 0.4, 0.2])
            }
        }
        return configs

    def set_timing_profile(self, profile_name):
        """Set timing profile and actually apply FlexRandomizers."""
        if profile_name not in self.randomizer_configs:
            self.log.warning(f"Unknown timing profile '{profile_name}', using 'normal'")
            profile_name = 'normal'
        config = self.randomizer_configs[profile_name]

        applied = []
        if getattr(self, 'ar_master', None) is not None:
            self.ar_master.set_randomizer(
                FlexRandomizer({'valid_delay': config['master_delay']}))
            applied.append('ar_master.valid_delay')
        if getattr(self, 'r_master', None) is not None:
            self.r_master.set_randomizer(
                FlexRandomizer({'valid_delay': config['slave_delay']}))
            applied.append('r_master.valid_delay')
        if getattr(self, 'r_slave', None) is not None:
            self.r_slave.set_randomizer(
                FlexRandomizer({'ready_delay': config['master_delay']}))
            applied.append('r_slave.ready_delay')

        self.log.info(f"Set timing profile to '{profile_name}' -> {', '.join(applied) or 'NOTHING'}")
        return applied

    async def assert_reset(self):
        """Assert reset and initialize components"""
        self.aresetn.value = 0
        await self.ar_master.reset_bus()
        await self.r_master.reset_bus()
        await self.wait_clocks(self.aclk_name, 5)
        self.log.info("Reset asserted")

    async def deassert_reset(self):
        """Deassert reset"""
        self.aresetn.value = 1
        await self.wait_clocks(self.aclk_name, 5)
        self.log.info(f"Reset deasserted{self.get_time_ns_str()}")

    def _calculate_arsize(self):
        """Calculate ARSIZE field based on data width"""
        bytes_per_beat = self.TEST_DATA_WIDTH // 8
        return bytes_per_beat.bit_length() - 1

    def _drain_output_ar_packets(self):
        """Drain all completed AR packets observed on the output side."""
        return self.output_ar_monitor.get_completed_packets()

    # Core test methods

    async def single_read_test(self, addr, expected_data=None, arid=None,
                               snoop_type=ACETransactionType.READ_SHARED):
        """
        Perform a single AXI4-ACE read transaction.

        Returns:
            tuple: (success, actual_data, response_info)
        """
        if arid is None:
            arid = random.randint(0, self.MAX_ID)

        if expected_data is None:
            bytes_per_word = self.TEST_DATA_WIDTH // 8
            expected_data_bytes = self.memory_model.read(addr, bytes_per_word)
            expected_data = int.from_bytes(expected_data_bytes, byteorder='little')

        self.log.debug(
            f"Single ACE read: addr=0x{addr:08X}, id={arid}, "
            f"snoop={snoop_type.name}, expected=0x{expected_data:08X}"
        )

        try:
            self.stats['total_reads'] += 1
            self.stats['single_reads'] += 1

            actual_data = await self.ace_master.single_read(
                address=addr,
                id=arid,
                size=self._calculate_arsize(),
                burst_type=1,
                snoop_type=snoop_type
            )

            if actual_data != expected_data:
                self.log.warning(
                    f"Data mismatch at 0x{addr:08X}: got 0x{actual_data:08X}, "
                    f"expected 0x{expected_data:08X}"
                )
                self.stats['data_mismatches'] += 1
                self.stats['failed_reads'] += 1
                return False, actual_data, {
                    'expected': expected_data,
                    'actual': actual_data,
                    'mismatch': True
                }

            # Validate output-side AR passthrough
            ar_packets = self._drain_output_ar_packets()
            snoop_ok, ar_info = self._check_output_ar(
                ar_packets, arid, addr, 0, snoop_type
            )
            if not snoop_ok:
                self.stats['snoop_mismatches'] += 1
                self.stats['failed_reads'] += 1
                return False, actual_data, ar_info

            self.stats['successful_reads'] += 1
            return True, actual_data, {
                'expected': expected_data,
                'actual': actual_data,
                'id': arid,
                'output_ar': ar_info
            }

        except Exception as e:
            self.log.error(f"ACE read failed with exception: {e}")
            self.stats['failed_reads'] += 1
            self.stats['timeout_errors'] += 1
            return False, 0, {'error': str(e)}

    async def burst_read_test(self, addr, burst_len, arid=None,
                              snoop_type=ACETransactionType.READ_SHARED):
        """
        Perform a burst AXI4-ACE read transaction.

        Returns:
            tuple: (success, data_list, response_info)
        """
        if arid is None:
            arid = random.randint(0, self.MAX_ID)

        self.log.debug(
            f"Burst ACE read: addr=0x{addr:08X}, len={burst_len}, "
            f"id={arid}, snoop={snoop_type.name}"
        )

        try:
            self.stats['total_reads'] += 1
            self.stats['burst_reads'] += 1

            data_list = await self.ace_master.read_transaction(
                address=addr,
                burst_len=burst_len,
                id=arid,
                size=self._calculate_arsize(),
                burst_type=1,
                snoop_type=snoop_type
            )

            if len(data_list) != burst_len:
                self.log.error(
                    f"Burst length mismatch: got {len(data_list)}, expected {burst_len}"
                )
                self.stats['failed_reads'] += 1
                return False, data_list, {'length_mismatch': True}

            # Validate data against memory model
            bytes_per_word = self.TEST_DATA_WIDTH // 8
            data_valid = True
            for i, actual_data in enumerate(data_list):
                expected_addr = addr + (i * bytes_per_word)
                expected_bytes = self.memory_model.read(expected_addr, bytes_per_word)
                expected_data = int.from_bytes(expected_bytes, byteorder='little') & self.MAX_DATA
                actual_data &= self.MAX_DATA
                if actual_data != expected_data:
                    self.log.error(
                        f"Burst data mismatch at beat {i}: addr=0x{expected_addr:08X}, "
                        f"expected=0x{expected_data:08X}, actual=0x{actual_data:08X}"
                    )
                    self.stats['data_mismatches'] += 1
                    data_valid = False

            # Validate output-side AR passthrough
            ar_packets = self._drain_output_ar_packets()
            snoop_ok, ar_info = self._check_output_ar(
                ar_packets, arid, addr, burst_len - 1, snoop_type
            )
            if not snoop_ok:
                self.stats['snoop_mismatches'] += 1
                self.stats['failed_reads'] += 1
                return False, data_list, ar_info

            if data_valid:
                self.stats['successful_reads'] += 1
                return True, data_list, {
                    'burst_len': burst_len,
                    'data_count': len(data_list),
                    'id': arid,
                    'output_ar': ar_info
                }
            else:
                self.stats['failed_reads'] += 1
                return False, data_list, {'error': 'Data validation failed'}

        except Exception as e:
            self.log.error(f"ACE burst read failed with exception: {e}")
            self.stats['failed_reads'] += 1
            self.stats['timeout_errors'] += 1
            return False, [], {'error': str(e)}

    def _check_output_ar(self, ar_packets, expected_id, expected_addr,
                         expected_len, expected_snoop):
        """
        Check that the captured output-side AR packet matches the request.

        Returns:
            tuple: (ok, info_dict)
        """
        expected_snoop_val = int(expected_snoop)

        if not ar_packets:
            return False, {'error': 'No output AR packet captured'}

        # Use the last captured AR packet (most recent transaction)
        ar_pkt = ar_packets[-1]
        pkt_id = getattr(ar_pkt, 'id', None)
        pkt_addr = getattr(ar_pkt, 'addr', None)
        pkt_len = getattr(ar_pkt, 'len', None)
        pkt_snoop = getattr(ar_pkt, 'snoop', None)

        info = {
            'expected_id': expected_id,
            'actual_id': pkt_id,
            'expected_addr': expected_addr,
            'actual_addr': pkt_addr,
            'expected_len': expected_len,
            'actual_len': pkt_len,
            'expected_snoop': expected_snoop_val,
            'actual_snoop': pkt_snoop,
        }

        if pkt_id != expected_id:
            self.log.error(f"Output AR ID mismatch: expected {expected_id}, got {pkt_id}")
            return False, info
        if pkt_addr != expected_addr:
            self.log.error(
                f"Output AR ADDR mismatch: expected 0x{expected_addr:08X}, "
                f"got 0x{pkt_addr:08X}"
            )
            return False, info
        if pkt_len != expected_len:
            self.log.error(f"Output AR LEN mismatch: expected {expected_len}, got {pkt_len}")
            return False, info
        if pkt_snoop != expected_snoop_val:
            self.log.error(
                f"Output AR SNOOP mismatch: expected 0x{expected_snoop_val:X} "
                f"({expected_snoop.name}), got 0x{pkt_snoop:X}"
            )
            return False, info

        return True, info

    # High-level test sequences

    async def basic_read_sequence(self, count=10):
        """Run basic single read sequence"""
        self.log.info(f"Running basic read sequence ({count} reads)...")

        success_count = 0
        base_addr = 0x1000

        for i in range(count):
            addr = base_addr + (i * (self.TEST_DATA_WIDTH // 8))
            success, data, info = await self.single_read_test(addr)
            if success:
                success_count += 1

            await self.wait_clocks(self.aclk_name, 2)

        self.log.info(f"Basic sequence result: {success_count}/{count} successful")
        return success_count == count

    async def burst_read_sequence(self, burst_lengths=[2, 4, 8, 16]):
        """Run burst read sequence with different lengths"""
        self.log.info(f"Running burst read sequence: {burst_lengths}")

        success_count = 0
        base_addr = 0x2000

        for i, burst_len in enumerate(burst_lengths):
            addr = base_addr + (i * burst_len * (self.TEST_DATA_WIDTH // 8))
            success, data, info = await self.burst_read_test(addr, burst_len)
            if success:
                success_count += 1

            await self.wait_clocks(self.aclk_name, 5)

        self.log.info(f"Burst sequence result: {success_count}/{len(burst_lengths)} successful")
        return success_count == len(burst_lengths)

    async def stress_read_test(self, count=50):
        """Run stress test with rapid reads"""
        self.log.info(f"Running stress read test ({count} reads)...")

        self.set_timing_profile('stress')

        success_count = 0
        for i in range(count):
            addr_ranges = [0x1000, 0x2000, 0x3000]
            base_addr = random.choice(addr_ranges)
            offset = random.randint(0, 31) * (self.TEST_DATA_WIDTH // 8)
            addr = base_addr + offset

            success, data, info = await self.single_read_test(addr)
            if success:
                success_count += 1

        self.log.info(f"Stress test result: {success_count}/{count} successful")
        return success_count >= (count * 0.95)

    async def snoop_type_matrix_test(self):
        """
        Issue single and burst reads for every ACETransactionType member and
        verify AR field passthrough (including ARSNOOP) and data integrity.
        """
        self.log.info("=== ACE Snoop-Type Matrix Test ===")

        bytes_per_word = self.TEST_DATA_WIDTH // 8
        success_count = 0
        total_count = 0

        for snoop_type in ACETransactionType:
            total_count += 1
            addr = 0x1000 + (total_count * bytes_per_word)
            arid = total_count % (self.MAX_ID + 1)

            self.log.info(f"Testing snoop type {snoop_type.name} (0x{int(snoop_type):X})")

            # Single read
            success, _, info = await self.single_read_test(
                addr, arid=arid, snoop_type=snoop_type
            )
            if not success:
                self.log.error(f"Single read failed for {snoop_type.name}: {info}")
                continue

            # Burst read (4 beats)
            burst_addr = 0x2000 + (total_count * 4 * bytes_per_word)
            burst_id = (total_count + 1) % (self.MAX_ID + 1)
            success, _, info = await self.burst_read_test(
                burst_addr, 4, arid=burst_id, snoop_type=snoop_type
            )
            if not success:
                self.log.error(f"Burst read failed for {snoop_type.name}: {info}")
                continue

            success_count += 1

        self.log.info(f"Snoop-type matrix result: {success_count}/{len(ACETransactionType)} types passed")
        return success_count == len(ACETransactionType)

    async def rack_check_test(self):
        """
        Verify that m_axi_rack pulses one cycle after the final RLAST handshake
        and stays low during the burst beats.
        """
        self.log.info("=== ACE RACK Check Test ===")

        self.stats['rack_checks'] += 1
        addr = 0x4000
        burst_len = 4
        arid = 0x55 & self.MAX_ID
        snoop_type = ACETransactionType.READ_SHARED

        # Pre-charge memory at the burst address
        bytes_per_word = self.TEST_DATA_WIDTH // 8
        for i in range(burst_len):
            data = (0x50000000 + i) & self.MAX_DATA
            self.memory_model.write(
                addr + (i * bytes_per_word),
                self.memory_model.integer_to_bytearray(data, bytes_per_word)
            )

        # Confirm RACK is low before the read starts
        await RisingEdge(self.aclk)
        if int(self.dut.m_axi_rack.value) != 0:
            raise AssertionError("RACK was high before read started")

        rack_event = Event()

        async def _watch_rack():
            await RisingEdge(self.dut.m_axi_rack)
            rack_event.set()

        cocotb.start_soon(_watch_rack())

        # Sample RACK on every rising clock edge until explicitly stopped
        rack_samples = []
        stop_sampling = Event()

        async def _sample_rack():
            while not stop_sampling.is_set():
                await RisingEdge(self.aclk)
                rack_samples.append(int(self.dut.m_axi_rack.value))

        sampler = cocotb.start_soon(_sample_rack())

        success, data_list, info = await self.burst_read_test(
            addr, burst_len, arid=arid, snoop_type=snoop_type
        )

        if not success:
            stop_sampling.set()
            await RisingEdge(self.aclk)
            await sampler
            self.log.error(f"RACK check read failed: {info}")
            return False

        try:
            await with_timeout(rack_event.wait(), 1, 'us')
        except Exception as exc:
            stop_sampling.set()
            await RisingEdge(self.aclk)
            await sampler
            self.log.error(f"m_axi_rack did not pulse after RLAST: {exc}")
            return False

        # Let the sampler run a couple more cycles to guarantee it captures the
        # pulse, then stop it cleanly.
        await RisingEdge(self.aclk)
        await RisingEdge(self.aclk)
        stop_sampling.set()
        await RisingEdge(self.aclk)
        await sampler

        if not any(rack_samples):
            self.log.error("RACK sample buffer contains no high sample")
            return False

        first_high = next((i for i, v in enumerate(rack_samples) if v), None)
        if first_high is None:
            self.log.error("RACK never went high in sampled data")
            return False

        spurious = any(v for v in rack_samples[:first_high])
        if spurious:
            self.log.error(
                f"RACK was high before the expected pulse (first high at sample {first_high})"
            )
            return False

        self.log.info("RACK pulse check passed")
        return True

    async def wait_for_quiescence(self, idle_cycles=10):
        """Wait until the DUT reports no activity and busy goes low."""
        for _ in range(idle_cycles):
            await RisingEdge(self.aclk)
        busy_val = int(self.dut.busy.value) if hasattr(self.dut, 'busy') else -1
        self.log.info(f"Busy output after quiescence: {busy_val}")
        return busy_val == 0

    def get_test_stats(self):
        """Get comprehensive test statistics"""
        total_tests = self.stats['total_reads']
        success_rate = (self.stats['successful_reads'] / total_tests * 100) if total_tests > 0 else 0

        self.finalize_test()

        return {
            'summary': {
                'total_reads': total_tests,
                'successful_reads': self.stats['successful_reads'],
                'success_rate': f"{success_rate:.1f}%"
            },
            'details': self.stats.copy()
        }

    def reset_stats(self):
        """Reset all statistics"""
        for key in self.stats:
            if isinstance(self.stats[key], int):
                self.stats[key] = 0

    def finalize_test(self):
        """Print compliance reports for all components."""
        print_compliance_reports_from_components(self.master_components)
        print_compliance_reports_from_components(self.slave_components)

        if hasattr(self, 'axi4_compliance_checker') and self.axi4_compliance_checker:
            self.axi4_compliance_checker.print_compliance_report()
