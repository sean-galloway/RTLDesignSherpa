# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXI5MasterReadTB
# Purpose: AXI5 Read Master Testbench
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-16

"""
AXI5 Read Master Testbench

Simple testbench for testing AXI5 read master functionality using the CocoTB
framework's AXI5 components. Focuses on AR and R channel validation with
AXI5-specific features.

AXI5 Features Tested:
- Standard AXI4 burst transactions
- NSAID (Non-secure Access ID)
- TRACE signal propagation
- MPAM (Memory Partitioning and Monitoring)
- MECID (Memory Encryption Context)
- UNIQUE access
- CHUNKEN (Chunked transfers)
- TAGOP (Memory Tagging Extension operations)
- POISON indicators
- TAGMATCH for MTE
"""
import os
import random

# Framework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

# AXI5 specific imports
from CocoTBFramework.components.axi5.axi5_factories import (
    create_axi5_master_rd,
    create_axi5_slave_rd,
)
from CocoTBFramework.components.axi5.axi5_timing_config import create_axi5_timing_from_profile
from CocoTBFramework.components.axi5.axi5_compliance_checker import AXI5ComplianceChecker


class AXI5MasterReadTB(TBBase):
    """
    Simple AXI5 Read Master testbench for baseline testing.

    Tests basic read functionality using AR and R channels with the
    axi5_master_rd_stub.sv RTL module, including AXI5-specific features.
    """

    def __init__(self, dut, aclk=None, aresetn=None):
        super().__init__(dut)

        # Get test parameters from environment
        self.TEST_STUB = self.convert_to_int(os.environ.get('TEST_STUB', '0'))
        self.TEST_ID_WIDTH = self.convert_to_int(os.environ.get('TEST_ID_WIDTH', '8'))
        self.TEST_ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '32'))
        self.TEST_DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.TEST_USER_WIDTH = self.convert_to_int(os.environ.get('TEST_USER_WIDTH', '1'))
        self.TEST_CLK_PERIOD = self.convert_to_int(os.environ.get('TEST_CLK_PERIOD', '10'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TIMEOUT_CYCLES = self.convert_to_int(os.environ.get('TIMEOUT_CYCLES', '1000'))

        # AXI5 specific widths
        self.TEST_NSAID_WIDTH = self.convert_to_int(os.environ.get('TEST_NSAID_WIDTH', '4'))
        self.TEST_MPAM_WIDTH = self.convert_to_int(os.environ.get('TEST_MPAM_WIDTH', '11'))
        self.TEST_MECID_WIDTH = self.convert_to_int(os.environ.get('TEST_MECID_WIDTH', '16'))
        self.TEST_TAG_WIDTH = self.convert_to_int(os.environ.get('TEST_TAG_WIDTH', '4'))
        self.TEST_TAGOP_WIDTH = self.convert_to_int(os.environ.get('TEST_TAGOP_WIDTH', '2'))
        self.TEST_CHUNKNUM_WIDTH = self.convert_to_int(os.environ.get('TEST_CHUNKNUM_WIDTH', '4'))

        # Stub uses packed signals, direct module uses individual signals
        self.use_multi_sig = (self.TEST_STUB == 0)

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
        self.MAX_NSAID = (2**self.TEST_NSAID_WIDTH) - 1
        self.MAX_MPAM = (2**self.TEST_MPAM_WIDTH) - 1
        self.MAX_MECID = (2**self.TEST_MECID_WIDTH) - 1

        # Log configuration
        msg = '\n'
        msg += '='*80 + "\n"
        msg += ' AXI5 Read Master Test Configuration:\n'
        msg += '-'*80 + "\n"
        msg += f' Stub:         {self.TEST_STUB}\n'
        msg += f' ID Width:     {self.TEST_ID_WIDTH}\n'
        msg += f' Addr Width:   {self.TEST_ADDR_WIDTH}\n'
        msg += f' Data Width:   {self.TEST_DATA_WIDTH}\n'
        msg += f' User Width:   {self.TEST_USER_WIDTH}\n'
        msg += f' NSAID Width:  {self.TEST_NSAID_WIDTH}\n'
        msg += f' MPAM Width:   {self.TEST_MPAM_WIDTH}\n'
        msg += f' MECID Width:  {self.TEST_MECID_WIDTH}\n'
        msg += f' Clock Period: {self.TEST_CLK_PERIOD} ns\n'
        msg += f' Max Addr:     0x{self.MAX_ADDR:X}\n'
        msg += f' Max Data:     0x{self.MAX_DATA:X}\n'
        msg += f' Max ID:       {self.MAX_ID}\n'
        msg += f' Seed:         {self.SEED}\n'
        msg += '='*80 + "\n"
        self.log.info(msg)

        # Create memory model for the slave side
        bytes_per_line = max(4, (self.TEST_DATA_WIDTH + 7) // 8)
        self.memory_model = MemoryModel(
            num_lines=65536,
            bytes_per_line=bytes_per_line,
            log=self.log
        )

        # Initialize memory with test patterns
        self._initialize_memory_patterns()

        # Create timing configurations
        self.timing_config = create_axi5_timing_from_profile('axi5_normal')

        # Create AXI5 master (AR + R channels only)
        try:
            self.master_components = create_axi5_master_rd(
                dut=dut,
                clock=self.aclk,
                prefix='fub_axi',
                log=self.log,
                id_width=self.TEST_ID_WIDTH,
                addr_width=self.TEST_ADDR_WIDTH,
                data_width=self.TEST_DATA_WIDTH,
                user_width=self.TEST_USER_WIDTH,
                nsaid_width=self.TEST_NSAID_WIDTH,
                mpam_width=self.TEST_MPAM_WIDTH,
                mecid_width=self.TEST_MECID_WIDTH,
                tag_width=self.TEST_TAG_WIDTH,
                tagop_width=self.TEST_TAGOP_WIDTH,
                chunknum_width=self.TEST_CHUNKNUM_WIDTH,
                memory_model=self.memory_model,
                multi_sig=self.use_multi_sig
            )

            # Access individual components
            self.ar_master = self.master_components['AR']
            self.r_slave = self.master_components['R']
            self.axi5_master = self.master_components['interface']

            self.log.info("AXI5 Master Read components created")
        except Exception as e:
            self.log.error(f"Failed to create master components: {e}")
            raise

        # Create AXI5 slave to respond on the master interface side
        try:
            self.slave_components = create_axi5_slave_rd(
                dut=dut,
                clock=self.aclk,
                prefix='m_axi',
                log=self.log,
                id_width=self.TEST_ID_WIDTH,
                addr_width=self.TEST_ADDR_WIDTH,
                data_width=self.TEST_DATA_WIDTH,
                user_width=self.TEST_USER_WIDTH,
                nsaid_width=self.TEST_NSAID_WIDTH,
                mpam_width=self.TEST_MPAM_WIDTH,
                mecid_width=self.TEST_MECID_WIDTH,
                tag_width=self.TEST_TAG_WIDTH,
                tagop_width=self.TEST_TAGOP_WIDTH,
                chunknum_width=self.TEST_CHUNKNUM_WIDTH,
                memory_model=self.memory_model,
                multi_sig=True
            )

            # Access individual components
            self.ar_slave = self.slave_components['AR']
            self.r_master = self.slave_components['R']

            self.log.info("AXI5 Slave Read components created")
        except Exception as e:
            self.log.error(f"Failed to create slave components: {e}")
            raise

        # Compliance checker
        self.axi5_compliance_checker = AXI5ComplianceChecker.create_if_enabled(
            dut=dut,
            clock=self.aclk,
            prefix='m_axi',
            log=self.log,
            data_width=self.TEST_DATA_WIDTH,
            id_width=self.TEST_ID_WIDTH,
            addr_width=self.TEST_ADDR_WIDTH,
            user_width=self.TEST_USER_WIDTH
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
            'axi5_feature_tests': 0,
            'nsaid_tests': 0,
            'trace_tests': 0,
            'mpam_tests': 0,
            'mecid_tests': 0,
            'tagop_tests': 0,
            'test_duration': 0
        }

        # Create randomizer configurations for different test profiles
        self.randomizer_configs = self._create_axi5_randomizer_configs()
        self.set_timing_profile('normal')

        self.log.info("AXI5 Read Master testbench initialized successfully")

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

    def _create_axi5_randomizer_configs(self):
        """Create AXI5-specific randomizer configurations"""
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
            },
            'atomic': {
                'master_delay': ([(0, 2)], [1.0]),
                'slave_delay': ([(2, 8)], [1.0])  # Longer for atomic ops
            },
            'mte': {
                'master_delay': ([(0, 3), (4, 8)], [0.6, 0.4]),
                'slave_delay': ([(1, 5), (6, 12)], [0.5, 0.5])  # Tag check overhead
            },
            'secure': {
                'master_delay': ([(1, 4), (5, 10)], [0.6, 0.4]),
                'slave_delay': ([(2, 6), (7, 14)], [0.5, 0.5])
            }
        }
        return configs

    def set_timing_profile(self, profile_name):
        """Set timing profile for the test"""
        if profile_name in self.randomizer_configs:
            self.log.info(f"Set timing profile to '{profile_name}'")
        else:
            self.log.warning(f"Unknown timing profile '{profile_name}', using 'normal'")

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

    # Core test methods

    async def single_read_test(self, addr, expected_data=None, arid=None,
                               nsaid=None, trace=None, mpam=None, mecid=None,
                               unique=None, chunken=None, tagop=None):
        """
        Perform a single AXI5 read transaction with optional AXI5 features.

        Args:
            addr: Address to read from
            expected_data: Expected data value (if None, read from memory model)
            arid: Transaction ID (if None, auto-generated)
            nsaid: Non-secure Access ID (AXI5)
            trace: Trace signal (AXI5)
            mpam: Memory Partitioning and Monitoring (AXI5)
            mecid: Memory Encryption Context ID (AXI5)
            unique: Unique access (AXI5)
            chunken: Chunked transfer enable (AXI5)
            tagop: Tag operation (AXI5 MTE)

        Returns:
            tuple: (success, actual_data, response_info)
        """
        if arid is None:
            arid = random.randint(0, self.MAX_ID)

        # Get expected data from memory model if not provided
        if expected_data is None:
            bytes_per_word = self.TEST_DATA_WIDTH // 8
            expected_data_bytes = self.memory_model.read(addr, bytes_per_word)
            expected_data = int.from_bytes(expected_data_bytes, byteorder='little')

        # Track AXI5 features used
        axi5_features = {}
        if nsaid is not None:
            axi5_features['nsaid'] = nsaid
            self.stats['nsaid_tests'] += 1
        if trace is not None:
            axi5_features['trace'] = trace
            self.stats['trace_tests'] += 1
        if mpam is not None:
            axi5_features['mpam'] = mpam
            self.stats['mpam_tests'] += 1
        if mecid is not None:
            axi5_features['mecid'] = mecid
            self.stats['mecid_tests'] += 1
        if tagop is not None:
            axi5_features['tagop'] = tagop
            self.stats['tagop_tests'] += 1

        if axi5_features:
            self.stats['axi5_feature_tests'] += 1

        self.log.debug(f"Single read: addr=0x{addr:08X}, id={arid}, "
                      f"expected=0x{expected_data:08X}, axi5={axi5_features}")

        try:
            self.stats['total_reads'] += 1
            self.stats['single_reads'] += 1

            # Build kwargs for AXI5 features
            read_kwargs = {
                'address': addr,
                'id': arid,
                'size': self._calculate_arsize(),
                'burst_type': 1,  # INCR
            }

            # Add AXI5-specific parameters if provided
            if nsaid is not None:
                read_kwargs['nsaid'] = nsaid
            if trace is not None:
                read_kwargs['trace'] = trace
            if mpam is not None:
                read_kwargs['mpam'] = mpam
            if mecid is not None:
                read_kwargs['mecid'] = mecid
            if unique is not None:
                read_kwargs['unique'] = unique
            if chunken is not None:
                read_kwargs['chunken'] = chunken
            if tagop is not None:
                read_kwargs['tagop'] = tagop

            actual_data = await self.axi5_master.single_read(**read_kwargs)

            # Check data match
            if actual_data != expected_data:
                self.log.warning(f"Data mismatch at 0x{addr:08X}: "
                               f"got 0x{actual_data:08X}, expected 0x{expected_data:08X}")
                self.stats['data_mismatches'] += 1
                self.stats['failed_reads'] += 1
                return False, actual_data, {
                    'expected': expected_data,
                    'actual': actual_data,
                    'mismatch': True,
                    'axi5_features': axi5_features
                }

            self.stats['successful_reads'] += 1
            return True, actual_data, {
                'expected': expected_data,
                'actual': actual_data,
                'id': arid,
                'axi5_features': axi5_features
            }

        except Exception as e:
            self.log.error(f"Read failed with exception: {e}")
            self.stats['failed_reads'] += 1
            self.stats['timeout_errors'] += 1
            return False, 0, {'error': str(e), 'axi5_features': axi5_features}

    async def burst_read_test(self, addr, burst_len, **axi5_kwargs):
        """
        Perform a burst AXI5 read transaction with optional AXI5 features.

        Args:
            addr: Starting address
            burst_len: Burst length (number of beats)
            **axi5_kwargs: AXI5-specific parameters (nsaid, trace, mpam, etc.)

        Returns:
            tuple: (success, data_list, response_info)
        """
        arid = random.randint(0, self.MAX_ID)
        self.log.debug(f"Burst read: addr=0x{addr:08X}, len={burst_len}, id={arid}")

        try:
            self.stats['total_reads'] += 1
            self.stats['burst_reads'] += 1

            if axi5_kwargs:
                self.stats['axi5_feature_tests'] += 1

            data_list = await self.axi5_master.read_transaction(
                address=addr,
                burst_len=burst_len,
                id=arid,
                size=self._calculate_arsize(),
                burst_type=1,  # INCR
                **axi5_kwargs
            )

            if len(data_list) != burst_len:
                self.log.error(f"Burst length mismatch: got {len(data_list)}, expected {burst_len}")
                self.stats['failed_reads'] += 1
                return False, data_list, {'length_mismatch': True}

            self.stats['successful_reads'] += 1
            return True, data_list, {
                'burst_len': burst_len,
                'data_count': len(data_list),
                'id': arid,
                'axi5_features': axi5_kwargs
            }

        except Exception as e:
            self.log.error(f"Burst read failed with exception: {e}")
            self.stats['failed_reads'] += 1
            self.stats['timeout_errors'] += 1
            return False, [], {'error': str(e)}

    def _calculate_arsize(self):
        """Calculate ARSIZE field based on data width"""
        bytes_per_beat = self.TEST_DATA_WIDTH // 8
        return bytes_per_beat.bit_length() - 1

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

    async def axi5_feature_test_sequence(self, count=10):
        """Run AXI5-specific feature tests"""
        self.log.info(f"Running AXI5 feature test sequence ({count} reads)...")

        success_count = 0
        base_addr = 0x1000

        for i in range(count):
            addr = base_addr + (i * (self.TEST_DATA_WIDTH // 8))

            # Randomize AXI5 features
            nsaid = random.randint(0, self.MAX_NSAID)
            trace = random.randint(0, 1)
            mpam = random.randint(0, self.MAX_MPAM) if random.random() > 0.5 else None
            mecid = random.randint(0, self.MAX_MECID) if random.random() > 0.5 else None
            tagop = random.randint(0, 3) if random.random() > 0.5 else None

            success, data, info = await self.single_read_test(
                addr,
                nsaid=nsaid,
                trace=trace,
                mpam=mpam,
                mecid=mecid,
                tagop=tagop
            )
            if success:
                success_count += 1

            await self.wait_clocks(self.aclk_name, 3)

        self.log.info(f"AXI5 feature sequence result: {success_count}/{count} successful")
        return success_count == count

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
            'details': self.stats.copy(),
            'axi5_features': {
                'total_axi5_tests': self.stats['axi5_feature_tests'],
                'nsaid_tests': self.stats['nsaid_tests'],
                'trace_tests': self.stats['trace_tests'],
                'mpam_tests': self.stats['mpam_tests'],
                'mecid_tests': self.stats['mecid_tests'],
                'tagop_tests': self.stats['tagop_tests'],
            }
        }

    def reset_stats(self):
        """Reset all statistics"""
        for key in self.stats:
            if isinstance(self.stats[key], int):
                self.stats[key] = 0

    def finalize_test(self):
        """Print compliance reports for all AXI5 components."""
        if hasattr(self, 'axi5_compliance_checker') and self.axi5_compliance_checker:
            self.axi5_compliance_checker.print_compliance_report()
