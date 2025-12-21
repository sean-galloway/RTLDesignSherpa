# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXI5SlaveWriteTB
# Purpose: AXI5 Write Slave Testbench
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-19

"""
AXI5 Write Slave Testbench

Simple testbench for testing AXI5 write slave functionality using the CocoTB
framework's AXI5 components. Focuses on AW, W, and B channel validation with
AXI5-specific features from the slave perspective.

AXI5 Features Tested:
- Standard AXI4 burst transactions
- ATOP (Atomic Operations)
- NSAID (Non-secure Access ID)
- TRACE signal propagation
- MPAM (Memory Partitioning and Monitoring)
- MECID (Memory Encryption Context)
- UNIQUE access
- TAGOP (Memory Tagging Extension operations)
- TAG values on AW, W, and B channels
- POISON indicators
- TAGUPDATE on W channel
- TAGMATCH on B channel
"""
import os
import random

# Framework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

# AXI5 specific imports
from CocoTBFramework.components.axi5.axi5_factories import (
    create_axi5_master_wr,
    create_axi5_slave_wr,
)
from CocoTBFramework.components.axi5.axi5_timing_config import create_axi5_timing_from_profile
from CocoTBFramework.components.axi5.axi5_compliance_checker import AXI5ComplianceChecker


class AXI5SlaveWriteTB(TBBase):
    """
    Simple AXI5 Write Slave testbench for baseline testing.

    Tests basic write functionality using AW, W, and B channels with the
    axi5_slave_wr_stub.sv RTL module, including AXI5-specific features.
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
        self.TEST_ATOP_WIDTH = self.convert_to_int(os.environ.get('TEST_ATOP_WIDTH', '6'))
        self.TEST_NSAID_WIDTH = self.convert_to_int(os.environ.get('TEST_NSAID_WIDTH', '4'))
        self.TEST_MPAM_WIDTH = self.convert_to_int(os.environ.get('TEST_MPAM_WIDTH', '11'))
        self.TEST_MECID_WIDTH = self.convert_to_int(os.environ.get('TEST_MECID_WIDTH', '16'))
        self.TEST_TAG_WIDTH = self.convert_to_int(os.environ.get('TEST_TAG_WIDTH', '4'))
        self.TEST_TAGOP_WIDTH = self.convert_to_int(os.environ.get('TEST_TAGOP_WIDTH', '2'))

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
        self.MAX_ATOP = (2**self.TEST_ATOP_WIDTH) - 1

        # Log configuration
        msg = '\n'
        msg += '='*80 + "\n"
        msg += ' AXI5 Write Slave Test Configuration:\n'
        msg += '-'*80 + "\n"
        msg += f' Stub:         {self.TEST_STUB}\n'
        msg += f' ID Width:     {self.TEST_ID_WIDTH}\n'
        msg += f' Addr Width:   {self.TEST_ADDR_WIDTH}\n'
        msg += f' Data Width:   {self.TEST_DATA_WIDTH}\n'
        msg += f' User Width:   {self.TEST_USER_WIDTH}\n'
        msg += f' ATOP Width:   {self.TEST_ATOP_WIDTH}\n'
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

        # Create AXI5 master to drive the slave interface (on s_axi side)
        try:
            self.master_components = create_axi5_master_wr(
                dut=dut,
                clock=self.aclk,
                prefix='s_axi',
                log=self.log,
                id_width=self.TEST_ID_WIDTH,
                addr_width=self.TEST_ADDR_WIDTH,
                data_width=self.TEST_DATA_WIDTH,
                user_width=self.TEST_USER_WIDTH,
                atop_width=self.TEST_ATOP_WIDTH,
                nsaid_width=self.TEST_NSAID_WIDTH,
                mpam_width=self.TEST_MPAM_WIDTH,
                mecid_width=self.TEST_MECID_WIDTH,
                tag_width=self.TEST_TAG_WIDTH,
                tagop_width=self.TEST_TAGOP_WIDTH,
                memory_model=self.memory_model,
                multi_sig=True
            )

            # Access individual components
            self.aw_master = self.master_components['AW']
            self.w_master = self.master_components['W']
            self.b_slave = self.master_components['B']
            self.axi5_master = self.master_components['interface']

            self.log.info("AXI5 Master Write components created (driving slave interface)")
        except Exception as e:
            self.log.error(f"Failed to create master components: {e}")
            raise

        # Create AXI5 slave to respond on the FUB side
        try:
            self.slave_components = create_axi5_slave_wr(
                dut=dut,
                clock=self.aclk,
                prefix='fub_axi',
                log=self.log,
                id_width=self.TEST_ID_WIDTH,
                addr_width=self.TEST_ADDR_WIDTH,
                data_width=self.TEST_DATA_WIDTH,
                user_width=self.TEST_USER_WIDTH,
                atop_width=self.TEST_ATOP_WIDTH,
                nsaid_width=self.TEST_NSAID_WIDTH,
                mpam_width=self.TEST_MPAM_WIDTH,
                mecid_width=self.TEST_MECID_WIDTH,
                tag_width=self.TEST_TAG_WIDTH,
                tagop_width=self.TEST_TAGOP_WIDTH,
                memory_model=self.memory_model,
                multi_sig=self.use_multi_sig
            )

            # Access individual components
            self.aw_slave = self.slave_components['AW']
            self.w_slave = self.slave_components['W']
            self.b_master = self.slave_components['B']

            self.log.info("AXI5 Slave Write components created")
        except Exception as e:
            self.log.error(f"Failed to create slave components: {e}")
            raise

        # Compliance checker
        self.axi5_compliance_checker = AXI5ComplianceChecker.create_if_enabled(
            dut=dut,
            clock=self.aclk,
            prefix='s_axi',
            log=self.log,
            data_width=self.TEST_DATA_WIDTH,
            id_width=self.TEST_ID_WIDTH,
            addr_width=self.TEST_ADDR_WIDTH,
            user_width=self.TEST_USER_WIDTH
        )

        # Statistics tracking
        self.stats = {
            'total_writes': 0,
            'successful_writes': 0,
            'failed_writes': 0,
            'timeout_errors': 0,
            'response_errors': 0,
            'single_writes': 0,
            'burst_writes': 0,
            'axi5_feature_tests': 0,
            'atop_tests': 0,
            'nsaid_tests': 0,
            'trace_tests': 0,
            'mpam_tests': 0,
            'mecid_tests': 0,
            'tagop_tests': 0,
            'poison_tests': 0,
            'test_duration': 0
        }

        # Create randomizer configurations for different test profiles
        self.randomizer_configs = self._create_axi5_randomizer_configs()
        self.set_timing_profile('normal')

        self.log.info("AXI5 Write Slave testbench initialized successfully")

    def _initialize_memory_patterns(self):
        """Initialize memory with known test patterns"""
        self.log.info("Initializing memory with test patterns...")

        bytes_per_word = self.TEST_DATA_WIDTH // 8

        # Initialize memory with zeros
        base_addr = 0x4000
        for i in range(256):
            addr = base_addr + (i * bytes_per_word)
            data_bytes = self.memory_model.integer_to_bytearray(0, bytes_per_word)
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
        await self.aw_master.reset_bus()
        await self.w_master.reset_bus()
        await self.b_master.reset_bus()
        await self.wait_clocks(self.aclk_name, 5)
        self.log.info("Reset asserted")

    async def deassert_reset(self):
        """Deassert reset"""
        self.aresetn.value = 1
        await self.wait_clocks(self.aclk_name, 5)
        self.log.info(f"Reset deasserted{self.get_time_ns_str()}")

    # Core test methods

    async def single_write_test(self, addr, data, awid=None,
                                atop=None, nsaid=None, trace=None, mpam=None,
                                mecid=None, unique=None, tagop=None, tag=None,
                                poison=None):
        """
        Perform a single AXI5 write transaction with optional AXI5 features.

        Args:
            addr: Address to write to
            data: Data to write
            awid: Transaction ID (if None, auto-generated)
            atop: Atomic operation type (AXI5)
            nsaid: Non-secure Access ID (AXI5)
            trace: Trace signal (AXI5)
            mpam: Memory Partitioning and Monitoring (AXI5)
            mecid: Memory Encryption Context ID (AXI5)
            unique: Unique access (AXI5)
            tagop: Tag operation (AXI5 MTE)
            tag: Memory tag value (AXI5 MTE)
            poison: Poison indicator (AXI5)

        Returns:
            tuple: (success, response_info)
        """
        if awid is None:
            awid = random.randint(0, self.MAX_ID)

        # Track AXI5 features used
        axi5_features = {}
        if atop is not None and atop != 0:
            axi5_features['atop'] = atop
            self.stats['atop_tests'] += 1
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
        if poison is not None:
            axi5_features['poison'] = poison
            self.stats['poison_tests'] += 1

        if axi5_features:
            self.stats['axi5_feature_tests'] += 1

        self.log.debug(f"Single write: addr=0x{addr:08X}, data=0x{data:08X}, "
                      f"id={awid}, axi5={axi5_features}")

        try:
            self.stats['total_writes'] += 1
            self.stats['single_writes'] += 1

            # Build kwargs for AXI5 features
            write_kwargs = {
                'address': addr,
                'data': data,
                'id': awid,
                'size': self._calculate_awsize(),
                'burst_type': 1,  # INCR
            }

            # Add AXI5-specific parameters if provided
            if atop is not None:
                write_kwargs['atop'] = atop
            if nsaid is not None:
                write_kwargs['nsaid'] = nsaid
            if trace is not None:
                write_kwargs['trace'] = trace
            if mpam is not None:
                write_kwargs['mpam'] = mpam
            if mecid is not None:
                write_kwargs['mecid'] = mecid
            if unique is not None:
                write_kwargs['unique'] = unique
            if tagop is not None:
                write_kwargs['tagop'] = tagop
            if tag is not None:
                write_kwargs['tag'] = tag
            if poison is not None:
                write_kwargs['poison'] = poison

            response = await self.axi5_master.single_write(**write_kwargs)

            # Check response - single_write returns a dict with 'success' and 'response' fields
            resp_code = response.get('response', 0) if isinstance(response, dict) else response
            success = response.get('success', True) if isinstance(response, dict) else (response == 0)

            if not success or resp_code != 0:  # OKAY response is 0
                self.log.warning(f"Write response error at 0x{addr:08X}: resp={response}")
                self.stats['response_errors'] += 1
                self.stats['failed_writes'] += 1
                return False, {
                    'response': response,
                    'error': True,
                    'axi5_features': axi5_features
                }

            self.stats['successful_writes'] += 1
            return True, {
                'address': addr,
                'data': data,
                'id': awid,
                'response': response,
                'axi5_features': axi5_features
            }

        except Exception as e:
            self.log.error(f"Write failed with exception: {e}")
            self.stats['failed_writes'] += 1
            self.stats['timeout_errors'] += 1
            return False, {'error': str(e), 'axi5_features': axi5_features}

    async def burst_write_test(self, addr, data_list, **axi5_kwargs):
        """
        Perform a burst AXI5 write transaction with optional AXI5 features.

        Args:
            addr: Starting address
            data_list: List of data values to write
            **axi5_kwargs: AXI5-specific parameters (atop, nsaid, trace, etc.)

        Returns:
            tuple: (success, response_info)
        """
        awid = random.randint(0, self.MAX_ID)
        burst_len = len(data_list)
        self.log.debug(f"Burst write: addr=0x{addr:08X}, len={burst_len}, id={awid}")

        try:
            self.stats['total_writes'] += 1
            self.stats['burst_writes'] += 1

            if axi5_kwargs:
                self.stats['axi5_feature_tests'] += 1

            response = await self.axi5_master.write_transaction(
                address=addr,
                data=data_list,
                id=awid,
                size=self._calculate_awsize(),
                burst_type=1,  # INCR
                **axi5_kwargs
            )

            # Check response - write_transaction returns a dict with 'success' and 'response' fields
            resp_code = response.get('response', 0) if isinstance(response, dict) else response
            success = response.get('success', True) if isinstance(response, dict) else (response == 0)

            if not success or resp_code != 0:
                self.log.warning(f"Burst write response error: resp={response}")
                self.stats['response_errors'] += 1
                self.stats['failed_writes'] += 1
                return False, {'response': response, 'error': True}

            self.stats['successful_writes'] += 1
            return True, {
                'burst_len': burst_len,
                'id': awid,
                'response': response,
                'axi5_features': axi5_kwargs
            }

        except Exception as e:
            self.log.error(f"Burst write failed with exception: {e}")
            self.stats['failed_writes'] += 1
            self.stats['timeout_errors'] += 1
            return False, {'error': str(e)}

    def _calculate_awsize(self):
        """Calculate AWSIZE field based on data width"""
        bytes_per_beat = self.TEST_DATA_WIDTH // 8
        return bytes_per_beat.bit_length() - 1

    # High-level test sequences

    async def basic_write_sequence(self, count=10):
        """Run basic single write sequence"""
        self.log.info(f"Running basic write sequence ({count} writes)...")

        success_count = 0
        base_addr = 0x4000

        for i in range(count):
            addr = base_addr + (i * (self.TEST_DATA_WIDTH // 8))
            data = random.randint(0, self.MAX_DATA)
            success, info = await self.single_write_test(addr, data)
            if success:
                success_count += 1

            await self.wait_clocks(self.aclk_name, 2)

        self.log.info(f"Basic sequence result: {success_count}/{count} successful")
        return success_count == count

    async def burst_write_sequence(self, burst_lengths=[2, 4, 8, 16]):
        """Run burst write sequence with different lengths"""
        self.log.info(f"Running burst write sequence: {burst_lengths}")

        success_count = 0
        base_addr = 0x5000

        for i, burst_len in enumerate(burst_lengths):
            addr = base_addr + (i * burst_len * (self.TEST_DATA_WIDTH // 8))
            data_list = [random.randint(0, self.MAX_DATA) for _ in range(burst_len)]
            success, info = await self.burst_write_test(addr, data_list)
            if success:
                success_count += 1

            await self.wait_clocks(self.aclk_name, 5)

        self.log.info(f"Burst sequence result: {success_count}/{len(burst_lengths)} successful")
        return success_count == len(burst_lengths)

    async def axi5_feature_test_sequence(self, count=10):
        """Run AXI5-specific feature tests"""
        self.log.info(f"Running AXI5 feature test sequence ({count} writes)...")

        success_count = 0
        base_addr = 0x4000

        for i in range(count):
            addr = base_addr + (i * (self.TEST_DATA_WIDTH // 8))
            data = random.randint(0, self.MAX_DATA)

            # Randomize AXI5 features
            nsaid = random.randint(0, self.MAX_NSAID)
            trace = random.randint(0, 1)
            mpam = random.randint(0, self.MAX_MPAM) if random.random() > 0.5 else None
            mecid = random.randint(0, self.MAX_MECID) if random.random() > 0.5 else None
            tagop = random.randint(0, 3) if random.random() > 0.5 else None
            poison = random.randint(0, 1) if random.random() > 0.8 else None

            success, info = await self.single_write_test(
                addr, data,
                nsaid=nsaid,
                trace=trace,
                mpam=mpam,
                mecid=mecid,
                tagop=tagop,
                poison=poison
            )
            if success:
                success_count += 1

            await self.wait_clocks(self.aclk_name, 3)

        self.log.info(f"AXI5 feature sequence result: {success_count}/{count} successful")
        return success_count == count

    async def atomic_operation_test(self, count=10):
        """Test AXI5 atomic operations"""
        self.log.info(f"Running atomic operation test ({count} operations)...")

        self.set_timing_profile('atomic')

        success_count = 0
        base_addr = 0x6000

        # ATOP encodings (6-bit field)
        # [5:4]: 00=Store, 01=Load, 10=Swap, 11=Compare
        # [3:0]: Operation-specific
        atomic_ops = [
            0b010000,  # AtomicLoad (ADD)
            0b010001,  # AtomicLoad (CLR)
            0b010010,  # AtomicLoad (EOR)
            0b010011,  # AtomicLoad (SET)
            0b100000,  # AtomicSwap
        ]

        for i in range(count):
            addr = base_addr + (i * (self.TEST_DATA_WIDTH // 8))
            data = random.randint(0, self.MAX_DATA)
            atop = random.choice(atomic_ops)

            success, info = await self.single_write_test(addr, data, atop=atop)
            if success:
                success_count += 1
            else:
                self.log.warning(f"Atomic op 0x{atop:02X} at 0x{addr:08X} failed: {info}")

            await self.wait_clocks(self.aclk_name, 5)

        self.log.info(f"Atomic test result: {success_count}/{count} successful")
        return success_count >= (count * 0.9)

    async def stress_write_test(self, count=50):
        """Run stress test with rapid writes"""
        self.log.info(f"Running stress write test ({count} writes)...")

        self.set_timing_profile('stress')

        success_count = 0
        for i in range(count):
            base_addr = 0x4000 + (random.randint(0, 255) * (self.TEST_DATA_WIDTH // 8))
            data = random.randint(0, self.MAX_DATA)

            success, info = await self.single_write_test(base_addr, data)
            if success:
                success_count += 1

        self.log.info(f"Stress test result: {success_count}/{count} successful")
        return success_count >= (count * 0.95)

    def get_test_stats(self):
        """Get comprehensive test statistics"""
        total_tests = self.stats['total_writes']
        success_rate = (self.stats['successful_writes'] / total_tests * 100) if total_tests > 0 else 0

        self.finalize_test()

        return {
            'summary': {
                'total_writes': total_tests,
                'successful_writes': self.stats['successful_writes'],
                'success_rate': f"{success_rate:.1f}%"
            },
            'details': self.stats.copy(),
            'axi5_features': {
                'total_axi5_tests': self.stats['axi5_feature_tests'],
                'atop_tests': self.stats['atop_tests'],
                'nsaid_tests': self.stats['nsaid_tests'],
                'trace_tests': self.stats['trace_tests'],
                'mpam_tests': self.stats['mpam_tests'],
                'mecid_tests': self.stats['mecid_tests'],
                'tagop_tests': self.stats['tagop_tests'],
                'poison_tests': self.stats['poison_tests'],
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
