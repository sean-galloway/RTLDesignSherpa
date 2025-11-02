# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: Axi2ApbTB
# Purpose: Apply AXI4 timing profile from axi4_timing_config
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

import os
import itertools
import logging
import random

import pytest
import cocotb
import cocotb.triggers
from cocotb_test.simulator import run
from cocotb.clock import Clock

from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.apb.apb_packet import APBTransaction
from CocoTBFramework.components.apb.apb_factories import \
    create_apb_slave, create_apb_monitor

# Use project's AXI4 components
from CocoTBFramework.components.axi4.axi4_factories import create_axi4_master_wr, create_axi4_master_rd
from CocoTBFramework.components.shared.memory_model import MemoryModel

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


class Axi2ApbTB(TBBase):
    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.log = self.configure_logging(level=logging.DEBUG)
        self.log.info('Starting Axi2ApbTB')

        # Get test parameters
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_AXI_DATA_WIDTH', '32'))
        self.APB_ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_APB_ADDR_WIDTH', '12'))
        self.APB_DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_APB_DATA_WIDTH', '8'))
        self.strb_bits = self.DATA_WIDTH // 8
        self.APB_STRB_WIDTH = self.APB_DATA_WIDTH // 8

        self.log.info(f"Configuration: AXI_DATA_WIDTH={self.DATA_WIDTH}, APB_ADDR_WIDTH={self.APB_ADDR_WIDTH}, APB_DATA_WIDTH={self.APB_DATA_WIDTH}")

        self.debug = True

        # Create memory model
        self.memory_model = MemoryModel(
            num_lines=65536,
            bytes_per_line=max(4, self.DATA_WIDTH // 8),
            log=self.log,
            debug=self.debug
        )

        # Create AXI4 master components
        self.log.info("Creating AXI4 Master Write interface...")
        self.axi_write_components = create_axi4_master_wr(
            dut=dut,
            clock=dut.aclk,
            prefix='s_axi',
            log=self.log,
            id_width=8,
            addr_width=32,
            data_width=self.DATA_WIDTH,
            user_width=1,
            memory_model=self.memory_model,
            multi_sig=True,
            timeout_cycles=1000
        )

        self.log.info("Creating AXI4 Master Read interface...")
        self.axi_read_components = create_axi4_master_rd(
            dut=dut,
            clock=dut.aclk,
            prefix='s_axi',
            log=self.log,
            id_width=8,
            addr_width=32,
            data_width=self.DATA_WIDTH,
            user_width=1,
            memory_model=self.memory_model,
            multi_sig=True,
            timeout_cycles=1000
        )

        # Access interfaces
        self.axi_write_interface = self.axi_write_components['interface']
        self.axi_read_interface = self.axi_read_components['interface']

        # Access individual channels
        self.aw_master = self.axi_write_components['AW']
        self.w_master = self.axi_write_components['W']
        self.b_slave = self.axi_write_components['B']

        self.ar_master = self.axi_read_components['AR']
        self.r_slave = self.axi_read_components['R']

        self.registers = 32 * self.strb_bits

        # Create APB components
        self.apb_slave_randomizer = FlexRandomizer({
            'ready': ([(0, 0), (1, 5), (6, 10)], [5, 3, 1]),
            'error': ([(0, 0), (1, 1)], [10, 0])
        })

        self.apb_monitor = create_apb_monitor(
            dut, 'APB Monitor', 'm_apb', dut.pclk,
            addr_width=self.APB_ADDR_WIDTH,
            data_width=self.APB_DATA_WIDTH,
            log=self.log
        )

        self.apb_slave = create_apb_slave(
            dut, 'APB Slave', 'm_apb', dut.pclk,
            registers=[0] * (self.registers * self.APB_STRB_WIDTH),
            addr_width=self.APB_ADDR_WIDTH,
            data_width=self.APB_DATA_WIDTH,
            randomizer=self.apb_slave_randomizer,
            log=self.log
        )

        self.main_loop_count = 0
        self.test_failures = []
        self.log.info("Axi2ApbTB Init Done.")

    def apply_timing_profile(self, profile_name='axi4_normal'):
        """Apply AXI4 timing profile from axi4_timing_config"""
        try:
            from CocoTBFramework.components.axi4.axi4_timing_config import create_axi4_timing_from_profile
            timing_config = create_axi4_timing_from_profile(profile_name)

            self.log.info(f"Applied timing profile: {profile_name}")

            # Apply timing if randomizer is available
            randomizer = timing_config.get('randomizer')
            if randomizer:
                if hasattr(self.aw_master, 'set_randomizer'):
                    self.aw_master.set_randomizer(randomizer)
                if hasattr(self.w_master, 'set_randomizer'):
                    self.w_master.set_randomizer(randomizer)
                if hasattr(self.ar_master, 'set_randomizer'):
                    self.ar_master.set_randomizer(randomizer)
                if hasattr(self.b_slave, 'set_randomizer'):
                    self.b_slave.set_randomizer(randomizer)
                if hasattr(self.r_slave, 'set_randomizer'):
                    self.r_slave.set_randomizer(randomizer)

            return True
        except Exception as e:
            self.log.warning(f"Could not apply timing profile {profile_name}: {e}")
            return False

    async def cycle_reset(self):
        self.log.info("Reset Start")
        self.dut.aresetn.value = 0
        self.dut.presetn.value = 0

        await self.apb_slave.reset_bus()

        # Reset AXI4 components
        if hasattr(self.aw_master, 'reset_bus'):
            await self.aw_master.reset_bus()
        if hasattr(self.w_master, 'reset_bus'):
            await self.w_master.reset_bus()
        if hasattr(self.ar_master, 'reset_bus'):
            await self.ar_master.reset_bus()
        if hasattr(self.b_slave, 'reset_bus'):
            await self.b_slave.reset_bus()
        if hasattr(self.r_slave, 'reset_bus'):
            await self.r_slave.reset_bus()

        await self.wait_clocks('pclk', 5)
        self.dut.aresetn.value = 1
        self.dut.presetn.value = 1
        await self.wait_clocks('pclk', 5)
        self.log.info("Reset Done.")

    async def axi_write(self, addr, data_bytes, size=None):
        """Perform AXI4 write using project framework"""
        try:
            if isinstance(data_bytes, (list, bytearray)):
                data_list = list(data_bytes)
            else:
                data_list = [data_bytes]

            self.log.debug(f"AXI Write: addr=0x{addr:08X}, data_len={len(data_list)}")

            bytes_per_word = self.DATA_WIDTH // 8  # e.g., 32-bit = 4 bytes

            if len(data_list) <= bytes_per_word:
                # Single AXI word - pack bytes into word (little-endian)
                data_word = 0
                for i, byte_val in enumerate(data_list):
                    data_word |= (byte_val << (i * 8))

                # Calculate proper size field for AXI
                # size = log2(number of bytes being transferred)
                actual_bytes = len(data_list)
                size_field = (actual_bytes - 1).bit_length() - 1 if actual_bytes > 1 else 0

                self.log.debug(f"Single word write: data=0x{data_word:08X}, size={size_field}, bytes={actual_bytes}")

                result = await self.axi_write_interface.single_write(
                    address=addr,
                    data=data_word,
                    id=0,
                    size=size_field,  # Use calculated size
                    burst_type=1
                )

                success = result.get('success', False)
                if not success:
                    self.log.error(f"AXI single write failed: {result}")
                    return False

                return True
            else:
                # True multi-word writes (bursts) - implement if needed
                self.log.error(f"Multi-word writes not implemented: {len(data_list)} bytes > {bytes_per_word} bytes per word")
                return False

        except Exception as e:
            self.log.error(f"AXI write failed with exception: {e}")
            return False

    async def axi_read(self, addr, length, size=None):
        """Perform AXI4 read using project framework"""
        try:
            self.log.debug(f"AXI Read: addr=0x{addr:08X}, length={length}")

            bytes_per_word = self.DATA_WIDTH // 8

            if length <= bytes_per_word:
                data_word = await self.axi_read_interface.single_read(
                    address=addr,
                    id=0,
                    size=min(3, (length - 1).bit_length()),
                    burst_type=1
                )

                # Convert word data back to bytes
                data_bytes = bytearray()
                for i in range(length):
                    data_bytes.append((data_word >> (i * 8)) & 0xFF)

                class ReadResponse:
                    def __init__(self, data):
                        self.data = data

                return ReadResponse(data_bytes)
            else:
                self.log.error("Multi-word reads not implemented yet")
                raise Exception("Multi-word reads not implemented")

        except Exception as e:
            self.log.error(f"AXI read failed with exception: {e}")
            raise

    async def single_write_read_test(self, addr, test_data, test_name, quick_mode=False):
        """Perform a single write-read-verify cycle"""
        if not quick_mode:
            self.log.debug(f"Test {test_name}: addr=0x{addr:08X}, data={[f'{x:02X}' for x in test_data]}")

        try:
            # Write
            write_success = await self.axi_write(addr, test_data)
            if not write_success:
                raise Exception(f"Write failed for {test_name} at 0x{addr:08X}")

            # Read back
            read_response = await self.axi_read(addr, len(test_data))

            # Verify
            if read_response.data != test_data:
                raise Exception(f"Data mismatch for {test_name}: expected {test_data}, got {read_response.data}")

            if not quick_mode:
                self.log.debug(f"Test {test_name}: PASSED")

        except Exception as e:
            error_msg = f"{test_name} failed: {e}"
            self.log.error(f"Test error: {error_msg}")
            self.test_failures.append(error_msg)
            raise

    async def run_comprehensive_write_read_test(self, timing_profile='axi4_normal'):
        """Run comprehensive write/read tests"""
        self.log.info(f'Running comprehensive test with timing profile: {timing_profile}')

        test_count = 0

        # Test 1: Single byte patterns
        self.log.info("Test 1: Single byte patterns")
        for addr in range(0, 64, 4):
            test_data = bytearray([addr & 0xFF])
            await self.single_write_read_test(addr, test_data, f"single_byte_{addr}")
            test_count += 1
            await self.wait_clocks('aclk', 5)

        # Test 2: Multi-byte patterns
        self.log.info("Test 2: Multi-byte patterns")
        for addr in range(0x100, 0x200, 8):
            test_data = bytearray([(addr + i) & 0xFF for i in range(4)])
            await self.single_write_read_test(addr, test_data, f"multi_byte_{addr}")
            test_count += 1
            await self.wait_clocks('aclk', 3)

        # Test 3: Data patterns
        self.log.info("Test 3: Data patterns")
        patterns = [
            ([0x00], "zeros"),
            ([0xFF], "ones"),
            ([0xAA], "alternating_1"),
            ([0x55], "alternating_2"),
            ([0x00, 0x01, 0x02, 0x03], "incremental"),
            ([0xFF, 0xFE, 0xFD, 0xFC], "decremental"),
            ([0xDE, 0xAD, 0xBE, 0xEF], "deadbeef"),
            ([0xCA, 0xFE, 0xBA, 0xBE], "cafebabe")
        ]

        base_addr = 0x300
        for i, (pattern, name) in enumerate(patterns):
            addr = base_addr + (i * 8)
            test_data = bytearray(pattern)
            await self.single_write_read_test(addr, test_data, f"pattern_{name}")
            test_count += 1
            await self.wait_clocks('aclk', 2)

        # Test 4: Rapid sequential access
        self.log.info("Test 4: Rapid sequential access")
        base_addr = 0x400
        for i in range(32):
            addr = base_addr + i
            test_data = bytearray([0x80 + i])
            await self.single_write_read_test(addr, test_data, f"rapid_{i}", quick_mode=True)
            test_count += 1
            await self.wait_clocks('aclk', 1)

        # Test 5: Bulk operations
        self.log.info("Test 5: Bulk write then bulk read")
        base_addr = 0x500
        write_data = {}

        # Bulk writes
        for i in range(16):
            addr = base_addr + (i * 4)
            data = bytearray([0xA0 + i, 0xB0 + i, 0xC0 + i, 0xD0 + i])
            write_data[addr] = data

            write_success = await self.axi_write(addr, data)
            if not write_success:
                raise Exception(f"Bulk write failed at address 0x{addr:08X}")

            await self.wait_clocks('aclk', 2)

        # Bulk reads and verify
        for addr, expected_data in write_data.items():
            read_response = await self.axi_read(addr, len(expected_data))
            if read_response.data != expected_data:
                raise Exception(f"Bulk read verification failed at 0x{addr:08X}")

            test_count += 1
            await self.wait_clocks('aclk', 2)

        # Test 6: Random address order
        self.log.info("Test 6: Random address order")
        addresses = list(range(0x600, 0x700, 8))
        random.shuffle(addresses)

        for addr in addresses[:16]:
            test_data = bytearray([random.randint(0, 255) for _ in range(2)])
            await self.single_write_read_test(addr, test_data, f"random_{addr:03X}", quick_mode=True)
            test_count += 1
            await self.wait_clocks('aclk', 1)

        self.log.info(f"Comprehensive test completed: {test_count} total operations")
        return test_count

    async def run_stress_test(self):
        """Run high-intensity stress testing"""
        self.log.info("Starting stress test - rapid fire operations")

        operations = 0
        base_addr = 0x1000

        # Rapid single-byte operations
        for i in range(64):
            addr = base_addr + i
            data = bytearray([i & 0xFF])
            await self.single_write_read_test(addr, data, f"stress_{i}", quick_mode=True)
            operations += 1

        # Rapid multi-byte operations
        for i in range(32):
            addr = base_addr + 0x100 + (i * 4)
            data = bytearray([i, i+1, i+2, i+3])
            await self.single_write_read_test(addr, data, f"stress_multi_{i}", quick_mode=True)
            operations += 1

        # Mixed pattern stress
        patterns = [
            [0x00], [0xFF], [0xAA], [0x55],
            [0xDE, 0xAD], [0xBE, 0xEF],
            [0xCA, 0xFE, 0xBA, 0xBE]
        ]

        for i in range(48):
            addr = base_addr + 0x200 + i
            pattern = random.choice(patterns)
            data = bytearray(pattern)
            await self.single_write_read_test(addr, data, f"stress_mixed_{i}", quick_mode=True)
            operations += 1

        self.log.info(f"Stress test completed: {operations} operations")
        return operations

    async def main_loop(self):
        """Main test loop with comprehensive testing"""
        self.main_loop_count += 1
        self.log.info(f"main_loop called {self.main_loop_count} times")

        # Configure APB slave
        apb_slv_constraints = {
            'ready': ([(0, 0), (1, 1)], [9, 1]),
            'error': ([(0, 0), (1, 1)], [10, 0]),
        }
        self.apb_slave.set_randomizer(FlexRandomizer(apb_slv_constraints))

        # Test with different timing profiles
        timing_profiles_to_test = [
            'axi4_backtoback',
            'axi4_normal',
            'axi4_fast',
            'axi4_slow',
        ]

        total_operations = 0

        for profile in timing_profiles_to_test:
            try:
                self.log.info(f"Testing with AXI4 timing profile: {profile}")

                self.apply_timing_profile(profile)
                await self.wait_clocks('aclk', 10)

                operations = await self.run_comprehensive_write_read_test(profile)
                total_operations += operations

                self.log.info(f"Completed {operations} operations with profile {profile}")
                await self.wait_clocks('aclk', 50)

            except Exception as e:
                error_msg = f"Profile {profile} failed: {e}"
                self.log.error(f"Profile error: {error_msg}")
                self.test_failures.append(error_msg)

        # Stress test
        try:
            self.log.info("Running stress test")
            self.apply_timing_profile('axi4_backtoback')
            await self.wait_clocks('aclk', 10)

            stress_operations = await self.run_stress_test()
            total_operations += stress_operations

            self.log.info(f"Stress test completed: {stress_operations} operations")

        except Exception as e:
            error_msg = f"Stress test failed: {e}"
            self.log.error(f"Stress error: {error_msg}")
            self.test_failures.append(error_msg)

        self.log.info(f"TOTAL OPERATIONS COMPLETED: {total_operations}")

        if self.test_failures:
            failure_summary = f"Test failures detected: {len(self.test_failures)} failures"
            self.log.error(f"Failure summary: {failure_summary}")
            for i, failure in enumerate(self.test_failures):
                self.log.error(f"Failure {i+1}: {failure}")
            raise Exception(f"{failure_summary}: {self.test_failures[0]}")


@cocotb.test(timeout_time=500, timeout_unit="ms")
async def axi2apb_shim_test(dut):
    """Main test function"""
    tb = Axi2ApbTB(dut)
    cocotb.start_soon(Clock(dut.aclk, 1, units="ns").start())
    cocotb.start_soon(Clock(dut.pclk, 10, units="ns").start())

    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)

    try:
        await tb.cycle_reset()
        await tb.wait_clocks('aclk', 10)

        await tb.main_loop()

        await tb.wait_clocks('aclk', 10)
        tb.done = True
        tb.log.info("All tests completed successfully.")

    except Exception as e:
        tb.log.error(f"Test FAILED with exception: {e}")
        tb.done = True
        raise


@pytest.mark.parametrize("id_width, addr_width, data_width, user_width, apb_addr_width, apb_data_width",
                            [(8,32,32,1,12,8)])
def test_axi2abp_shim(request, id_width, addr_width, data_width, user_width, apb_addr_width, apb_data_width):

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn':  'rtl/common',
        'rtl_amba': 'rtl/amba',
        'rtl_amba_includes': 'rtl/amba/includes',
        'rtl_converters': 'projects/components/converters/rtl',
    })

    dut_name = "axi4_to_apb_shim"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_amba'], "shared/cdc_handshake.sv"),
        os.path.join(rtl_dict['rtl_amba'], "gaxi/gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_amba'], "apb/apb_master.sv"),
        os.path.join(rtl_dict['rtl_amba'], "apb/apb_master_stub.sv"),
        os.path.join(rtl_dict['rtl_cmn'],  "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'],  "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_amba'], "gaxi/gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_amba'], "shared/axi_gen_addr.sv"),
        os.path.join(rtl_dict['rtl_converters'], "axi4_to_apb_convert.sv"),
        os.path.join(rtl_dict['rtl_amba'], "axi4/stubs/axi4_slave_wr_stub.sv"),
        os.path.join(rtl_dict['rtl_amba'], "axi4/stubs/axi4_slave_rd_stub.sv"),
        os.path.join(rtl_dict['rtl_amba'], "axi4/stubs/axi4_slave_stub.sv"),
        os.path.join(rtl_dict['rtl_converters'], f"{dut_name}.sv")
    ]

    aw_str = TBBase.format_dec(addr_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    uw_str = TBBase.format_dec(user_width, 3)
    aaw_str = TBBase.format_dec(apb_addr_width, 3)
    adw_str = TBBase.format_dec(apb_data_width, 3)
    test_name_plus_params = f"test_{dut_name}_aw{aw_str}_dw{dw_str}_uw{uw_str}_aaw{aaw_str}_adw{adw_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {
        'AXI_ID_WIDTH': str(id_width),
        'AXI_ADDR_WIDTH': str(addr_width),
        'AXI_DATA_WIDTH': str(data_width),
        'AXI_USER_WIDTH': str(user_width),
        'APB_ADDR_WIDTH': str(apb_addr_width),
        'APB_DATA_WIDTH': str(apb_data_width),
    }

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'DEBUG',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(0x434749)
    }

    extra_env.update({f'TEST_{k}': str(v) for k, v in rtl_parameters.items()})

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = ["--trace", "--trace-structs", "--trace-depth", "99"]
    sim_args = ["--trace", "--trace-structs", "--trace-depth", "99"]
    plusargs = ["--trace"]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=[rtl_dict['rtl_amba_includes']],
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
    except Exception as e:
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise
