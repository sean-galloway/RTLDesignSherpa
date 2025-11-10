# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: SimpleLFSRTB
# Purpose: Get a prime number for the given bit width from lookup table
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

import os
import sys
import random
import pytest
import cocotb
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

# Prime lookup table for different bit widths
prime_lookup = {
    8: 251,        # Largest prime < 2^8
    12: 4093,      # Largest prime < 2^12
    16: 65521,     # Largest prime < 2^16
    24: 16777213,  # Large prime < 2^24
    32: 4294967291,  # Largest prime < 2^32
    48: 281474976710597,  # Large prime < 2^48
    64: 18446744073709551557,  # Largest prime < 2^64
    96: 79228162514264337593543950319,  # Large prime < 2^96
    128: 340282366920938463463374607431768211297,  # Largest prime < 2^128
    256: 115792089237316195423570985008687907853269984665640564039457584007913129639747,  # Large prime < 2^256
    512: 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084095  # Large prime < 2^512
}

def find_prime_for_width(width):
    """Get a prime number for the given bit width from lookup table"""
    if width in prime_lookup:
        return prime_lookup[width]
    else:
        # Fallback for unsupported widths - use a smaller width's prime
        for w in sorted(prime_lookup.keys()):
            if w < width:
                return prime_lookup[w]
        return 251  # Ultimate fallback

# LFSR parameters from the PDF table - using 4-tap configurations
lfsr_params = {
    8: {'taps': [8, 6, 5, 4], 'seed': find_prime_for_width(8)},
    16: {'taps': [16, 15, 13, 4], 'seed': find_prime_for_width(16)},
    32: {'taps': [32, 30, 26, 25], 'seed': find_prime_for_width(32)},
    64: {'taps': [64, 63, 61, 60], 'seed': find_prime_for_width(64)},
    96: {'taps': [96, 94, 49, 47], 'seed': find_prime_for_width(96)},
    128: {'taps': [128, 126, 101, 99], 'seed': find_prime_for_width(128)},
    # Add more as needed from the PDF
    12: {'taps': [12, 11, 8, 6], 'seed': find_prime_for_width(12)},
    24: {'taps': [24, 23, 21, 20], 'seed': find_prime_for_width(24)},
    48: {'taps': [48, 44, 41, 39], 'seed': find_prime_for_width(48)},
    256: {'taps': [256, 254, 251, 246], 'seed': find_prime_for_width(256)},
    512: {'taps': [512, 510, 507, 504], 'seed': find_prime_for_width(512)},
}

class SimpleLFSRTB(TBBase):
    """Simplified testbench for LFSR value generation"""

    def __init__(self, dut):
        super().__init__(dut)
        
        # Get test parameters
        self.WIDTH = self.convert_to_int(os.environ.get('TEST_WIDTH', '8'))
        self.COUNT = self.convert_to_int(os.environ.get('TEST_COUNT', '100'))
        
        # Get LFSR configuration
        if self.WIDTH in lfsr_params:
            self.config = lfsr_params[self.WIDTH]
        else:
            # Fallback for unsupported widths
            self.config = {
                'taps': [self.WIDTH, self.WIDTH-1, self.WIDTH//2, 1],
                'seed': find_prime_for_width(self.WIDTH)
            }
        
        # DUT signals
        self.clk = self.dut.clk
        self.rst_n = self.dut.rst_n
        self.enable = self.dut.enable
        self.seed_load = self.dut.seed_load
        self.seed_data = self.dut.seed_data
        self.taps = self.dut.taps
        self.lfsr_out = self.dut.lfsr_out
        
        self.log.info(f"LFSR Width: {self.WIDTH}")
        self.log.info(f"Count: {self.COUNT}")
        self.log.info(f"Taps: {self.config['taps']}")
        self.log.info(f"Seed: 0x{self.config['seed']:x}")

    async def reset_dut(self):
        """Reset the DUT"""
        self.enable.value = 0
        self.seed_load.value = 0
        self.seed_data.value = 0
        
        # Set taps from configuration
        self.set_taps(self.config['taps'])
        
        # Apply reset
        self.rst_n.value = 0
        await self.wait_clocks('clk', 5)
        self.rst_n.value = 1
        await self.wait_clocks('clk', 5)

    def set_taps(self, tap_values):
        """Set the tap values for the LFSR"""
        TAP_COUNT = 4
        TAP_INDEX_WIDTH = 12
        
        # Ensure we have exactly 4 taps
        taps = tap_values[:TAP_COUNT]
        taps += [0] * (TAP_COUNT - len(taps))
        
        # Concatenate tap positions
        tap_value = 0
        for i, tap in enumerate(taps):
            tap_value |= (tap & ((1 << TAP_INDEX_WIDTH) - 1)) << (i * TAP_INDEX_WIDTH)
        
        self.taps.value = tap_value
        self.log.info(f"Set taps to: {taps}")

    async def load_seed(self, seed_value):
        """Load seed into LFSR"""
        self.seed_load.value = 1
        self.seed_data.value = seed_value
        self.enable.value = 1
        
        await self.wait_clocks('clk', 1)
        self.seed_load.value = 0
        await self.wait_clocks('clk', 1)

    async def generate_values(self):
        """Generate LFSR values and save to file"""
        # Reset and initialize
        await self.reset_dut()
        await self.load_seed(self.config['seed'])
        
        # Generate values
        values = []
        self.enable.value = 1
        
        for i in range(self.COUNT):
            await self.wait_clocks('clk', 1)
            value = int(self.lfsr_out.value)
            values.append(value)
            
            if i < 10:  # Log first 10 values
                self.log.info(f"Cycle {i}: 0x{value:x}")
        
        # Save to file
        with open('output.txt', 'w') as f:
            f.write(f"Width: {self.WIDTH}, Count: {self.COUNT}\n")
            for value in values:
                f.write(f"0x{value:x}\n")
        
        self.log.info(f"Generated {len(values)} values and saved to output.txt")
        return values

@cocotb.test(timeout_time=10000, timeout_unit="us")
async def simple_generate_test(dut):
    """Simple test to generate LFSR values"""
    tb = SimpleLFSRTB(dut)
    
    # Start clock
    await tb.start_clock('clk', 10, 'ns')
    
    # Generate values
    values = await tb.generate_values()
    
    # Simple assertion to ensure we got the right count
    expected_count = tb.COUNT
    assert len(values) == expected_count, f"Expected {expected_count} values, got {len(values)}"

def generate_test_params():
    """
    Generate test parameters based on REG_LEVEL.

    REG_LEVEL=GATE: 2 tests (8, 16-bit)
    REG_LEVEL=FUNC: 4 tests (8, 16, 32, 64-bit) - default
    REG_LEVEL=FULL: 7 tests (all widths up to 512-bit)

    Returns:
        List of dicts with WIDTH, COUNT
    """
    import os
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        return [
            {'WIDTH': 8, 'COUNT': 100},
            {'WIDTH': 16, 'COUNT': 100},
        ]
    elif reg_level == 'FUNC':
        return [
            {'WIDTH': 8, 'COUNT': 100},
            {'WIDTH': 16, 'COUNT': 100},
            {'WIDTH': 32, 'COUNT': 50},
            {'WIDTH': 64, 'COUNT': 50},
        ]
    else:  # FULL
        return [
            {'WIDTH': 8, 'COUNT': 100},
            {'WIDTH': 16, 'COUNT': 100},
            {'WIDTH': 32, 'COUNT': 50},
            {'WIDTH': 64, 'COUNT': 50},
            {'WIDTH': 128, 'COUNT': 25},
            {'WIDTH': 256, 'COUNT': 25},
            {'WIDTH': 512, 'COUNT': 10},
        ]

@pytest.mark.parametrize("params", generate_test_params())
def test_simple_lfsr_generate(request, params):
    """Parameterized test for different LFSR widths"""
    # Get paths
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})
    
    dut_name = "shifter_lfsr_galois"
    toplevel = dut_name
    
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/shifter_lfsr_galois.f'
    )
    
    # Test name
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name = f"simple_lfsr_W{params['WIDTH']}_C{params['COUNT']}_{reg_level}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name = f"{test_name}_{worker_id}"

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    log_path = os.path.join(log_dir, f'{test_name}.log')
    
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    
    # Module parameters - fixed for 4-tap configuration
    parameters = {
        'WIDTH': params['WIDTH'],
        'TAP_INDEX_WIDTH': 12,
        'TAP_COUNT': 4
    }
    
    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'TEST_WIDTH': str(params['WIDTH']),
        'TEST_COUNT': str(params['COUNT'])
    }
    
    compile_args = ["--trace", "--trace-structs", "--trace-depth", "99"]
    sim_args = ["--trace", "--trace-structs", "--trace-depth", "99"]
    plusargs = ["+trace"]
    
    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            toplevel=toplevel,
            module=module,
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
            includes=includes,  # From filelist via get_sources_from_filelist()
        )
    except Exception as e:
        print(f"Test failed: {str(e)}")
        print(f"Logs at: {log_path}")
        raise
