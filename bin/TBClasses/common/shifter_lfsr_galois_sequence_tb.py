# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: SimpleLFSRTB
# Purpose: Testbench for shifter_lfsr_galois_sequence
# Subsystem: framework
#
# Extracted from val/common/test_shifter_lfsr_galois_sequence.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
from TBClasses.shared.tbbase import TBBase


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
        self.COUNT = self.convert_to_int(
            os.environ.get('TEST_COUNT', str(50 * {'gate': 1, 'func': 2, 'full': 5}[
                os.environ.get('TEST_LEVEL', 'gate').lower()
                if os.environ.get('TEST_LEVEL', 'gate').lower() in ('gate', 'func', 'full')
                else 'gate'])))

        # Per-test depth. REG_LEVEL picks how many parameter combinations run;
        # TEST_LEVEL decides how hard each one works. This test had no depth
        # mechanism, so `full` cost exactly what `gate` did.
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        if self.TEST_LEVEL not in ('gate', 'func', 'full'):
            self.TEST_LEVEL = 'gate'
        self.LEVEL_MULT = {'gate': 1, 'func': 2, 'full': 5}[self.TEST_LEVEL]

        
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

    # ---- contract lifecycle (/GLOBAL_REQUIREMENTS.md 2.2) ----------------
    # Mandatory on every TB. This class inherited TBBase's stubs, which
    # only log "should be overridden" and drive nothing -- nominally
    # compliant, functionally absent. Wraps the reset path this TB
    # already used, so behaviour is unchanged.

    async def assert_reset(self):
        """Assert reset."""
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        """Release reset."""
        self.dut.rst_n.value = 1

    async def setup_clocks_and_reset(self):
        """Start the clock and drive the full reset sequence."""
        await self.start_clock('clk', 10, 'ns')
        await self.reset_dut()

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

    def reference_values(self, count):
        """Software Galois LFSR mirroring rtl/common/shifter_lfsr_galois.sv.

        Right shift, and when the shifted-out LSB is 1, XOR a 1 into each tap
        position of the shifted value. Mirrors the same convention as
        ShifterLFSRGaloisTB.simulate_galois_lfsr: advance twice before the
        first value the RTL presents, because the load consumes a cycle.
        """
        mask = (1 << self.WIDTH) - 1
        lfsr = self.config['seed'] & mask
        if lfsr == 0:
            lfsr = mask
        valid_taps = [t for t in self.config['taps'] if 0 < t <= self.WIDTH]
        out = []
        for _ in range(count + 2):
            lsb = lfsr & 1
            nxt = lfsr >> 1
            if lsb:
                for tap in valid_taps:
                    nxt ^= (1 << (tap - 1))
            lfsr = nxt & mask
            out.append(lfsr)
        return out[1:count + 1]
