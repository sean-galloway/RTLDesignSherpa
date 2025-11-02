# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_dataint_ecc_hamming_secded
# Purpose: Test runner for dataint_ecc_hamming_secded modules (encoder + decoder pair)
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Test runner for dataint_ecc_hamming_secded modules (encoder + decoder pair)

The Hamming SECDED (Single Error Correction, Double Error Detection) provides
data integrity for memory and communication systems.

Test Configurations:
- width=4: Minimal configuration for verification
- width=8: Typical byte-width configuration
- width=16: Word-width configuration
- width=32: Double-word configuration
- width=64: Quad-word configuration

Each test verifies:
- Encode/decode round-trip with no errors
- Single-bit error correction at all bit positions
- Double-bit error detection
- Multiple data patterns

Author: RTL Design Sherpa Project
"""

import os
import sys
import pytest
import cocotb
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))
if os.path.join(repo_root, 'bin') not in sys.path:
    sys.path.insert(0, os.path.join(repo_root, 'bin'))

from CocoTBFramework.tbclasses.dataint_ecc_hamming_secded_tb import DataintEccHammingSecDedTB
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.tbbase import TBBase


# ===========================================================================
# COCOTB TEST FUNCTIONS - prefix with "cocotb_" to prevent pytest collection
# ===========================================================================

@cocotb.test(timeout_time=500, timeout_unit="us")
async def cocotb_ecc_secded_test(dut):
    """Main ECC SECDED encoder/decoder test function"""
    tb = DataintEccHammingSecDedTB(dut)
    await tb.setup_clocks_and_reset()
    passed = await tb.run_all_tests()
    assert passed, "ECC SECDED test failed"


# ===========================================================================
# PARAMETER GENERATION
# ===========================================================================

def generate_test_params():
    """
    Generate test parameter combinations based on REG_LEVEL.

    REG_LEVEL=GATE: 2 tests (4, 8-bit)
    REG_LEVEL=FUNC: 5 tests (all widths) - default
    REG_LEVEL=FULL: 5 tests (same as FUNC)

    Returns:
        List of tuples: (width, test_mode)
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    all_configs = [
        (4, 'minimal'),      # Minimal width for quick verification
        (8, 'byte'),         # Byte-width (common)
        (16, 'word'),        # Word-width
        (32, 'dword'),       # Double-word
        (64, 'qword'),       # Quad-word
    ]

    if reg_level == 'GATE':
        return [all_configs[0], all_configs[1]]  # 4, 8-bit
    else:  # FUNC or FULL (same for this test)
        return all_configs


# ===========================================================================
# PYTEST WRAPPER FUNCTIONS
# ===========================================================================

@pytest.mark.parametrize("width, test_mode", generate_test_params())
def test_dataint_ecc_hamming_secded(request, width, test_mode):
    """
    ECC Hamming SECDED encoder/decoder test runner

    Tests SECDED (Single Error Correction, Double Error Detection):
    - Encode/decode round-trip
    - Single-bit error correction
    - Double-bit error detection
    - All data patterns (small widths)
    """
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_common': 'rtl/common'
    , 'rtl_amba_includes': 'rtl/amba/includes'})

    # Need both encoder and decoder modules
    encoder_name = "dataint_ecc_hamming_encode_secded"
    decoder_name = "dataint_ecc_hamming_decode_secded"

    verilog_sources = [
        os.path.join(rtl_dict['rtl_common'], f'{encoder_name}.sv'),
        os.path.join(rtl_dict['rtl_common'], f'{decoder_name}.sv'),
    ]

    # Top-level wrapper module (created below)
    toplevel = "ecc_secded_wrapper"

    # Format parameters for unique test name
    w_str = TBBase.format_dec(width, 2)
    test_name_plus_params = f"test_ecc_secded_w{w_str}_{test_mode}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # Create wrapper module that instantiates both encoder and decoder
    wrapper_path = os.path.join(sim_build, f'{toplevel}.sv')
    import math
    parity_bits = math.ceil(math.log2(width + math.ceil(math.log2(width + math.ceil(math.log2(width + 1)))) + 1))
    total_width = width + parity_bits + 1

    with open(wrapper_path, 'w') as f:
        f.write(f'''`timescale 1ns / 1ps

// Wrapper module for ECC SECDED encoder/decoder testing
module {toplevel} #(
    parameter int WIDTH = {width}
) (
    input  logic                  clk,
    input  logic                  rst_n,
    input  logic                  enable,
    input  logic [WIDTH-1:0]      data,
    output logic [{total_width-1}:0] encoded_data,
    input  logic [{total_width-1}:0] hamming_data,
    output logic [WIDTH-1:0]      decoded_data,
    output logic                  error_detected,
    output logic                  double_error_detected
);

    // Instantiate encoder
    dataint_ecc_hamming_encode_secded #(
        .WIDTH(WIDTH),
        .DEBUG(0)
    ) u_encoder (
        .data(data),
        .encoded_data(encoded_data)
    );

    // Instantiate decoder
    dataint_ecc_hamming_decode_secded #(
        .WIDTH(WIDTH),
        .DEBUG(0)
    ) u_decoder (
        .clk(clk),
        .rst_n(rst_n),
        .enable(enable),
        .hamming_data(hamming_data),
        .data(decoded_data),
        .error_detected(error_detected),
        .double_error_detected(double_error_detected)
    );

endmodule
''')

    verilog_sources.append(wrapper_path)

    rtl_parameters = {
        'WIDTH': width,
    }

    extra_env = {
        'LOG_PATH': log_path,
        'PARAM_WIDTH': str(width),
    }

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            toplevel=toplevel,
            module=module,
            testcase="cocotb_ecc_secded_test",
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,
            keep_files=True,
            compile_args=["-Wno-TIMESCALEMOD"],
            sim_args=[],
            plusargs=[],
            includes=[rtl_dict['rtl_amba_includes']]
        )
        print(f"✓ Test completed! Logs: {log_path}")
    except Exception as e:
        print(f"❌ Test failed: {str(e)}")
        print(f"Logs: {log_path}")
        raise
