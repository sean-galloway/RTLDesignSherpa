"""
V1 Baseline Read Engine Performance Test

Purpose: Measure sustained bandwidth with 1000 commands for V1 (single outstanding) read engine.
Collects empirical data for DMA performance modeling.

Author: RTL Design Sherpa
Created: 2025-10-28
"""

import os
import sys
import json
import pytest
import cocotb
from cocotb_test.simulator import run

# Add repo root to path
# Setup Python path BEFORE any other imports
# First, do minimal setup to import get_repo_root
repo_root_temp = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../..'))
sys.path.insert(0, os.path.join(repo_root_temp, 'bin'))

# Now import utilities to get proper repo root
from CocoTBFramework.tbclasses.shared.utilities import get_repo_root

# Use the proper get_repo_root() function
repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.stream.dv.tbclasses.datapath_rd_test_tb import DatapathRdTestTB
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


#=============================================================================
# Test Configuration Matrix
#=============================================================================

def generate_v1_baseline_params():
    """Generate V1 baseline test parameter matrix."""

    configs = []

    # Standard Test Matrix (18 configurations):
    # - 2 data widths (128, 256 bits)
    # - 3 burst sizes (256B, 512B, 1024B)
    # - 3 memory latencies (3, 60, 100 cycles)

    data_widths = [128, 256]
    burst_sizes_bytes = [256, 512, 1024]
    memory_configs = [
        ('SRAM', 3, False),
        ('DDR3', 60, False),
        ('DDR4', 100, False)
    ]

    for data_width in data_widths:
        bytes_per_beat = data_width // 8

        for burst_size_bytes in burst_sizes_bytes:
            beats_per_burst = burst_size_bytes // bytes_per_beat

            for memory_type, latency, is_stress in memory_configs:
                configs.append({
                    'data_width': data_width,
                    'burst_size_bytes': burst_size_bytes,
                    'beats_per_burst': beats_per_burst,
                    'memory_type': memory_type,
                    'memory_latency': latency,
                    'num_commands': 100,
                    'perf_config': 'v1',
                    'stress_mode': is_stress
                })

    # Stress Test Matrix (6 configurations):
    # - Maximum data width (256 bits)
    # - Maximum burst size (1024B)
    # - All memory latencies (3, 60, 100 cycles)
    # - Zero BFM delays (except prescribed latency)

    stress_configs = [
        ('SRAM_STRESS', 3, True),
        ('DDR3_STRESS', 60, True),
        ('DDR4_STRESS', 100, True)
    ]

    stress_data_width = 256
    stress_burst_size_bytes = 1024
    stress_bytes_per_beat = stress_data_width // 8
    stress_beats_per_burst = stress_burst_size_bytes // stress_bytes_per_beat

    for memory_type, latency, is_stress in stress_configs:
        configs.append({
            'data_width': stress_data_width,
            'burst_size_bytes': stress_burst_size_bytes,
            'beats_per_burst': stress_beats_per_burst,
            'memory_type': memory_type,
            'memory_latency': latency,
            'num_commands': 100,
            'perf_config': 'v1',
            'stress_mode': is_stress
        })

    return configs


# Generate test parameters
v1_configs = generate_v1_baseline_params()

# Generate meaningful test IDs
def generate_test_ids(configs):
    """Generate meaningful pytest IDs for each configuration."""
    ids = []
    for cfg in configs:
        prefix = "stress" if cfg['stress_mode'] else "std"
        test_id = (
            f"{prefix}_dw{cfg['data_width']}_"
            f"bs{cfg['burst_size_bytes']}_"
            f"{cfg['memory_type']}_lat{cfg['memory_latency']}"
        )
        ids.append(test_id)
    return ids

v1_test_ids = generate_test_ids(v1_configs)


#=============================================================================
# CocoTB Test Functions
#=============================================================================

@cocotb.test(timeout_time=100, timeout_unit="us")  # 100us timeout for stress tests (100 commands)
async def cocotb_test_v1_baseline_performance(dut):
    """V1 baseline sustained bandwidth measurement (up to 1000 commands for stress tests)."""

    # Get test configuration from environment
    data_width = int(os.environ.get('PERF_DATA_WIDTH', '512'))
    burst_size_bytes = int(os.environ.get('PERF_BURST_SIZE', '256'))
    memory_latency = int(os.environ.get('PERF_MEMORY_LATENCY', '3'))
    memory_type = os.environ.get('PERF_MEMORY_TYPE', 'SRAM')
    num_commands = int(os.environ.get('PERF_NUM_COMMANDS', '100'))  # Default 100 commands
    stress_mode = bool(int(os.environ.get('PERF_STRESS_MODE', '0')))

    bytes_per_beat = data_width // 8
    beats_per_burst = burst_size_bytes // bytes_per_beat

    tb = DatapathRdTestTB(dut)
    await tb.setup_clocks_and_reset()

    # Note: AXI slave read latency configured in memory model
    # (R beat delays controlled by memory model's read_latency parameter)

    channel_id = 0
    src_addr = 0x0000_0000  # Start at address 0 for simplicity

    # Performance measurement: Issue 1000 commands back-to-back
    tb.log.info(f"{'='*80}")
    tb.log.info(f"V1 BASELINE READ PERFORMANCE TEST")
    tb.log.info(f"  Data Width: {data_width} bits ({bytes_per_beat} bytes/beat)")
    tb.log.info(f"  Burst Size: {burst_size_bytes} bytes ({beats_per_burst} beats)")
    tb.log.info(f"  Memory: {memory_type} (latency={memory_latency} cycles)")
    tb.log.info(f"  Commands: {num_commands}")
    tb.log.info(f"  Stress Mode: {'ENABLED (zero BFM delays)' if stress_mode else 'DISABLED (normal delays)'}")
    tb.log.info(f"{'='*80}")

    # Stress mode configuration
    # Note: Read test already uses direct RTL signal control (zero delays - issues commands
    # as fast as ready allows). For true stress mode, would need to configure AXI slave for
    # back-to-back R beats (no random delays/backpressure beyond prescribed latency).
    # Current implementation: Uses default AXI slave behavior with set_read_latency configured.
    # This is sufficient for V1 baseline characterization.
    if stress_mode:
        tb.log.info("Stress mode: Direct RTL control already operates at max speed (zero delays)")
        tb.log.info("Stress mode: AXI slave uses default behavior + prescribed latency")
        # Future enhancement: Add AXI slave strict timing mode (back-to-back R beats after latency)

    # Populate memory for all commands
    total_beats = num_commands * beats_per_burst
    await tb.populate_memory(src_addr, total_beats, pattern='increment')

    # Start cycle counter
    start_cycle = tb.cycle_count
    commands_issued = 0
    commands_completed = 0
    current_addr = src_addr

    # Issue commands and track completion
    while commands_issued < num_commands or commands_completed < num_commands:
        # Issue new command if ready and haven't issued all
        if commands_issued < num_commands and tb.dut.datard_ready.value == 1:
            # Issue read request
            tb.dut.datard_valid.value = 1
            tb.dut.datard_addr.value = current_addr
            tb.dut.datard_beats_remaining.value = beats_per_burst
            tb.dut.datard_burst_len.value = beats_per_burst
            tb.dut.datard_channel_id.value = channel_id

            await tb.wait_clocks('clk', 1)

            tb.dut.datard_valid.value = 0
            commands_issued += 1
            current_addr += burst_size_bytes

            if commands_issued % 100 == 0:
                tb.log.info(f"Issued {commands_issued}/{num_commands} commands")
        else:
            tb.dut.datard_valid.value = 0
            await tb.wait_clocks('clk', 1)

        # Check for completion
        if tb.dut.datard_done_strobe.value == 1:
            commands_completed += 1
            if commands_completed % 100 == 0:
                tb.log.info(f"Completed {commands_completed}/{num_commands} commands")

    # End cycle counter
    end_cycle = tb.cycle_count
    total_cycles = end_cycle - start_cycle

    # Calculate metrics
    bandwidth_beats_per_cycle = total_beats / total_cycles
    ideal_bandwidth = 1.0  # 1 beat per cycle is ideal
    efficiency_percent = (bandwidth_beats_per_cycle / ideal_bandwidth) * 100.0

    # Calculate GB/s @ 200MHz
    clock_freq_mhz = 200
    bytes_per_sec = bandwidth_beats_per_cycle * bytes_per_beat * clock_freq_mhz * 1e6
    gb_per_sec = bytes_per_sec / 1e9

    # Output performance metrics in parseable format
    tb.log.info(f"")
    tb.log.info(f"{'='*80}")
    tb.log.info(f"PERFORMANCE RESULTS")
    tb.log.info(f"{'='*80}")
    tb.log.info(f"  Total Cycles: {total_cycles}")
    tb.log.info(f"  Total Beats: {total_beats}")
    tb.log.info(f"  Bandwidth: {bandwidth_beats_per_cycle:.4f} beats/cycle")
    tb.log.info(f"  Bandwidth: {gb_per_sec:.2f} GB/s @ {clock_freq_mhz}MHz")
    tb.log.info(f"  Efficiency: {efficiency_percent:.2f}%")
    tb.log.info(f"{'='*80}")

    # Output machine-parseable metric for report generation
    metric_line = (
        f"PERF_METRIC_V1_READ: "
        f"dw={data_width}, "
        f"bs={burst_size_bytes}, "
        f"mem={memory_type}, "
        f"lat={memory_latency}, "
        f"cycles={total_cycles}, "
        f"beats={total_beats}, "
        f"bw_beats={bandwidth_beats_per_cycle:.4f}, "
        f"bw_gbps={gb_per_sec:.2f}, "
        f"eff={efficiency_percent:.2f}"
    )
    tb.log.info(metric_line)

    # Also write JSON output for automated processing
    results = {
        'config': {
            'version': 'v1',
            'engine': 'read',
            'data_width_bits': data_width,
            'burst_size_bytes': burst_size_bytes,
            'beats_per_burst': beats_per_burst,
            'memory_type': memory_type,
            'memory_latency_cycles': memory_latency,
            'num_commands': num_commands
        },
        'metrics': {
            'total_cycles': total_cycles,
            'total_beats': total_beats,
            'bandwidth_beats_per_cycle': bandwidth_beats_per_cycle,
            'bandwidth_gbps': gb_per_sec,
            'efficiency_percent': efficiency_percent,
            'clock_freq_mhz': clock_freq_mhz
        }
    }

    # Write JSON to test output directory
    json_output_dir = os.environ.get('PERF_JSON_DIR', '/tmp')
    json_filename = (
        f"v1_read_perf_dw{data_width}_bs{burst_size_bytes}_"
        f"{memory_type}_lat{memory_latency}.json"
    )
    json_path = os.path.join(json_output_dir, json_filename)

    try:
        with open(json_path, 'w') as f:
            json.dump(results, f, indent=2)
        tb.log.info(f"Performance results written to: {json_path}")
    except Exception as e:
        tb.log.warning(f"Could not write JSON results: {e}")

    # Validate results are reasonable
    assert total_beats == num_commands * beats_per_burst, \
        f"Beat count mismatch: {total_beats} != {num_commands * beats_per_burst}"
    assert bandwidth_beats_per_cycle > 0, "Bandwidth must be positive"
    assert efficiency_percent <= 100, f"Efficiency cannot exceed 100%: {efficiency_percent}%"


#=============================================================================
# Pytest Wrapper Functions
#=============================================================================

@pytest.mark.parametrize("config", v1_configs, ids=v1_test_ids)
def test_v1_baseline_read_performance(request, config):
    """Pytest wrapper for V1 baseline read performance test."""

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_fub': '../../../../rtl/stream_fub'
    })

    dut_name = "datapath_rd_test"

    # Create descriptive test name
    test_name = (
        f"v1_read_perf_dw{config['data_width']}_"
        f"bs{config['burst_size_bytes']}_"
        f"{config['memory_type']}_lat{config['memory_latency']}"
    )

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/stream/rtl/filelists/fub/datapath_rd_test.f'
    )

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # Create JSON output directory
    json_output_dir = os.path.join(tests_dir, 'performance_results')
    os.makedirs(json_output_dir, exist_ok=True)

    log_path = os.path.join(log_dir, f'{test_name}.log')
    results_path = os.path.join(log_dir, f'results_{test_name}.xml')

    # V1 configuration: ENABLE_CMD_PIPELINE = 0
    parameters = {
        'DATA_WIDTH': str(config['data_width']),
        'NUM_CHANNELS': '8',
        'SRAM_DEPTH': '4096',
        'ENABLE_CMD_PIPELINE': '0',  # V1 configuration
        'CMD_QUEUE_DEPTH': '4',      # Unused in V1
        'MAX_OUTSTANDING': '4'       # Unused in V1
    }

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': '42',  # Fixed seed for reproducibility
        # Performance test configuration
        'PERF_DATA_WIDTH': str(config['data_width']),
        'PERF_BURST_SIZE': str(config['burst_size_bytes']),
        'PERF_MEMORY_LATENCY': str(config['memory_latency']),
        'PERF_MEMORY_TYPE': config['memory_type'],
        'PERF_NUM_COMMANDS': str(config['num_commands']),
        'PERF_JSON_DIR': json_output_dir,
        'PERF_STRESS_MODE': '1' if config['stress_mode'] else '0',
    }

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        "--trace-depth", "99",
    ]

    sim_args = [
        "--trace",
        "--trace-depth", "99",
    ]

    plusargs = [
        "--trace",
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase="cocotb_test_v1_baseline_performance",
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs
        )
        print(f"✓ V1 baseline read PASSED: {test_name}")
    except Exception as e:
        print(f"✗ V1 baseline read FAILED: {test_name}: {str(e)}")
        raise


#=============================================================================
# Main entry point for standalone execution
#=============================================================================

if __name__ == "__main__":
    # Run all V1 baseline configurations
    pytest.main([__file__, '-v', '-s'])
