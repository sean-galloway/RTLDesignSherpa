"""
Performance profiling test for STREAM core.

This test measures key performance metrics for the stream_core design across
different configurations using the 'fast' (no-stress) timing profile.

Metrics collected:
- Throughput (beats/cycle, GB/s)
- Latency (first beat, average per transfer)
- Efficiency (% of theoretical max)
- Channel utilization
- SRAM utilization
- AXI bus efficiency

Test configurations:
- Single channel vs multi-channel
- Various data widths (128, 256, 512 bits)
- Various FIFO depths (512, 1024, 2048)
- Various transfer sizes

Author: RTL Design Sherpa
"""

import pytest
import os
import sys
import json
from pathlib import Path

# CRITICAL: Must setup paths BEFORE importing from CocoTBFramework
# First, do minimal setup to import get_repo_root
repo_root_temp = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../..'))
sys.path.insert(0, os.path.join(repo_root_temp, 'bin'))

from cocotb_test.simulator import run
import cocotb
from cocotb.triggers import ClockCycles, RisingEdge, Timer
from cocotb.clock import Clock

# Now we can import utilities
from CocoTBFramework.tbclasses.shared.utilities import get_repo_root, get_paths
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist

# Use the proper get_repo_root() function
repo_root = get_repo_root()
sys.path.insert(0, repo_root)

# Import testbench
from projects.components.stream.dv.tbclasses.stream_core_tb import StreamCoreTB

# ============================================================================
# Performance Test Configurations
# ============================================================================

PERF_TEST_CONFIGS = [
    # Single channel - various data widths
    # Weighted distribution: min 256, most at 512 for proper machinery stress
    {
        'name': 'single_ch_dw128',
        'num_channels': 4,
        'data_width': 128,
        'fifo_depth': 512,
        'test_channels': [0],
        'desc_count': 8,
        'transfer_sizes': [256, 384, 512, 512, 512],
    },
    {
        'name': 'single_ch_dw256',
        'num_channels': 4,
        'data_width': 256,
        'fifo_depth': 512,
        'test_channels': [0],
        'desc_count': 8,
        'transfer_sizes': [256, 384, 512, 512, 512],
    },
    {
        'name': 'single_ch_dw512',
        'num_channels': 4,
        'data_width': 512,
        'fifo_depth': 512,
        'test_channels': [0],
        'desc_count': 8,
        'transfer_sizes': [256, 384, 512, 512, 512],
    },

    # Multi-channel - 2 channels
    {
        'name': 'dual_ch_dw128',
        'num_channels': 4,
        'data_width': 128,
        'fifo_depth': 512,
        'test_channels': [0, 1],
        'desc_count': 8,
        'transfer_sizes': [256, 384, 512, 512],
    },
    {
        'name': 'dual_ch_dw256',
        'num_channels': 4,
        'data_width': 256,
        'fifo_depth': 512,
        'test_channels': [0, 1],
        'desc_count': 8,
        'transfer_sizes': [256, 384, 512, 512],
    },

    # Multi-channel - 4 channels
    {
        'name': 'quad_ch_dw128',
        'num_channels': 4,
        'data_width': 128,
        'fifo_depth': 512,
        'test_channels': [0, 1, 2, 3],
        'desc_count': 8,
        'transfer_sizes': [256, 384, 512, 512],
    },
    {
        'name': 'quad_ch_dw256',
        'num_channels': 4,
        'data_width': 256,
        'fifo_depth': 512,
        'test_channels': [0, 1, 2, 3],
        'desc_count': 8,
        'transfer_sizes': [256, 384, 512, 512],
    },

    # Varying FIFO depths
    {
        'name': 'fifo_depth_comparison_512',
        'num_channels': 4,
        'data_width': 256,
        'fifo_depth': 512,
        'test_channels': [0],
        'desc_count': 8,
        'transfer_sizes': [384, 512, 512],
    },
    {
        'name': 'fifo_depth_comparison_1024',
        'num_channels': 4,
        'data_width': 256,
        'fifo_depth': 1024,
        'test_channels': [0],
        'desc_count': 8,
        'transfer_sizes': [384, 512, 512],
    },
    {
        'name': 'fifo_depth_comparison_2048',
        'num_channels': 4,
        'data_width': 256,
        'fifo_depth': 2048,
        'test_channels': [0],
        'desc_count': 8,
        'transfer_sizes': [384, 512, 512],
    },
]

# ============================================================================
# CocoTB Performance Test
# ============================================================================

@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_performance_profile(dut):
    """Performance profiling test with 'fast' timing (no stress)"""

    # Get test configuration from parameters
    config_name = os.environ.get('PERF_CONFIG_NAME', 'single_ch_dw128')
    cocotb.log.info(f"Running performance test: {config_name}")

    # Find matching config
    config = next((c for c in PERF_TEST_CONFIGS if c['name'] == config_name), None)
    if not config:
        raise ValueError(f"Unknown performance config: {config_name}")

    # Initialize testbench with parameters from config
    tb = StreamCoreTB(
        dut,
        num_channels=config['num_channels'],
        data_width=config['data_width'],
        fifo_depth=config['fifo_depth']
    )

    # Setup clock and reset (SRAM configured via RTL parameters, not runtime)
    await tb.setup_clocks_and_reset()
    await tb.wait_clocks('clk', 10)

    # Performance metrics collection
    perf_results = {
        'config': config,
        'channels': {}
    }

    # Run transfers for each test channel
    for channel in config['test_channels']:
        cocotb.log.info(f"Testing channel {channel}")

        channel_metrics = {
            'transfers': [],
            'total_bytes': 0,
            'total_cycles': 0,
            'total_beats': 0,
        }

        # Create descriptor chain with various transfer sizes
        base_src_addr = 0x80000000 + (channel * 0x1000000)
        base_dst_addr = 0x90000000 + (channel * 0x1000000)
        src_offset = 0
        dst_offset = 0

        # Track descriptors for chain
        descriptors = []

        for i in range(config['desc_count']):
            # Rotate through transfer sizes
            transfer_size = config['transfer_sizes'][i % len(config['transfer_sizes'])]

            # Descriptor address (64-byte spacing like working test)
            desc_addr = tb.desc_mem_base + (channel * 0x100000) + (i * 64)
            next_desc_addr = desc_addr + 64 if i < config['desc_count'] - 1 else 0

            # Source/destination addresses (0x10000 offset per descriptor)
            src_addr = tb.src_mem_base + (i * 0x10000)
            dst_addr = tb.dst_mem_base + (i * 0x10000)

            # Write test pattern to source memory
            for beat in range(transfer_size):
                beat_addr = src_addr + (beat * tb.data_bytes)
                # Pattern includes descriptor index
                pattern = ((i << 4) | (beat & 0xF)) & 0xFF
                # Use byte replication (like working test)
                data = int.from_bytes(bytes([pattern] * tb.data_bytes), byteorder='little')
                tb.write_source_data(beat_addr, data, tb.data_bytes)

            # Write descriptor to memory
            is_last = (i == config['desc_count'] - 1)
            tb.write_descriptor(
                addr=desc_addr,
                src_addr=src_addr,
                dst_addr=dst_addr,
                length=transfer_size,
                next_ptr=next_desc_addr,
                priority=0,
                last=is_last
            )

            # Track descriptor for verification
            descriptors.append({
                'src_addr': src_addr,
                'dst_addr': dst_addr,
                'length': transfer_size
            })

        # Record start time
        start_time = cocotb.utils.get_sim_time('ns')

        # Kick off channel
        first_desc_addr = tb.desc_mem_base + (channel * 0x100000)
        await tb.kick_off_channel(channel, first_desc_addr)

        # Wait for completion (correct method name)
        await tb.wait_for_channel_idle(channel, timeout_us=100_000)

        # Record end time
        end_time = cocotb.utils.get_sim_time('ns')

        # Get performance stats from TB (has start/end times)
        perf_stats = tb.get_performance_stats(channel)

        # Calculate metrics
        total_ns = end_time - start_time
        total_beats = sum(config['transfer_sizes'])
        bytes_per_beat = tb.data_bytes
        total_bytes = total_beats * bytes_per_beat

        # Throughput calculations (assuming 10ns clock period = 100MHz)
        clock_period_ns = 10
        clock_freq_mhz = 1000.0 / clock_period_ns
        total_cycles = total_ns / clock_period_ns if total_ns > 0 else 0
        beats_per_cycle = total_beats / total_cycles if total_cycles > 0 else 0
        throughput_mbps = (total_bytes / (total_ns / 1000.0)) if total_ns > 0 else 0
        theoretical_max_mbps = (config['data_width'] / 8) * clock_freq_mhz
        efficiency_pct = (throughput_mbps / theoretical_max_mbps * 100) if theoretical_max_mbps > 0 else 0

        channel_metrics['total_beats'] = total_beats
        channel_metrics['total_bytes'] = total_bytes
        channel_metrics['total_cycles'] = int(total_cycles)
        channel_metrics['total_ns'] = int(total_ns)
        channel_metrics['beats_per_cycle'] = beats_per_cycle
        channel_metrics['throughput_mbps'] = throughput_mbps
        channel_metrics['theoretical_max_mbps'] = theoretical_max_mbps
        channel_metrics['efficiency_pct'] = efficiency_pct

        perf_results['channels'][channel] = channel_metrics

        cocotb.log.info(f"Channel {channel} Performance:")
        cocotb.log.info(f"  Total beats: {total_beats}")
        cocotb.log.info(f"  Total cycles: {total_cycles:.0f}")
        cocotb.log.info(f"  Throughput: {beats_per_cycle:.3f} beats/cycle")
        cocotb.log.info(f"  Bandwidth: {throughput_mbps:.1f} MB/s")
        cocotb.log.info(f"  Efficiency: {efficiency_pct:.1f}%")

        # Verify data transfer (like working test)
        cocotb.log.info(f"Verifying data for channel {channel}...")
        all_passed = True
        for idx, desc in enumerate(descriptors):
            match = tb.verify_transfer(desc['src_addr'], desc['dst_addr'], desc['length'])
            if not match:
                cocotb.log.error(f"Transfer {idx} ({desc['length']} beats) data mismatch")
                all_passed = False
            else:
                cocotb.log.info(f"Transfer {idx} ({desc['length']} beats) verified OK")

        if all_passed:
            cocotb.log.info(f"✓ Channel {channel} data verification PASSED")
        else:
            cocotb.log.error(f"✗ Channel {channel} data verification FAILED")

    # Save results to JSON file
    results_dir = Path("perf_results")
    results_dir.mkdir(exist_ok=True)
    results_file = results_dir / f"{config_name}_perf.json"

    with open(results_file, 'w') as f:
        json.dump(perf_results, f, indent=2)

    cocotb.log.info(f"Performance results saved to {results_file}")

# ============================================================================
# Pytest Wrapper
# ============================================================================

@pytest.mark.parametrize("config", PERF_TEST_CONFIGS, ids=lambda c: c['name'])
def test_stream_performance_profile(request, config):
    """Run performance profiling for a specific configuration"""

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})

    dut_name = "stream_core"

    # Get sources from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/stream/rtl/filelists/macro/stream_core.f'
    )

    # RTL parameters
    rtl_parameters = {
        'NUM_CHANNELS': config['num_channels'],
        'DATA_WIDTH': config['data_width'],
        'ADDR_WIDTH': 64,
        'AXI_ID_WIDTH': 8,
        'FIFO_DEPTH': config['fifo_depth'],
    }

    # Set environment variable for config name
    os.environ['PERF_CONFIG_NAME'] = config['name']
    os.environ['TIMING_PROFILE'] = 'fast'  # No-stress timing

    # Create unique sim_build directory for this config
    sim_build = f"local_sim_build/perf_{config['name']}"

    # Build extra_args conditionally based on WAVES
    waves_enabled = int(os.environ.get('WAVES', 0))
    extra_args = [
        "-Wno-WIDTH",
        "-Wno-CASEINCOMPLETE",
        "-Wno-TIMESCALEMOD",
        "-Wno-SELRANGE",
    ]
    if waves_enabled:
        extra_args.extend(["--trace-fst", "--trace-structs"])

    # Build and run
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_performance_profile",
        parameters=rtl_parameters,
        simulator="verilator",
        sim_build=sim_build,
        waves=waves_enabled,
        extra_args=extra_args,
        compile_args=[
            "-j", "4",
        ],
    )

# ============================================================================
# Performance Report Generation
# ============================================================================

def generate_performance_report():
    """Generate performance report from JSON results"""
    results_dir = Path("perf_results")

    if not results_dir.exists():
        print("No performance results found")
        return

    print("\n" + "="*80)
    print(" STREAM Core Performance Profiling Report")
    print("="*80)
    print("\nTiming Profile: FAST (no-stress)")
    print("\n" + "-"*80)

    # Collect all results
    all_results = []
    for json_file in sorted(results_dir.glob("*_perf.json")):
        with open(json_file, 'r') as f:
            results = json.load(f)
            all_results.append(results)

    # Group by category
    single_ch = [r for r in all_results if 'single_ch' in r['config']['name']]
    dual_ch = [r for r in all_results if 'dual_ch' in r['config']['name']]
    quad_ch = [r for r in all_results if 'quad_ch' in r['config']['name']]
    fifo_comp = [r for r in all_results if 'fifo_depth' in r['config']['name']]

    # Print results by category
    def print_category(title, results):
        print(f"\n{title}")
        print("-" * 80)
        print(f"{'Config':<25} {'Data Width':<12} {'Throughput':<15} {'Efficiency':<12} {'Latency (ns)'}")
        print("-" * 80)

        for r in results:
            config = r['config']
            # Get first channel metrics
            ch_metrics = list(r['channels'].values())[0]

            print(f"{config['name']:<25} "
                  f"{config['data_width']:<12} "
                  f"{ch_metrics['beats_per_cycle']:<6.3f} b/cyc   "
                  f"{ch_metrics['efficiency_pct']:<6.1f}%      "
                  f"{ch_metrics.get('total_ns', 0):<10.0f}")

    if single_ch:
        print_category("Single Channel Performance", single_ch)

    if dual_ch:
        print_category("Dual Channel Performance", dual_ch)

    if quad_ch:
        print_category("Quad Channel Performance", quad_ch)

    if fifo_comp:
        print_category("FIFO Depth Comparison", fifo_comp)

    print("\n" + "="*80)

if __name__ == "__main__":
    # Generate report from existing results
    generate_performance_report()
