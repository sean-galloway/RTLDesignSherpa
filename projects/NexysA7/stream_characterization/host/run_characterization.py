#!/usr/bin/env python3
"""
run_characterization.py - STREAM DMA characterization test runner

Drives the stream_char_harness on the Nexys A7 FPGA through UART to
execute the full 40-configuration characterization matrix:

  Phase 1:  1 descriptor/ch x 1 MB  x  1..8 channels  =  8 runs
  Phase 2:  {2,4,8,16} desc/ch x 1 MB  x  1..8 channels  = 32 runs

For each run:
  1. Reset CRC/LFSR (clear_stats)
  2. Load descriptor chain(s) into desc_ram
  3. Configure STREAM (global enable, channel enable)
  4. Kick off channels via APB
  5. Poll completion
  6. Read and compare CRC values
  7. Optionally dump MonBus trace from debug_sram
  8. Log results

Prerequisites:
  - FPGA programmed with stream_char bitstream
  - USB-UART connected (typically /dev/ttyUSB1)
  - pip install pyserial

Usage:
  python3 run_characterization.py                      # full matrix
  python3 run_characterization.py --port /dev/ttyUSB0  # different port
  python3 run_characterization.py --configs 1desc_1ch 1desc_2ch  # specific
  python3 run_characterization.py --phase 1             # phase 1 only
  python3 run_characterization.py --dry-run              # print plan, no FPGA

Requires: uart_axi_bridge.py from projects/components/converters/bin/
"""

import argparse
import os
import sys
import time
import json
from datetime import datetime
from pathlib import Path

# Add converters/bin to path for UARTAxiBridge
script_dir = Path(__file__).resolve().parent
repo_root = script_dir.parent.parent.parent.parent
sys.path.insert(0, str(repo_root / 'projects' / 'components' / 'converters' / 'bin'))

from descriptor_builder import (
    DescriptorBuilder, CharConfig, build_char_matrix, load_configs_from_csv,
    _size_label, _parse_size,
    HARNESS_CSR_BASE, STREAM_APB_BASE, DESC_RAM_BASE,
    CTRL_VALID, CTRL_LAST, CTRL_INTERRUPT,
)

# =========================================================================
# Harness CSR addresses
# =========================================================================
CSR_CTRL            = HARNESS_CSR_BASE + 0x00
CSR_STATUS          = HARNESS_CSR_BASE + 0x04
CSR_DBG_WR_PTR     = HARNESS_CSR_BASE + 0x08
CSR_DBG_OVERFLOW    = HARNESS_CSR_BASE + 0x0C
CSR_CRC_RD_EXPECTED = HARNESS_CSR_BASE + 0x10
CSR_CRC_WR_EXPECTED = HARNESS_CSR_BASE + 0x14
CSR_CRC_WR_COMPUTED = HARNESS_CSR_BASE + 0x18
CSR_CRC_MATCH       = HARNESS_CSR_BASE + 0x1C
CSR_SCRATCH         = HARNESS_CSR_BASE + 0x20
CSR_BUILD_ID        = HARNESS_CSR_BASE + 0x24

EXPECTED_BUILD_ID   = 0x5354_5243

# STREAM APB registers — from projects/components/stream/rtl/stream_regmap.py
APB_GLOBAL_CTRL         = STREAM_APB_BASE + 0x100
APB_CHANNEL_ENABLE      = STREAM_APB_BASE + 0x120
APB_CHANNEL_RESET       = STREAM_APB_BASE + 0x124
APB_SCHED_TIMEOUT_CYC   = STREAM_APB_BASE + 0x200
APB_SCHED_CONFIG        = STREAM_APB_BASE + 0x204
APB_DESCENG_CONFIG      = STREAM_APB_BASE + 0x220
APB_DESCENG_ADDR0_BASE  = STREAM_APB_BASE + 0x224
APB_DESCENG_ADDR0_LIMIT = STREAM_APB_BASE + 0x228
APB_DESCENG_ADDR1_BASE  = STREAM_APB_BASE + 0x22C
APB_DESCENG_ADDR1_LIMIT = STREAM_APB_BASE + 0x230
APB_AXI_XFER_CONFIG     = STREAM_APB_BASE + 0x2A0
APB_CH_KICK_BASE        = STREAM_APB_BASE + 0x000
APB_CH_KICK_STRIDE      = 0x08


# =========================================================================
# Test execution
# =========================================================================

class CharacterizationRunner:
    """Runs characterization tests on the FPGA via UART."""

    def __init__(self, bridge, data_width: int = 128,
                 verbose: bool = False):
        self.bridge = bridge
        self.builder = DescriptorBuilder(data_width=data_width)
        self.verbose = verbose
        self.results = []

    def log(self, msg: str):
        ts = datetime.now().strftime('%H:%M:%S')
        print(f"[{ts}] {msg}")

    def vlog(self, msg: str):
        if self.verbose:
            self.log(msg)

    # -----------------------------------------------------------------
    # Low-level helpers
    # -----------------------------------------------------------------

    def ping(self) -> bool:
        """Verify UART link + harness CSR are alive."""
        val = 0xDEAD_BEEF
        ok = self.bridge.write(CSR_SCRATCH, val)
        if not ok:
            self.log("ERROR: scratch write failed")
            return False
        rb = self.bridge.read(CSR_SCRATCH)
        if rb != val:
            self.log(f"ERROR: scratch mismatch: wrote 0x{val:08X}, read {rb}")
            return False

        bid = self.bridge.read(CSR_BUILD_ID)
        if bid != EXPECTED_BUILD_ID:
            self.log(f"ERROR: build_id mismatch: expected 0x{EXPECTED_BUILD_ID:08X}, got {bid}")
            return False

        self.log(f"Ping OK (build_id=0x{bid:08X})")
        return True

    def clear_stats(self):
        """Clear CRC/LFSR state and debug trace pointer."""
        self.bridge.write(CSR_CTRL, 0x02)  # clear_stats pulse
        time.sleep(0.01)

    def load_descriptors(self, writes):
        """Write descriptor data to desc_ram."""
        count = 0
        for addr, data in writes:
            ok = self.bridge.write(addr, data)
            if not ok:
                self.log(f"ERROR: descriptor write failed at 0x{addr:08X}")
                return False
            count += 1
        self.vlog(f"  Loaded {count} words into desc_ram")
        return True

    def configure_stream(self, num_channels: int):
        """Full STREAM configuration — matches StreamHelper sequence."""
        # Scheduler config
        sched_cfg = 0x0F  # SCHED_EN + TIMEOUT_EN + ERR_EN + COMPL_EN
        self.bridge.write(APB_SCHED_CONFIG, sched_cfg)
        self.bridge.write(APB_SCHED_TIMEOUT_CYC, 0xFFFF)

        # Descriptor engine config
        self.bridge.write(APB_DESCENG_CONFIG, 0x01)  # DESCENG_EN

        # Address ranges (full 32-bit space)
        self.bridge.write(APB_DESCENG_ADDR0_BASE,  0x0000_0000)
        self.bridge.write(APB_DESCENG_ADDR0_LIMIT, 0xFFFF_FFFF)
        self.bridge.write(APB_DESCENG_ADDR1_BASE,  0x0000_0000)
        self.bridge.write(APB_DESCENG_ADDR1_LIMIT, 0xFFFF_FFFF)

        # AXI burst config (16 beats rd + 16 beats wr)
        axi_cfg = (15 & 0xFF) | ((15 & 0xFF) << 8)
        self.bridge.write(APB_AXI_XFER_CONFIG, axi_cfg)

        # Global enable + channels
        self.bridge.write(APB_GLOBAL_CTRL, 0x01)
        ch_mask = (1 << num_channels) - 1
        self.bridge.write(APB_CHANNEL_ENABLE, ch_mask)
        self.vlog(f"  STREAM configured: sched=0x{sched_cfg:02X}, "
                  f"desceng=0x01, axi=0x{axi_cfg:04X}, ch_mask=0x{ch_mask:02X}")

    def kick_channels(self, kick_addresses: dict):
        """Write kick-off addresses to start descriptor fetch per channel.
        apbtodescr requires two APB writes per channel: LOW [31:0] then HIGH [63:32]."""
        for ch, axi4_addr in sorted(kick_addresses.items()):
            kick_reg = APB_CH_KICK_BASE + ch * APB_CH_KICK_STRIDE
            low  = axi4_addr & 0xFFFF_FFFF
            high = (axi4_addr >> 32) & 0xFFFF_FFFF
            self.bridge.write(kick_reg + 0, low)    # LOW word
            self.bridge.write(kick_reg + 4, high)   # HIGH word
            self.vlog(f"  Kicked channel {ch} → desc@0x{axi4_addr:08X}")

    def poll_completion(self, timeout_s: float = 30.0) -> dict:
        """Poll harness STATUS register until done or timeout."""
        start = time.time()
        while (time.time() - start) < timeout_s:
            status = self.bridge.read(CSR_STATUS)
            if status is None:
                time.sleep(0.1)
                continue

            irq = bool(status & 0x01)
            err = bool(status & 0x02)
            overflow = bool(status & 0x04)

            if irq or err:
                elapsed = time.time() - start
                return {
                    'completed': True,
                    'irq': irq,
                    'error': err,
                    'overflow': overflow,
                    'elapsed_s': elapsed,
                    'raw': status,
                }
            time.sleep(0.05)

        return {'completed': False, 'elapsed_s': timeout_s}

    def read_crc(self) -> dict:
        """Read CRC registers."""
        return {
            'rd_expected': self.bridge.read(CSR_CRC_RD_EXPECTED),
            'wr_expected': self.bridge.read(CSR_CRC_WR_EXPECTED),
            'wr_computed': self.bridge.read(CSR_CRC_WR_COMPUTED),
            'match_reg':   self.bridge.read(CSR_CRC_MATCH),
        }

    def read_trace_summary(self) -> dict:
        """Read debug trace metadata (not full dump)."""
        wr_ptr = self.bridge.read(CSR_DBG_WR_PTR)
        overflow = self.bridge.read(CSR_DBG_OVERFLOW)
        return {'wr_ptr': wr_ptr, 'overflow': overflow}

    def reset_stream(self):
        """Soft-reset STREAM via global control."""
        self.bridge.write(APB_GLOBAL_CTRL, 0x02)  # GLOBAL_RST
        time.sleep(0.05)
        self.bridge.write(APB_GLOBAL_CTRL, 0x00)  # clear
        time.sleep(0.05)

    # -----------------------------------------------------------------
    # Run a single configuration
    # -----------------------------------------------------------------

    def run_config(self, config: CharConfig) -> dict:
        """
        Execute one characterization configuration.

        Returns result dict with pass/fail, CRC, timing, etc.
        """
        self.log(f"--- {config.name}: {config.num_channels}ch x "
                 f"{config.descriptors_per_channel}desc x "
                 f"{config.transfer_bytes // 1024}KB ---")

        test_data = self.builder.build_test(config)
        result = {
            'name': config.name,
            'num_channels': config.num_channels,
            'descriptors_per_channel': config.descriptors_per_channel,
            'transfer_bytes': config.transfer_bytes,
            'total_descriptors': test_data['total_descriptors'],
            'total_bytes': test_data['total_bytes'],
        }

        # 1. Reset
        self.reset_stream()
        self.clear_stats()

        # 2. Load descriptors
        t0 = time.time()
        ok = self.load_descriptors(test_data['descriptor_writes'])
        result['load_time_s'] = time.time() - t0
        if not ok:
            result['pass'] = False
            result['error'] = 'descriptor_load_failed'
            return result
        self.log(f"  Descriptors loaded in {result['load_time_s']:.1f}s "
                 f"({len(test_data['descriptor_writes'])} writes)")

        # 3. Configure STREAM
        self.configure_stream(config.num_channels)

        # 4. Kick channels
        t0 = time.time()
        self.kick_channels(test_data['kick_addresses'])

        # 5. Poll completion
        completion = self.poll_completion(timeout_s=60.0)
        result['dma_time_s'] = time.time() - t0
        result['completion'] = completion

        if not completion.get('completed'):
            self.log(f"  TIMEOUT after {completion['elapsed_s']:.1f}s")
            result['pass'] = False
            result['error'] = 'timeout'
            return result

        self.log(f"  DMA completed in {result['dma_time_s']:.3f}s")

        if completion.get('error'):
            self.log(f"  ERROR flagged in status register")
            result['pass'] = False
            result['error'] = 'status_error'
            return result

        # 6. CRC check
        crc = self.read_crc()
        result['crc'] = crc
        match_reg = crc.get('match_reg')
        crc_match = (match_reg is not None) and (match_reg & 0x01 == 1)
        crc_valid = (match_reg is not None) and (match_reg & 0x02 == 2)

        if crc_match and crc_valid:
            self.log(f"  CRC MATCH (rd=0x{crc['rd_expected']:08X} "
                     f"wr=0x{crc['wr_computed']:08X})")
        else:
            self.log(f"  CRC MISMATCH! rd_exp=0x{crc.get('rd_expected', 0):08X} "
                     f"wr_comp=0x{crc.get('wr_computed', 0):08X} "
                     f"match_reg=0x{match_reg or 0:08X}")

        # 7. Trace summary
        trace = self.read_trace_summary()
        result['trace'] = trace
        self.vlog(f"  Trace: {trace['wr_ptr']} packets, "
                  f"overflow={'YES' if trace.get('overflow') else 'no'}")

        # 8. Throughput
        if result['dma_time_s'] > 0:
            mbps = (result['total_bytes'] / (1024 * 1024)) / result['dma_time_s']
            result['throughput_mbps'] = mbps
            self.log(f"  Throughput: {mbps:.1f} MB/s "
                     f"({result['total_bytes'] / (1024*1024):.0f} MB in "
                     f"{result['dma_time_s']:.3f}s)")

        result['pass'] = crc_match and crc_valid
        return result

    # -----------------------------------------------------------------
    # Run full matrix
    # -----------------------------------------------------------------

    def run_matrix(self, configs: list) -> list:
        """Run a list of configurations and collect results."""
        self.log(f"=== Characterization: {len(configs)} configurations ===\n")

        if not self.ping():
            self.log("FATAL: ping failed, aborting")
            return []

        results = []
        passed = 0
        failed = 0

        for i, cfg in enumerate(configs):
            self.log(f"\n[{i+1}/{len(configs)}]")
            result = self.run_config(cfg)
            results.append(result)
            if result.get('pass'):
                passed += 1
            else:
                failed += 1

        self.log(f"\n{'='*60}")
        self.log(f"RESULTS: {passed} passed, {failed} failed, "
                 f"{len(configs)} total")
        self.log(f"{'='*60}")

        return results


# =========================================================================
# CLI
# =========================================================================

def parse_args():
    parser = argparse.ArgumentParser(
        description="STREAM DMA characterization on Nexys A7",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""\
Examples:
  %(prog)s                                    # full 40-config matrix
  %(prog)s --csv char_tests.csv               # run from CSV (comment lines to skip)
  %(prog)s --csv char_tests.csv --dry-run     # preview CSV without running
  %(prog)s --phase 1                          # phase 1 only (8 configs)
  %(prog)s --size 64KB --channels 1 8         # custom size, specific channels
  %(prog)s --configs 1desc_1ch 4desc_8ch      # specific configs by name
  %(prog)s --dry-run                          # print plan, don't run
  %(prog)s --port /dev/ttyUSB0 -v             # different port, verbose
  %(prog)s --output results.json              # save results to JSON
""")
    parser.add_argument('--port', default='/dev/ttyUSB1',
                        help='Serial port (default: /dev/ttyUSB1)')
    parser.add_argument('--baud', type=int, default=115200,
                        help='Baud rate (default: 115200)')
    parser.add_argument('--phase', type=int, choices=[1, 2],
                        help='Run only phase 1 or phase 2')
    parser.add_argument('--configs', nargs='+',
                        help='Run only named configs (e.g., 1desc_1ch 4desc_8ch)')
    parser.add_argument('--channels', type=int, nargs='+',
                        help='Limit to specific channel counts (e.g., 1 4 8)')
    parser.add_argument('--size', type=str, default='1MB',
                        help='Transfer size per descriptor (e.g., 4KB, 1MB, 4MB; default 1MB)')
    parser.add_argument('--csv', type=str, default=None,
                        help='Load test configs from CSV file (overrides --phase/--size/--configs)')
    parser.add_argument('--dry-run', action='store_true',
                        help='Print test plan without running')
    parser.add_argument('--output', '-o', type=str,
                        help='Save results to JSON file')
    parser.add_argument('--verbose', '-v', action='store_true',
                        help='Verbose output')
    return parser.parse_args()


def main():
    args = parse_args()

    # Build config list — CSV takes priority over programmatic matrix
    if args.csv:
        configs = load_configs_from_csv(args.csv)
    else:
        transfer_bytes = _parse_size(args.size)
        all_configs = build_char_matrix(transfer_bytes=transfer_bytes)

        # Filter
        configs = all_configs
        if args.phase == 1:
            configs = [c for c in configs if c.descriptors_per_channel == 1]
        elif args.phase == 2:
            configs = [c for c in configs if c.descriptors_per_channel > 1]

        if args.configs:
            configs = [c for c in configs if c.name in args.configs]

        if args.channels:
            configs = [c for c in configs if c.num_channels in args.channels]

    if not configs:
        print("No configurations match the filter. Use --dry-run to see available.")
        return 1

    # Dry run
    if args.dry_run:
        builder = DescriptorBuilder(data_width=128)
        print(f"Test plan: {len(configs)} configurations\n")
        print(f"{'#':<4} {'Name':<28} {'Ch':>3} {'Desc/Ch':>8} "
              f"{'Total Data':>12} {'UART Writes':>12}")
        print("-" * 75)
        for i, cfg in enumerate(configs):
            test = builder.build_test(cfg)
            total_label = _size_label(test['total_bytes'])
            print(f"{i+1:<4} {cfg.name:<28} {cfg.num_channels:>3} "
                  f"{cfg.descriptors_per_channel:>8} "
                  f"{total_label:>12} "
                  f"{len(test['descriptor_writes']):>12}")
        return 0

    # Lazy import — pyserial only needed for real FPGA runs
    from uart_axi_bridge import UARTAxiBridge

    # Run
    with UARTAxiBridge(args.port, args.baud) as bridge:
        runner = CharacterizationRunner(
            bridge, data_width=128, verbose=args.verbose)
        results = runner.run_matrix(configs)

    # Save results
    if args.output and results:
        with open(args.output, 'w') as f:
            json.dump(results, f, indent=2, default=str)
        print(f"\nResults saved to {args.output}")

    # Exit code: 0 if all passed
    all_pass = all(r.get('pass') for r in results) if results else False
    return 0 if all_pass else 1


if __name__ == '__main__':
    sys.exit(main())
