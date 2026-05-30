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

# Add converters/bin to path for UARTAxiBridge.
# host/ is five levels under the repo root:
#   host -> flows-stream-bridge -> stream_characterization
#         -> NexysA7 -> projects -> REPO_ROOT
script_dir = Path(__file__).resolve().parent
repo_root = script_dir.parent.parent.parent.parent.parent
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
# Per-channel CRC verification (multi-channel)
CSR_CRC_RD_PER_CH_BASE = HARNESS_CSR_BASE + 0x60
CSR_CRC_WR_PER_CH_BASE = HARNESS_CSR_BASE + 0x80
CSR_CRC_VALID_MASK     = HARNESS_CSR_BASE + 0xA0
CSR_CRC_MATCH_MASK     = HARNESS_CSR_BASE + 0xA4
# Kick-burst fast path
CSR_CH_KICK_ADDR_BASE  = HARNESS_CSR_BASE + 0xB0
CSR_KICK_GO            = HARNESS_CSR_BASE + 0xC0
CSR_SCRATCH         = HARNESS_CSR_BASE + 0x20
CSR_BUILD_ID        = HARNESS_CSR_BASE + 0x24

# Harness timer (the right "DMA is done" signal). The IRQ-on-completion
# path is not wired by default -- descriptors don't set CTRL_INTERRUPT
# and no monbus packet type is routed to the err FIFO at boot. The timer
# fires when the write-side beat count reaches TIMER_EXPECTED_BEATS.
CSR_TIMER_CTRL          = HARNESS_CSR_BASE + 0x28  # W: bit 0 = clear pulse
CSR_TIMER_STATUS        = HARNESS_CSR_BASE + 0x2C  # R: [0]=done [1]=running [2]=pass
CSR_TIMER_CYCLES_LO     = HARNESS_CSR_BASE + 0x30
CSR_TIMER_CYCLES_HI     = HARNESS_CSR_BASE + 0x34
CSR_TIMER_EXPECTED_BEATS= HARNESS_CSR_BASE + 0x38  # RW: stop when sink beat >= this

# Per-engine first/last beat cycle stamps (steady-state datapath window).
CSR_TIMER_R_FIRST_LO    = HARNESS_CSR_BASE + 0x40
CSR_TIMER_R_FIRST_HI    = HARNESS_CSR_BASE + 0x44
CSR_TIMER_R_LAST_LO     = HARNESS_CSR_BASE + 0x48
CSR_TIMER_R_LAST_HI     = HARNESS_CSR_BASE + 0x4C
CSR_TIMER_W_FIRST_LO    = HARNESS_CSR_BASE + 0x50
CSR_TIMER_W_FIRST_HI    = HARNESS_CSR_BASE + 0x54
CSR_TIMER_W_LAST_LO     = HARNESS_CSR_BASE + 0x58
CSR_TIMER_W_LAST_HI     = HARNESS_CSR_BASE + 0x5C

# axi_bus_meter readback bases (R = 0x100, W = 0x180); per-meter offsets
# match read_bus_meters.py's OFF_* constants -- see that module for the
# full per-(channel,bucket) map.
CSR_RD_METER_BASE       = HARNESS_CSR_BASE + 0x100
CSR_WR_METER_BASE       = HARNESS_CSR_BASE + 0x180

# Engine data width in BYTES per beat. The DMA's AXI bus is 128 bits wide
# (DATA_WIDTH parameter in stream_top_ch8 / stream_char_top), so each
# beat moves 16 bytes. expected_beats = total_bytes // DATA_WIDTH_BYTES.
DATA_WIDTH_BYTES = 16

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
        self.bridge.write(APB_SCHED_TIMEOUT_CYC, 0x0FFFFFFF)  # 28-bit, ~2.68s @ 100MHz

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
        """Kick-burst fast path: pre-load per-channel addresses into the
        harness CSR shadow registers, then fire a single KICK_GO write
        with a channel bitmask. The harness pulses every kick line on the
        same aclk cycle, so multi-channel runs actually pipeline instead
        of serializing on the slow UART that the legacy per-channel APB
        kick path needed (~2 ms / write at 115200 baud)."""
        mask = 0
        for ch, axi4_addr in sorted(kick_addresses.items()):
            self.bridge.write(CSR_CH_KICK_ADDR_BASE + 4 * ch,
                              axi4_addr & 0xFFFFFFFF)
            mask |= (1 << ch)
            self.vlog(f"  Loaded channel {ch} kick addr 0x{axi4_addr:08X}")
        self.bridge.write(CSR_KICK_GO, mask)
        self.vlog(f"  Kick burst fired, mask=0x{mask:02X}")

    # -----------------------------------------------------------------
    # Methodology metrics capture (per DMA_UTILIZATION_MEASUREMENT.md)
    # -----------------------------------------------------------------
    @staticmethod
    def _read64(bridge, lo_addr: int, hi_addr: int) -> int:
        lo = bridge.read(lo_addr) or 0
        hi = bridge.read(hi_addr) or 0
        return ((hi & 0xFFFF_FFFF) << 32) | (lo & 0xFFFF_FFFF)

    def read_run_metrics(self, num_channels: int) -> dict:
        """Snapshot timer + bus meter state at the moment 'done' fired.

        Computes the methodology-doc primitives:

          - Datapath utilization, per side (Section 2.1 burst-only window)
              R = R_prod_aggregate / (R_LAST - R_FIRST + 1)
              W = W_prod_aggregate / (W_LAST - W_FIRST + 1)

          - End-to-end utilization (Section 2.3, end event = timer 'done')
              prod_bytes / (timer_cycles * data_width_bytes)

          - 4-bucket bus breakdown (Section 3) -- aggregate counts on
            each side as percentages of (R_LAST - R_FIRST + 1) and
            (W_LAST - W_FIRST + 1) respectively.

          - Per-channel productive / backpressure / starvation / idle
            with the sticky overflow mask (one bit per (channel, bucket)
            that wrapped the 16-bit per-channel counter).

        The raw timer + meter snapshot is returned alongside the derived
        ratios so the JSON output preserves everything for offline
        analysis.
        """
        # Lazy import so the optional read_bus_meters module isn't a hard
        # dep of run_characterization (e.g. for older bitstreams).
        try:
            from read_bus_meters import (
                read_meter, R_METER_BASE, W_METER_BASE,
            )
        except ImportError:
            return {'available': False, 'error': 'read_bus_meters import failed'}

        # Timer values (cycle stamps captured by stream_char_harness)
        cycles_total = self._read64(self.bridge,
                                    CSR_TIMER_CYCLES_LO, CSR_TIMER_CYCLES_HI)
        r_first = self._read64(self.bridge,
                               CSR_TIMER_R_FIRST_LO, CSR_TIMER_R_FIRST_HI)
        r_last  = self._read64(self.bridge,
                               CSR_TIMER_R_LAST_LO,  CSR_TIMER_R_LAST_HI)
        w_first = self._read64(self.bridge,
                               CSR_TIMER_W_FIRST_LO, CSR_TIMER_W_FIRST_HI)
        w_last  = self._read64(self.bridge,
                               CSR_TIMER_W_LAST_LO,  CSR_TIMER_W_LAST_HI)

        # Bus meter snapshots (aggregate + per-channel for both sides).
        rd_meter = read_meter(self.bridge, R_METER_BASE, num_channels, 'R')
        wr_meter = read_meter(self.bridge, W_METER_BASE, num_channels, 'W')

        # Datapath windows: methodology Section 2.1 -- first-to-last beat
        # on each engine. Steady-state utilization isolates the engine
        # from descriptor-fetch + last-burst-drain overhead.
        r_window = (r_last - r_first + 1) if r_last >= r_first and r_last > 0 else 0
        w_window = (w_last - w_first + 1) if w_last >= w_first and w_last > 0 else 0

        r_datapath_util = (rd_meter.aggregate.productive / r_window) if r_window else 0.0
        w_datapath_util = (wr_meter.aggregate.productive / w_window) if w_window else 0.0

        # End-to-end (Section 2.3, end = TIMER_STATUS.done). 'cycles_total'
        # is the harness timer's free-running counter spanning the same
        # window the meters accumulate over.
        prod_beats = rd_meter.aggregate.productive  # = W productive for in-order DMA
        ee_util    = (prod_beats / cycles_total) if cycles_total else 0.0

        # 4-bucket aggregate breakdown (Section 3), expressed as fraction
        # of the per-side window. The meters freeze at timer 'done' so
        # all four bucket counts reflect only in-window cycles.
        def buckets(meter, window):
            if window == 0:
                return {'productive': 0.0, 'backpressure': 0.0,
                        'starvation':  0.0, 'idle':         0.0}
            return {
                'productive':   meter.aggregate.productive   / window,
                'backpressure': meter.aggregate.backpressure / window,
                'starvation':   meter.aggregate.starvation   / window,
                'idle':         meter.aggregate.idle         / window,
            }

        return {
            'available': True,
            'cycles_total': cycles_total,
            'r_first': r_first, 'r_last': r_last, 'r_window_cycles': r_window,
            'w_first': w_first, 'w_last': w_last, 'w_window_cycles': w_window,
            'datapath_utilization_r': r_datapath_util,
            'datapath_utilization_w': w_datapath_util,
            'end_to_end_utilization': ee_util,
            'r_buckets_pct': buckets(rd_meter, r_window),
            'w_buckets_pct': buckets(wr_meter, w_window),
            'r_aggregate': {
                'productive':   rd_meter.aggregate.productive,
                'backpressure': rd_meter.aggregate.backpressure,
                'starvation':   rd_meter.aggregate.starvation,
                'idle':         rd_meter.aggregate.idle,
            },
            'w_aggregate': {
                'productive':   wr_meter.aggregate.productive,
                'backpressure': wr_meter.aggregate.backpressure,
                'starvation':   wr_meter.aggregate.starvation,
                'idle':         wr_meter.aggregate.idle,
            },
            'r_per_channel': [{
                'channel': c.channel,
                'productive': c.productive, 'backpressure': c.backpressure,
                'starvation': c.starvation, 'idle': c.idle,
                'overflow_mask': c.overflow,
            } for c in rd_meter.per_channel],
            'w_per_channel': [{
                'channel': c.channel,
                'productive': c.productive, 'backpressure': c.backpressure,
                'starvation': c.starvation, 'idle': c.idle,
                'overflow_mask': c.overflow,
            } for c in wr_meter.per_channel],
        }

    def setup_timer(self, total_bytes: int) -> int:
        """Program the harness timer's stop trigger and zero its counter.

        Returns the expected beat count. Call after configure_stream and
        before kick_channels. Polls clear_busy (STATUS[3]) to make sure the
        debug_sram wipe + meter clear from a prior clear_stats has finished
        before we arm the timer.
        """
        # Wait for any prior clear_stats to finish (debug_sram wipe takes
        # ~656 us at 100 MHz, well under one UART round-trip; this is mostly
        # belt-and-braces).
        for _ in range(100):
            st = self.bridge.read(CSR_STATUS)
            if st is None or (st & 0x08) == 0:  # bit 3 = clear_busy
                break
            time.sleep(0.01)

        expected_beats = total_bytes // DATA_WIDTH_BYTES
        # Pulse-clear the timer counter + first/last latches, then arm the
        # stop trigger. Order matters: clear first so a stale stop from a
        # previous run can't immediately re-latch done.
        self.bridge.write(CSR_TIMER_CTRL, 0x1)
        self.bridge.write(CSR_TIMER_EXPECTED_BEATS, expected_beats)
        self.vlog(f"  Timer armed: expected_beats={expected_beats} "
                  f"(= {total_bytes} bytes / {DATA_WIDTH_BYTES} B/beat)")
        return expected_beats

    def poll_completion(self, timeout_s: float = 30.0) -> dict:
        """Poll harness TIMER_STATUS until 'done' or timeout.

        The harness latches done = 1 when the write-side beat counter
        reaches TIMER_EXPECTED_BEATS (programmed by setup_timer). We also
        watch STATUS[1] (any_error sticky) so a bus-level error surfaces
        even before the timer terminates.
        """
        start = time.time()
        while (time.time() - start) < timeout_s:
            ts = self.bridge.read(CSR_TIMER_STATUS)
            st = self.bridge.read(CSR_STATUS)
            if ts is None or st is None:
                time.sleep(0.1)
                continue

            done    = bool(ts & 0x01)
            running = bool(ts & 0x02)
            tpass   = bool(ts & 0x04)
            err     = bool(st & 0x02)
            irq     = bool(st & 0x01)
            overflow = bool(st & 0x04)

            if done or err:
                elapsed = time.time() - start
                return {
                    'completed': True,
                    'irq': irq,
                    'error': err,
                    'overflow': overflow,
                    'timer_pass': tpass,
                    'timer_running': running,
                    'elapsed_s': elapsed,
                    'raw_timer': ts,
                    'raw_status': st,
                }
            time.sleep(0.05)

        return {'completed': False, 'elapsed_s': timeout_s}

    def read_crc(self, num_channels: int = 1) -> dict:
        """Read CRC registers.

        Aggregate scalars stay backward-compat (rd_expected = ch0,
        match_reg = AND-reduce). Per-channel arrays + bitmasks expose
        each channel's pass/fail independently for multi-channel runs.
        """
        rd_per_ch = []
        wr_per_ch = []
        for ch in range(num_channels):
            rd_per_ch.append(self.bridge.read(CSR_CRC_RD_PER_CH_BASE + 4 * ch))
            wr_per_ch.append(self.bridge.read(CSR_CRC_WR_PER_CH_BASE + 4 * ch))
        return {
            'rd_expected': self.bridge.read(CSR_CRC_RD_EXPECTED),
            'wr_expected': self.bridge.read(CSR_CRC_WR_EXPECTED),
            'wr_computed': self.bridge.read(CSR_CRC_WR_COMPUTED),
            'match_reg':   self.bridge.read(CSR_CRC_MATCH),
            'rd_per_ch':   rd_per_ch,
            'wr_per_ch':   wr_per_ch,
            'valid_mask':  self.bridge.read(CSR_CRC_VALID_MASK) or 0,
            'match_mask':  self.bridge.read(CSR_CRC_MATCH_MASK) or 0,
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

        # 4. Arm the harness timer with the expected sink-side beat count.
        # The timer fires "done" when the write-side beat counter reaches
        # this value, which is how poll_completion knows the DMA is over.
        self.setup_timer(test_data['total_bytes'])

        # 5. Kick channels
        t0 = time.time()
        self.kick_channels(test_data['kick_addresses'])

        # 6. Poll completion (TIMER_STATUS.done OR STATUS.any_error)
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

        # 6. CRC check (per-channel + aggregate)
        crc = self.read_crc(num_channels=config.num_channels)
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
        # Per-channel CRC visibility (multi-channel runs)
        if config.num_channels > 1:
            v_mask = crc.get('valid_mask', 0) or 0
            m_mask = crc.get('match_mask', 0) or 0
            for ch in range(config.num_channels):
                rd_v = (crc.get('rd_per_ch') or [None])[ch]
                wr_v = (crc.get('wr_per_ch') or [None])[ch]
                self.log(f"    ch{ch}: rd=0x{(rd_v or 0):08X} wr=0x{(wr_v or 0):08X} "
                         f"valid={(v_mask >> ch) & 1} match={(m_mask >> ch) & 1}")

        # 7. Methodology metrics (datapath / end-to-end / 4-bucket)
        metrics = self.read_run_metrics(num_channels=config.num_channels)
        result['metrics'] = metrics
        if metrics.get('available'):
            r_pct = metrics['datapath_utilization_r'] * 100
            w_pct = metrics['datapath_utilization_w'] * 100
            ee_pct = metrics['end_to_end_utilization'] * 100
            r_starv = metrics['r_buckets_pct']['starvation'] * 100
            w_starv = metrics['w_buckets_pct']['starvation'] * 100
            r_bp    = metrics['r_buckets_pct']['backpressure'] * 100
            w_bp    = metrics['w_buckets_pct']['backpressure'] * 100
            self.log(f"  Datapath util:  R={r_pct:5.1f}%  W={w_pct:5.1f}%  "
                     f"End-to-end={ee_pct:5.1f}%")
            self.log(f"  R bus: prod {r_pct:5.1f}%  bp {r_bp:4.1f}%  "
                     f"starv {r_starv:5.1f}%")
            self.log(f"  W bus: prod {w_pct:5.1f}%  bp {w_bp:4.1f}%  "
                     f"starv {w_starv:5.1f}%")
            # Flag per-channel overflows -- the 16-bit per-channel buckets
            # wrap at 65536 cycles (655 us). If any are set, the
            # per-channel numbers are unreliable for that channel.
            r_overflowed = [c['channel'] for c in metrics['r_per_channel']
                            if c['overflow_mask']]
            w_overflowed = [c['channel'] for c in metrics['w_per_channel']
                            if c['overflow_mask']]
            if r_overflowed or w_overflowed:
                self.log(f"  Per-channel 16-bit overflow: "
                         f"R={r_overflowed} W={w_overflowed} -- aggregate is "
                         f"authoritative for these channels")

        # 8. Trace summary
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
