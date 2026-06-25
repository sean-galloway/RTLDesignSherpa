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
sys.path.insert(0, str(script_dir))

import mon_configs as mon_cfg  # noqa: E402  (named monitor presets)

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
# Response-delay knob -- per-beat hold time injected on R and B channels
# by the axi_response_delay blocks. [15:0]=rd_delay, [31:16]=wr_delay,
# in aclk cycles. 0 = bypass.
CSR_RESP_DELAY      = HARNESS_CSR_BASE + 0x3C
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
# Kick-burst fast path. KICK_GO sits at 0xC0 (in the middle of the kick-addr
# slot range), so the per-channel kick-address slots are split into two banks:
#   ch 0..3 -> 0xB0/0xB4/0xB8/0xBC  (4-byte stride from 0xB0)
#   ch 4..7 -> 0xC4/0xC8/0xCC/0xD0  (4-byte stride from 0xC4)
# A naive `4*ch` stride hits 0xC0 for ch=4 and writes the kick address into
# KICK_GO -- it pulses a spurious kick for whichever channels the LSBs happen
# to encode and never delivers the real address for channels >= 4. Use the
# kick_addr_csr() helper below instead of the bare base + 4*ch.
CSR_KICK_GO            = HARNESS_CSR_BASE + 0xC0

def kick_addr_csr(ch: int) -> int:
    """CSR address for the per-channel kick-address shadow register.

    Skips the 0xC0 KICK_GO slot so the 8-channel layout is unambiguous.
    """
    if ch < 4:
        return HARNESS_CSR_BASE + 0xB0 + 4 * ch          # ch 0..3
    return HARNESS_CSR_BASE + 0xC4 + 4 * (ch - 4)        # ch 4..7
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

# (The harness axi_bus_meter readback bases at HARNESS_CSR_BASE + 0x100 / 0x180
#  were retired in RFC Stage E.4 -- datapath utilization is now read in-core via
#  the read_bus_meters shim over the STREAM perf CSRs.)

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

# Monitor configuration. The RDL default leaves PKT_MASK = 0xFFFF which
# DROPS every packet type at monbus entry -- so the trace SRAM stays
# empty and the whole monitor system is dark on every run unless we
# explicitly clear masks + enable the monitors. The cocotb TB does this
# (stream_char_tb.py); the runner missed it until now, which is why
# every prior FPGA sweep reported "Trace: 0 packets, overflow=no".
APB_DAXMON_ENABLE       = STREAM_APB_BASE + 0x240
APB_DAXMON_PKT_MASK     = STREAM_APB_BASE + 0x24C
APB_DAXMON_ERR_CFG      = STREAM_APB_BASE + 0x250
APB_RDMON_ENABLE        = STREAM_APB_BASE + 0x260
APB_RDMON_PKT_MASK      = STREAM_APB_BASE + 0x26C
APB_RDMON_ERR_CFG       = STREAM_APB_BASE + 0x270
APB_WRMON_ENABLE        = STREAM_APB_BASE + 0x280
APB_WRMON_PKT_MASK      = STREAM_APB_BASE + 0x28C
APB_WRMON_ERR_CFG       = STREAM_APB_BASE + 0x290

# WRMON_ENABLE.COMPRESS_EN (bit 5): 1 = compress the monbus write stream,
# 0 = raw 3-beat records. Only effective on a USE_MON_COMPRESSION=1 build.
WRMON_COMPRESS_EN_BIT   = 1 << 5

# MON_PKT_MASK: 1 = drop packet of that type at the monbus entry.
# 0x0000_FFF0 keeps Error (0), Completion (1), Threshold (2), Timeout (3)
# flowing and drops everything above. Mirrors stream_char_tb.MON_PKT_MASK_ALLOW_BASIC.
MON_PKT_MASK_ALLOW_BASIC = 0x0000_FFF0
# MON_ENABLE: bit 0 = ERR_EN, 1 = TIMEOUT_EN, 2 = COMPL_EN, 3 = THRESH_EN.
MON_ENABLE_COMPL_IRQ     = 0x0F
# MON_ERR_CFG.ERR_SELECT[15:0]: per-packet-type IRQ-vs-bulk route bit.
#   bit[type] = 1  -> packet of that type goes to the err FIFO IRQ path
#   bit[type] = 0  -> packet of that type goes to the bulk write FIFO,
#                      which drains via m_mon_axil into debug_sram
# Inside monbus_axil_axil_group these are *exclusive*:
#   pkt_to_write_fifo = !pkt_drop && !pkt_to_err_fifo
# so any type routed to the err FIFO is NOT also captured in debug_sram.
#
# We want every emitted packet captured in the bulk trace SRAM so the
# post-hang dump in run_config()._snapshot_on_hang() can show what the
# monitors saw before the wedge. The runner polls TIMER_STATUS.done for
# completion (not stream_irq), so silencing the IRQ path costs nothing.
# Was 0x0000_000F (Error / Completion / Threshold / Timeout -> IRQ
# path); now 0x0 so every type lands in debug_sram.
MON_ERR_CFG_BULK_TRACE   = 0x0000_0000


# =========================================================================
# Test execution
# =========================================================================

class CharacterizationRunner:
    """Runs characterization tests on the FPGA via UART."""

    def __init__(self, bridge, data_width: int = 128,
                 verbose: bool = False, mon_config: str = None,
                 poll_interval_s: float = 0.001,
                 aclk_hz: float = 100_000_000.0,
                 compression: bool = True):
        self.bridge = bridge
        self.builder = DescriptorBuilder(data_width=data_width)
        self.verbose = verbose
        self.results = []
        # Runtime monbus compression toggle. Drives WRMON_ENABLE.COMPRESS_EN
        # (bit 5) after the monitor cones are programmed. Only meaningful on
        # a USE_MON_COMPRESSION=1 bitstream (compressor hardware present);
        # harmless otherwise.
        self.compression = compression
        # Named monitor preset (mon_configs.CONFIGS) or None for the
        # legacy "allow basic types" programming.
        self.mon_config = mon_cfg.get(mon_config) if mon_config else None
        # poll_interval_s is the gap between TIMER_STATUS polls in the
        # host-side completion loop. Was hard-coded at 50 ms (5e-2),
        # which dominated dma_time_s for short transfers (a 1 MB DMA
        # finishes in <1 ms on the FPGA but the host only noticed on
        # the next 50 ms tick). 1 ms makes the host poll cadence
        # comparable to the UART round-trip cost and lets dma_time_s
        # actually track the FPGA work. The on-chip timer (cycles_total)
        # is now the authoritative bus-time source either way -- see
        # bus_time_s / bus_throughput_mbps emitted by run_config.
        self.poll_interval_s = poll_interval_s
        # AXI clock the on-chip timer counts on. Used to convert
        # cycles_total -> bus_time_s -> bus_throughput. Default 100 MHz
        # matches the stream_char bitstream's create_clock.
        self.aclk_hz = aclk_hz

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

    def cam_clear(self):
        """Synchronously clear ALL stream CAMs (CTRL[4]): the monbus compressor
        template CAM + its stat counters, and the monitor transaction CAMs.
        Use between compress runs (when idle) to reset compression statistics
        without a full soft-reset that would strand in-flight transactions."""
        self.bridge.write(CSR_CTRL, 0x10)  # cam_clear pulse (CTRL bit 4)
        time.sleep(0.01)

    def set_resp_delay(self, rd_cyc: int, wr_cyc: int) -> None:
        """Program the per-beat hold time injected by the harness's
        axi_response_delay blocks. rd_cyc applies to the R channel,
        wr_cyc to B. Both are clamped to 16 bits. 0 = bypass."""
        rd = rd_cyc & 0xFFFF
        wr = wr_cyc & 0xFFFF
        self.bridge.write(CSR_RESP_DELAY, (wr << 16) | rd)
        self.vlog(f"  RESP_DELAY = rd={rd}cyc wr={wr}cyc")

    def run_resp_delay_sweep(self, configs, rd_delays, wr_delays):
        """Run each config once per (rd_delay, wr_delay) pair, capturing
        the methodology metrics at each operating point. All runs share
        a single UART session.

        rd_delays / wr_delays must be the same length; index i pairs
        (rd_delays[i], wr_delays[i]) -- this lets callers sweep
        symmetric (rd=wr=N) curves OR asymmetric ones in the same call.

        Result schema:
            [{'rd_delay': N, 'wr_delay': N, 'config': name, 'result': {...}}, ...]
        """
        if not configs:
            return []
        if not self.ping():
            return [{'error': 'ping_failed'}]
        if len(rd_delays) != len(wr_delays):
            raise ValueError("rd_delays and wr_delays must have the same length")

        sweep_results = []
        for cfg in configs:
            for rd, wr in zip(rd_delays, wr_delays):
                self.log("")
                self.log(f"--- {cfg.name}  rd_delay={rd}  wr_delay={wr} ---")
                self.set_resp_delay(rd, wr)
                # Let the new delay propagate through the AXI pipeline
                # for a handful of aclk ticks before the next test starts.
                time.sleep(0.005)
                result = self.run_config(cfg)
                sweep_results.append({
                    'config': cfg.name,
                    'rd_delay': rd,
                    'wr_delay': wr,
                    'result': result,
                })
        return sweep_results

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

    def configure_stream(self, channels):
        """Full STREAM configuration — matches StreamHelper sequence.

        `channels` is the explicit list of physical channels to enable (e.g.
        [0,1,2] or [2,5,7]); the channel-enable mask is the OR of those bits.
        """
        # Scheduler config
        sched_cfg = 0x0F  # SCHED_EN + TIMEOUT_EN + ERR_EN + COMPL_EN
        self.bridge.write(APB_SCHED_CONFIG, sched_cfg)
        # SCHED_TIMEOUT_CYCLES is a 32-bit field. The earlier 0x0FFFFFFF
        # (28-bit = ~2.68 s) was too tight for deep descriptor chains
        # (16 desc x 1 MB) -- every such config in the matrix timed out
        # because cumulative inter-descriptor stall exceeded the budget on
        # at least one channel. Bump to the field maximum (~42.9 s @ 100 MHz)
        # so the scheduler doesn't bail before the chain naturally completes.
        self.bridge.write(APB_SCHED_TIMEOUT_CYC, 0xFFFFFFFF)  # 32-bit max, ~42.9s @ 100MHz

        # Descriptor engine config
        self.bridge.write(APB_DESCENG_CONFIG, 0x01)  # DESCENG_EN

        # Address ranges (full 32-bit space)
        self.bridge.write(APB_DESCENG_ADDR0_BASE,  0x0000_0000)
        self.bridge.write(APB_DESCENG_ADDR0_LIMIT, 0xFFFF_FFFF)
        self.bridge.write(APB_DESCENG_ADDR1_BASE,  0x0000_0000)
        self.bridge.write(APB_DESCENG_ADDR1_LIMIT, 0xFFFF_FFFF)

        # AXI burst config: ARLEN (beats-1) for rd [7:0] and wr [15:8]. This is
        # the size of an INDIVIDUAL AXI transaction (the rd/wr xfer-beats config
        # bits), default 16 beats (256 B). Swept via XFER_BEATS / XFER_BEATS_RD /
        # XFER_BEATS_WR to characterize per-transaction datapath util vs burst
        # size (1 KB = 64 beats down to a single beat).
        import os as _os
        _rb = int(_os.environ.get('XFER_BEATS_RD', _os.environ.get('XFER_BEATS', '16')))
        _wb = int(_os.environ.get('XFER_BEATS_WR', _os.environ.get('XFER_BEATS', '16')))
        axi_cfg = ((_rb - 1) & 0xFF) | (((_wb - 1) & 0xFF) << 8)
        self.bridge.write(APB_AXI_XFER_CONFIG, axi_cfg)

        # Unblock the monbus monitors so packets actually flow out into
        # debug_sram (and the err FIFO IRQ path). RDL default leaves
        # PKT_MASK = 0xFFFF which silently drops every packet at monbus
        # entry; without clearing it the trace SRAM stays empty and we
        # get zero observability when something hangs. Mirror the TB's
        # sequence in stream_char_tb.run_dma_test step 3e.
        if self.mon_config is not None:
            # Named preset (perf-mon / debug-*): programs ENABLE +
            # PKT_MASK + every event-code mask on all three monitors.
            self.mon_config.apply(self.bridge.write)
            tag = " (compressed build expected)" if self.mon_config.compress else ""
            self.vlog(f"  monitors: '{self.mon_config.name}' preset "
                      f"[{', '.join(self.mon_config.cones)}]{tag}")
        else:
            # Legacy default: allow the basic packet types, route all to
            # the bulk-trace SRAM. (Event-code masks left at reset.)
            for pkt_mask_reg, en_reg, err_reg in (
                (APB_DAXMON_PKT_MASK, APB_DAXMON_ENABLE, APB_DAXMON_ERR_CFG),
                (APB_RDMON_PKT_MASK,  APB_RDMON_ENABLE,  APB_RDMON_ERR_CFG),
                (APB_WRMON_PKT_MASK,  APB_WRMON_ENABLE,  APB_WRMON_ERR_CFG),
            ):
                self.bridge.write(pkt_mask_reg, MON_PKT_MASK_ALLOW_BASIC)
                self.bridge.write(en_reg,       MON_ENABLE_COMPL_IRQ)
                self.bridge.write(err_reg,      MON_ERR_CFG_BULK_TRACE)

        # Runtime compression toggle. Done LAST because the cone-enable
        # writes above land in the same WRMON_ENABLE register and would
        # otherwise clobber COMPRESS_EN. Read-modify-write bit 5.
        wrmon_en = self.bridge.read(APB_WRMON_ENABLE) or 0
        if self.compression:
            wrmon_en |= WRMON_COMPRESS_EN_BIT
        else:
            wrmon_en &= ~WRMON_COMPRESS_EN_BIT
        self.bridge.write(APB_WRMON_ENABLE, wrmon_en)
        self.vlog(f"  monbus compression: {'ON' if self.compression else 'OFF'} "
                  f"(WRMON_ENABLE=0x{wrmon_en:02X})")

        # Global enable + channels. The mask is the OR of the selected physical
        # channels (contiguous 0..N-1 by default, or an explicit subset).
        self.bridge.write(APB_GLOBAL_CTRL, 0x01)
        ch_mask = 0
        for ch in channels:
            ch_mask |= (1 << ch)
        self.bridge.write(APB_CHANNEL_ENABLE, ch_mask)
        self.vlog(f"  STREAM configured: sched=0x{sched_cfg:02X}, "
                  f"desceng=0x01, axi=0x{axi_cfg:04X}, ch_mask=0x{ch_mask:02X} "
                  f"(channels {channels})")

    def kick_channels(self, kick_addresses: dict):
        """Kick-burst fast path: pre-load per-channel addresses into the
        harness CSR shadow registers, then fire a single KICK_GO write
        with a channel bitmask. The harness pulses every kick line on the
        same aclk cycle, so multi-channel runs actually pipeline instead
        of serializing on the slow UART that the legacy per-channel APB
        kick path needed (~2 ms / write at 115200 baud)."""
        mask = 0
        for ch, axi4_addr in sorted(kick_addresses.items()):
            self.bridge.write(kick_addr_csr(ch),
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
        """Snapshot timer + in-core datapath monitor state after the run.

        Sources the datapath buckets from the in-core STREAM perf monitors
        (RFC Stage E option 2) via the read_bus_meters compatibility shim --
        the legacy harness axi_bus_meter was retired in Stage E.4. The perf
        windows were opened before the kick and closed the instant the workload
        completed (see run_config), so the in-core bucket sum brackets the burst
        and, for real workloads, matches the harness timer's first/last span.

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

        # In-core monitor snapshots (aggregate + per-channel for both sides),
        # read through the legacy meter-compatible shim.
        rd_meter = read_meter(self.bridge, R_METER_BASE, num_channels, 'R')
        wr_meter = read_meter(self.bridge, W_METER_BASE, num_channels, 'W')

        # First/last beat windows from the harness timer (methodology
        # Section 2.1, expressed in aclk cycles). Reported alongside the
        # bucket math so the JSON record preserves the precise burst span.
        r_firstlast = (r_last - r_first + 1) if r_last >= r_first and r_last > 0 else 0
        w_firstlast = (w_last - w_first + 1) if w_last >= w_first and w_last > 0 else 0

        # Window = sum of all four buckets. The in-core monitor accumulates
        # only while RDMON/WRMON_PERF_CTRL.RUN=1 (opened before kick, closed at
        # completion), so the bucket sum brackets the burst; dividing productive
        # by it yields the methodology datapath number. Falls back to the timer
        # first/last span if the bucket sum is zero (a workload that never
        # produced a beat). For an exact methodology denominator the timer's
        # first/last span (r_firstlast / w_firstlast) is reported alongside.
        def window_of(meter):
            agg = meter.aggregate
            s = agg.productive + agg.backpressure + agg.starvation + agg.idle
            return s if s > 0 else 0

        r_window = window_of(rd_meter) or r_firstlast
        w_window = window_of(wr_meter) or w_firstlast

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
            'r_first': r_first, 'r_last': r_last,
            'r_window_cycles': r_window,
            'r_firstlast_cycles': r_firstlast,
            'w_first': w_first, 'w_last': w_last,
            'w_window_cycles': w_window,
            'w_firstlast_cycles': w_firstlast,
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
        next_progress = 5.0   # PROGRESS_DEBUG: first heartbeat at 5 s
        while (time.time() - start) < timeout_s:
            ts = self.bridge.read(CSR_TIMER_STATUS)
            st = self.bridge.read(CSR_STATUS)
            if ts is None or st is None:
                time.sleep(0.1)
                continue

            # PROGRESS_DEBUG: periodic heartbeat to tell a true deadlock
            # (frozen R_LAST/W_LAST) from a severe throttle (advancing). The
            # *_LAST regs hold the aclk cycle of the most recent R/W beat.
            elapsed_now = time.time() - start
            if elapsed_now >= next_progress:
                def _rd64(lo, hi):
                    l = self.bridge.read(lo) or 0
                    h = self.bridge.read(hi) or 0
                    return (h << 32) | (l & 0xFFFFFFFF)
                r_last = _rd64(CSR_TIMER_R_LAST_LO, CSR_TIMER_R_LAST_HI)
                w_last = _rd64(CSR_TIMER_W_LAST_LO, CSR_TIMER_W_LAST_HI)
                cyc    = _rd64(CSR_TIMER_CYCLES_LO, CSR_TIMER_CYCLES_HI)
                # vlog = verbose-only: a frozen r_last/w_last while timer_cyc
                # advances is a hard deadlock (zero beats); advancing *_last is
                # a throttle. Diagnostic for the debug-compl 4-7ch hang.
                self.vlog(f"  [progress {elapsed_now:5.1f}s] timer_cyc={cyc} "
                          f"r_last_beat_cyc={r_last} w_last_beat_cyc={w_last} "
                          f"running={bool(ts & 0x02)} done={bool(ts & 0x01)}")
                next_progress += 5.0

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
            time.sleep(self.poll_interval_s)

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

    # ------------------------------------------------------------------
    # Post-hang diagnostic snapshot. Called by run_config() on TIMEOUT.
    # Pulls every STREAM idle/error register the harness can see, plus
    # a head/tail of the monbus trace SRAM so we can read the last
    # packets the monitors emitted before the wedge.
    # ------------------------------------------------------------------
    DEBUG_SRAM_BASE_HOST = 0x0004_0000  # see stream_char_harness.sv address map

    # Per-monitor "monitor still alive" + sticky-state registers. The
    # field block in stream_regs.rdl exposes each engine's outstanding /
    # transaction-count / state-machine snapshots over the APB; reading
    # them on a TIMEOUT tells us which engine got stuck and where.
    _STREAM_STATUS_REGS = [
        ("GLOBAL_STATUS",     STREAM_APB_BASE + 0x104),
        ("CHANNEL_ENABLE",    STREAM_APB_BASE + 0x120),
        ("CHANNEL_IDLE",      STREAM_APB_BASE + 0x140),
        ("DESC_ENGINE_IDLE",  STREAM_APB_BASE + 0x144),
        ("SCHEDULER_IDLE",    STREAM_APB_BASE + 0x148),
        ("AXI_RD_COMPLETE",   STREAM_APB_BASE + 0x174),
        ("AXI_WR_COMPLETE",   STREAM_APB_BASE + 0x178),
        ("SCHED_ERROR",       STREAM_APB_BASE + 0x170),
    ]

    def _snapshot_on_hang(self, result: dict) -> None:
        """Dump everything we can read after a TIMEOUT.

        Records (into result['hang_snapshot']) the STREAM idle/error
        regs, the harness trace counters (wr_ptr / overflow), and a head
        + tail block of the debug_sram raw 32-bit words so we can decode
        the last monbus packets the monitors emitted before the wedge.
        """
        snap: dict = {'stream_regs': {}, 'trace': {}, 'sram_head': [],
                      'sram_tail': []}

        # 1. STREAM idle/error registers
        self.log("  --- Hang snapshot: STREAM status ---")
        for name, addr in self._STREAM_STATUS_REGS:
            val = self.bridge.read(addr)
            snap['stream_regs'][name] = val
            self.log(f"    {name:18s} @ 0x{addr:04X} = "
                     f"{'0x%08X' % val if val is not None else 'READ_FAIL'}")

        # 2. Trace SRAM counters
        trace = self.read_trace_summary()
        snap['trace'] = trace
        self.log(f"  --- Trace counters: wr_ptr={trace['wr_ptr']} "
                 f"overflow={trace['overflow']} ---")

        # 3. Head / tail of the SRAM. The monbus_axil_axil_group writes 32-bit
        # words sequentially; wr_ptr counts WORDS (not bytes). Each
        # monitor record is 3 words: pkt[31:0], pkt[63:32], timestamp[31:0]
        # (plus another 3 for the 128-bit upper half + timestamp[63:32]
        # depending on the group config) -- the offline parser in
        # host/dump_monbus_sram.py knows the format; for the snapshot we
        # just grab raw words so we have something to feed it.
        wr_ptr = trace.get('wr_ptr') or 0
        head_count = min(48, wr_ptr)
        tail_start_words = max(wr_ptr - 48, 0)
        tail_count = min(48, wr_ptr - tail_start_words)

        for i in range(head_count):
            v = self.bridge.read(self.DEBUG_SRAM_BASE_HOST + 4 * i)
            snap['sram_head'].append(v)
        for i in range(tail_count):
            v = self.bridge.read(self.DEBUG_SRAM_BASE_HOST
                                 + 4 * (tail_start_words + i))
            snap['sram_tail'].append(v)

        if snap['sram_head']:
            self.log("  --- SRAM head (first 48 words) ---")
            for j in range(0, len(snap['sram_head']), 8):
                row = snap['sram_head'][j:j + 8]
                self.log("    " + " ".join(
                    f"{(w if w is not None else 0):08x}" for w in row))
        if snap['sram_tail'] and tail_start_words > head_count:
            self.log(f"  --- SRAM tail (words {tail_start_words}..{wr_ptr - 1}) ---")
            for j in range(0, len(snap['sram_tail']), 8):
                row = snap['sram_tail'][j:j + 8]
                self.log("    " + " ".join(
                    f"{(w if w is not None else 0):08x}" for w in row))

        result['hang_snapshot'] = snap

    def reset_stream(self):
        """Soft-reset the whole DMA+harness unit.

        Writes CSR_CTRL[3] = 1 to fire the harness-side soft-reset pulse,
        which the harness pulse-extends into ~16 clocks of reset on the
        unit_aresetn line. That line fans out to u_stream, u_desc_ram,
        u_debug_sram, u_rd_pattern, u_wr_crc_check, u_rd_resp_delay,
        u_wr_resp_delay -- i.e. every block whose internal state might
        wedge across matrix configs. (The harness axi_bus_meter blocks
        were retired in RFC Stage E.4.)
        u_csr (harness CSR), u_uart, and u_bridge intentionally stay on
        hardware aresetn so the soft reset can't break the host
        connection or self-terminate the very pulse driving it.

        Was: APB_GLOBAL_CTRL bit 1 (STREAM's GLOBAL_RST). That bit only
        resets per-channel state inside STREAM; it does not reset the
        monitors, the SRAM controller, or any harness sub-block.
        """
        self.bridge.write(CSR_CTRL, 0x08)   # bit 3 = soft_reset_pulse
        time.sleep(0.05)

    # -----------------------------------------------------------------
    # Run a single configuration
    # -----------------------------------------------------------------

    def run_config(self, config: CharConfig) -> dict:
        """
        Execute one characterization configuration.

        Returns result dict with pass/fail, CRC, timing, etc.
        """
        channels = config.channel_list()
        # Per-channel HW arrays (CRC, meters) are indexed by physical channel,
        # so read enough slots to cover the highest selected channel. For the
        # default contiguous 0..N-1 selection this equals num_channels, leaving
        # existing behaviour and the record format unchanged.
        slot_count = max(channels) + 1
        ch_str = "" if channels == list(range(config.num_channels)) else f" {channels}"
        self.log(f"--- {config.name}: {config.num_channels}ch x "
                 f"{config.descriptors_per_channel}desc x "
                 f"{config.transfer_bytes // 1024}KB{ch_str} ---")

        test_data = self.builder.build_test(config)
        result = {
            'name': config.name,
            'num_channels': config.num_channels,
            'channels': channels,  # physical channels exercised (default 0..N-1)
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
        self.configure_stream(channels)

        # 4. Arm the harness timer with the expected sink-side beat count.
        # The timer fires "done" when the write-side beat counter reaches
        # this value, which is how poll_completion knows the DMA is over.
        self.setup_timer(test_data['total_bytes'])

        # 4b. Open the in-core datapath perf windows (RFC Stage E option 2).
        # They accumulate cycle buckets / beat-byte-burst counts / latency
        # histograms while RDMON/WRMON_PERF_CTRL.RUN=1; the rising edge clears
        # the counters. We open here (just before kick) and close the instant
        # the workload completes (below) so the window brackets the burst. The
        # legacy harness axi_bus_meter (which hardware-froze on the timer) was
        # retired in Stage E.4; this is its in-core replacement.
        try:
            from read_rw_perf import open_windows as _open_perf_windows
            _open_perf_windows(self.bridge)
        except ImportError:
            pass

        # 5. Kick channels
        t0 = time.time()
        self.kick_channels(test_data['kick_addresses'])

        # 6. Poll completion (TIMER_STATUS.done OR STATUS.any_error). 120 s
        # is the host wall-clock budget; deep-chain configs (16 desc per
        # channel) need more than the prior 60 s, especially when paired
        # with high channel count -- 16 desc x 8 ch x 1 MB = 128 MB total,
        # which at observed ~250 MB/s aggregate wall throughput is ~0.5 s
        # of DMA but several seconds of host-side per-channel overhead.
        # DIAG: if DIAG_NO_POLL_MS is set, sleep with ZERO UART traffic instead
        # of hammering the xbar with poll reads. If the perf window then reads
        # tight (high util), the host's poll traffic was starving the datapath
        # (not a scheduler_idle bug); if still loose, the datapath genuinely
        # lingers.
        _diag_ms = float(os.environ.get('DIAG_NO_POLL_MS', '0') or 0)
        if _diag_ms > 0:
            time.sleep(_diag_ms / 1000.0)
            completion = {'completed': True, 'elapsed_s': _diag_ms / 1000.0,
                          'error': False, 'diag_no_poll': True}
        else:
            completion = self.poll_completion(timeout_s=120.0)
        result['dma_time_s'] = time.time() - t0
        result['completion'] = completion

        # DIAGNOSTIC: read RDMON/WRMON_PERF_STATUS.WIN_ACTIVE with RUN still
        # HIGH. With the hardware-close window this should already be 0 (the
        # window auto-closed when the datapath went idle); if it reads 1 the
        # auto-close did not fire and the buckets are contaminated.
        try:
            rd_wa = self.bridge.read(STREAM_APB_BASE + 0x304) & 0x1
            wr_wa = self.bridge.read(STREAM_APB_BASE + 0x334) & 0x1
            self.log(f"  [perf-window] WIN_ACTIVE (RUN still high): "
                     f"RD={rd_wa} WR={wr_wa} (0 = auto-closed in hardware)")
        except Exception as _e:
            pass

        # Close the in-core perf windows ASAP after completion -- before the
        # slow CRC/UART readback below -- so post-burst idle cycles don't
        # contaminate the buckets. (For real characterization workloads the
        # done-detect-to-close gap is negligible vs the multi-ms transfer;
        # datapath_utilization additionally uses the harness timer's exact
        # first/last beat span as the methodology denominator.)
        try:
            from read_rw_perf import close_windows as _close_perf_windows
            _close_perf_windows(self.bridge)
        except ImportError:
            pass

        if not completion.get('completed'):
            self.log(f"  TIMEOUT after {completion['elapsed_s']:.1f}s")
            # Snapshot monitor + STREAM diagnostic state at the moment of
            # wedge. The monbus trace SRAM has every packet the monitors
            # emitted up to the hang -- if a Threshold / Timeout / Error
            # packet fired before the wedge it's in here. We also pull
            # the STREAM idle/error registers so we can see which engine
            # or scheduler is in a bad state.
            self._snapshot_on_hang(result)
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
        crc = self.read_crc(num_channels=slot_count)
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
            for ch in channels:
                rd_v = (crc.get('rd_per_ch') or [None])[ch]
                wr_v = (crc.get('wr_per_ch') or [None])[ch]
                self.log(f"    ch{ch}: rd=0x{(rd_v or 0):08X} wr=0x{(wr_v or 0):08X} "
                         f"valid={(v_mask >> ch) & 1} match={(m_mask >> ch) & 1}")

        # 7. Methodology metrics (datapath / end-to-end / 4-bucket)
        metrics = self.read_run_metrics(num_channels=slot_count)
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
        #
        # Two numbers, on purpose:
        #
        #   throughput_mbps        -- host wall clock (dma_time_s).
        #                             Includes UART CSR round-trips and
        #                             the poll-loop cadence. Useful for
        #                             "how long did the whole DMA take
        #                             end-to-end including the host"
        #                             but NOT a bus-efficiency metric.
        #
        #   bus_throughput_mbps    -- FPGA on-chip timer (cycles_total
        #                             at aclk_hz). No host overhead.
        #                             This is what the AXI engine
        #                             actually sustained on the bus.
        #
        # The bus number is the right one to quote when characterizing
        # the engine. The wall number stays in the record for
        # transparency / debugging.
        if result['dma_time_s'] > 0:
            mbps = (result['total_bytes'] / (1024 * 1024)) / result['dma_time_s']
            result['throughput_mbps'] = mbps
            self.log(f"  Wall throughput: {mbps:.1f} MB/s "
                     f"({result['total_bytes'] / (1024*1024):.0f} MB in "
                     f"{result['dma_time_s']:.3f}s; includes UART overhead)")

        # Bus-side throughput from the on-chip timer (cycles_total).
        # End-to-end util comes from read_run_metrics already; we just
        # surface it onto the top-level result so the CSV exporter has
        # a single place to grab it.
        if metrics.get('available'):
            cycles_total = metrics.get('cycles_total', 0) or 0
            if cycles_total > 0 and self.aclk_hz > 0:
                bus_time_s = cycles_total / self.aclk_hz
                bus_mbps   = (result['total_bytes'] / (1024 * 1024)) / bus_time_s
                result['bus_time_s']         = bus_time_s
                result['bus_throughput_mbps'] = bus_mbps
                result['bus_cycles_total']    = cycles_total
                result['bus_e2e_util_pct']   = metrics['end_to_end_utilization'] * 100
                # Theoretical single-bus ceiling at this clock + bus
                # width: aclk * data_width_bytes. The DMA reads then
                # writes each byte, so the practical net-bytes-moved
                # ceiling is half that.
                bus_max_one_dir = self.aclk_hz * DATA_WIDTH_BYTES / (1024 * 1024)
                result['bus_max_one_dir_mbps']    = bus_max_one_dir
                result['bus_max_net_moved_mbps']  = bus_max_one_dir / 2
                self.log(f"  Bus  throughput: {bus_mbps:.1f} MB/s "
                         f"(FPGA timer {bus_time_s*1e3:.3f} ms; "
                         f"E2E util {result['bus_e2e_util_pct']:.1f}%; "
                         f"ceiling {result['bus_max_net_moved_mbps']:.0f} MB/s "
                         f"net-moved at {self.aclk_hz/1e6:.0f} MHz)")

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
    parser.add_argument('--mon-config', dest='mon_config',
                        choices=sorted(mon_cfg.CONFIGS),
                        help='Named monitor preset to program before the run '
                             '(perf-mon = perf only, low rate; debug-* = '
                             'richer mixes, high traffic / compressed build). '
                             'Default: legacy "allow basic types".')
    parser.add_argument('--compression', dest='compression',
                        choices=['on', 'off'], default='on',
                        help='Runtime monbus compression (WRMON_ENABLE.COMPRESS_EN). '
                             'on=compress the bulk-trace stream, off=raw 3-beat '
                             'records. Only effective on a USE_MON_COMPRESSION=1 '
                             'bitstream. Default: on.')
    parser.add_argument('--phase', type=int, choices=[1, 2],
                        help='Run only phase 1 or phase 2')
    parser.add_argument('--configs', nargs='+',
                        help='Run only named configs (e.g., 1desc_1ch 4desc_8ch)')
    parser.add_argument('--channels', type=int, nargs='+',
                        help='Limit to specific channel counts (e.g., 1 4 8)')
    parser.add_argument('--channel-list', dest='channel_list', type=int, nargs='+',
                        default=None,
                        help='Select which PHYSICAL channels to enable, e.g. '
                             '"--channel-list 2 5 7". Default is the contiguous '
                             'block 0..N-1. Selects matrix/CSV configs whose '
                             'channel count equals len(list) and maps them onto '
                             'these channels. Indices 0..7.')
    parser.add_argument('--channel-mask', dest='channel_mask',
                        type=lambda s: int(s, 0), default=None,
                        help='Same as --channel-list but as a bitmask, e.g. '
                             '"--channel-mask 0xA4" -> channels [2,5,7]. '
                             'Mutually exclusive with --channel-list.')
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

    # On-chip / host clock plumbing. poll_interval_ms used to be fixed
    # at 50 ms which dominated dma_time_s for short transfers; 1 ms
    # default lets dma_time_s actually track the FPGA work, and the
    # on-chip timer (cycles_total) is the authoritative bus-time source
    # anyway.
    parser.add_argument('--poll-interval-ms', type=float, default=1.0,
                        help='Sleep between TIMER_STATUS polls in the '
                             'host completion loop (default 1.0 ms; '
                             'was 50 ms historically and polluted '
                             'short-transfer wall-clock throughput).')
    parser.add_argument('--aclk-mhz', type=float, default=100.0,
                        help='AXI clock the on-chip timer counts on, '
                             'in MHz (default 100). Used to convert '
                             'cycles_total -> bus_time_s for the bus-'
                             'side throughput metric.')

    # Response-delay sweep mode (methodology Section 6, "backpressure
    # profile" axis). When --resp-delays is set, the listed configs are
    # each run once per delay value; rd_delay = wr_delay for each entry
    # unless --asymmetric-resp-delays is also given (then rd and wr are
    # paired by position).
    parser.add_argument('--resp-delays', type=str, default=None,
                        help='Comma-separated list of resp-delay values '
                             'in aclk cycles, e.g. "0,1,2,4,8,16,32,64" '
                             '(0 = bypass). Each --configs run is '
                             'repeated once per delay.')
    parser.add_argument('--resp-delays-wr', type=str, default=None,
                        help='Optional companion to --resp-delays for '
                             'asymmetric sweeps. Must have the same '
                             'length. If unset, wr_delay = rd_delay for '
                             'each pair.')
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

    # Explicit physical-channel selection (applies to CSV and matrix configs).
    # --channel-mask and --channel-list are two spellings of the same thing.
    chan_sel = None
    if args.channel_mask is not None and args.channel_list is not None:
        print("Use only one of --channel-mask / --channel-list.")
        return 1
    if args.channel_mask is not None:
        chan_sel = [i for i in range(8) if (args.channel_mask >> i) & 1]
    elif args.channel_list is not None:
        chan_sel = sorted(set(args.channel_list))
    if chan_sel is not None:
        if not chan_sel or any(c < 0 or c > 7 for c in chan_sel):
            print(f"--channel-list/-mask must select channels in 0..7 (got {chan_sel}).")
            return 1
        # Map the chosen physical channels onto configs whose active-channel
        # count matches; their descriptors/kicks/enable mask then target exactly
        # these channels instead of the default 0..N-1 block.
        matched = [c for c in configs if c.num_channels == len(chan_sel)]
        if not matched:
            print(f"No {len(chan_sel)}-channel config to map onto channels "
                  f"{chan_sel}. Pick a config/phase with {len(chan_sel)} "
                  f"channel(s), or change the selection width.")
            return 1
        for c in matched:
            c.channels = list(chan_sel)
        configs = matched
        print(f"Channel selection: running {len(configs)} config(s) on physical "
              f"channels {chan_sel}")

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
            bridge, data_width=128, verbose=args.verbose,
            mon_config=args.mon_config,
            poll_interval_s=args.poll_interval_ms / 1000.0,
            aclk_hz=args.aclk_mhz * 1_000_000.0,
            compression=(args.compression == 'on'))
        if args.resp_delays:
            rd = [int(s, 0) for s in args.resp_delays.split(',') if s.strip()]
            if args.resp_delays_wr:
                wr = [int(s, 0) for s in args.resp_delays_wr.split(',') if s.strip()]
            else:
                wr = list(rd)
            print(f"\n=== RESP_DELAY sweep: {len(rd)} points x "
                  f"{len(configs)} configs = {len(rd)*len(configs)} runs ===\n")
            results = runner.run_resp_delay_sweep(configs, rd, wr)
        else:
            results = runner.run_matrix(configs)

    # Save results
    if args.output and results:
        with open(args.output, 'w') as f:
            json.dump(results, f, indent=2, default=str)
        print(f"\nResults saved to {args.output}")

    # Exit code: 0 if all passed (for sweep mode, pass is on the inner result)
    def _pass(r):
        if 'result' in r:
            return r['result'].get('pass', False)
        return r.get('pass', False)
    all_pass = all(_pass(r) for r in results) if results else False
    return 0 if all_pass else 1


if __name__ == '__main__':
    sys.exit(main())
