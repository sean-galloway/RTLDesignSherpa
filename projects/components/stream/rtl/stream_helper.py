# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# StreamHelper - High-level configuration API for STREAM DMA engine
# Follows HPETHelper pattern for consistency with RLB methodology

"""
StreamHelper - STREAM DMA Configuration Helper

Provides human-readable API on top of the RegisterMap class for
configuring stream_top. Following the HPET methodology pattern.

Usage:
    from stream_helper import StreamHelper

    # Create helper
    helper = StreamHelper(log=logger)

    # Configure STREAM
    helper.enable_global(True)
    helper.enable_channels(0xFF)  # All 8 channels
    helper.kick_off_channel(0, 0x8000_0000)  # Start channel 0

    # Generate APB cycles for all pending writes
    apb_cycles = helper.generate_apb_cycles()

    # Send to DUT via APB master
    for pkt in apb_cycles:
        await apb_master.send(pkt)
"""

import os
import sys

# Add repo root to path for imports
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../..'))
if repo_root not in sys.path:
    sys.path.insert(0, repo_root)

from projects.components.stream.rtl.stream_regmap import (
    top_block,
    get_ch_ctrl_low_addr, get_ch_ctrl_high_addr, get_ch_state_addr,
    ADDR_GLOBAL_CTRL, ADDR_GLOBAL_STATUS, ADDR_VERSION,
    ADDR_CHANNEL_ENABLE, ADDR_CHANNEL_RESET,
    ADDR_CHANNEL_IDLE, ADDR_DESC_ENGINE_IDLE, ADDR_SCHEDULER_IDLE,
    ADDR_SCHED_ERROR, ADDR_AXI_RD_COMPLETE, ADDR_AXI_WR_COMPLETE,
    ADDR_MON_FIFO_STATUS, ADDR_MON_FIFO_COUNT,
    ADDR_SCHED_TIMEOUT_CYCLES, ADDR_SCHED_CONFIG,
    ADDR_DESCENG_CONFIG, ADDR_DESCENG_ADDR0_BASE, ADDR_DESCENG_ADDR0_LIMIT,
    ADDR_DESCENG_ADDR1_BASE, ADDR_DESCENG_ADDR1_LIMIT,
    ADDR_AXI_XFER_CONFIG, ADDR_PERF_CONFIG
)


class StreamHelper:
    """
    High-level configuration helper for STREAM DMA engine.

    Provides human-readable methods for configuring stream_top via APB.
    Accumulates writes and generates APB packets for batch sending.

    Following HPET methodology for consistent register configuration.
    """

    NUM_CHANNELS = 8

    def __init__(self, log=None):
        """
        Initialize StreamHelper.

        Args:
            log: CocoTB logger (optional, for debug output)
        """
        self.log = log
        self._pending_writes = []  # List of (addr, data) tuples
        self._state = {}  # Track current register values

    # =========================================================================
    # APB Packet Generation
    # =========================================================================

    def generate_apb_cycles(self):
        """
        Generate APB write packets for all pending writes.

        Returns:
            List of (address, data) tuples for APB writes
        """
        cycles = list(self._pending_writes)
        self._pending_writes.clear()
        return cycles

    def clear_pending(self):
        """Clear any pending writes without generating packets."""
        self._pending_writes.clear()

    def _add_write(self, addr, data):
        """Add a write to pending queue."""
        self._pending_writes.append((addr, data))
        self._state[addr] = data
        if self.log:
            self.log.debug(f"StreamHelper: Queue write @ 0x{addr:03X} = 0x{data:08X}")

    # =========================================================================
    # Global Control
    # =========================================================================

    def enable_global(self, enable=True):
        """
        Enable or disable STREAM engine globally.

        Args:
            enable: True to enable, False to disable
        """
        value = 0x1 if enable else 0x0
        self._add_write(ADDR_GLOBAL_CTRL, value)

    def reset_global(self):
        """Assert global reset (self-clearing)."""
        self._add_write(ADDR_GLOBAL_CTRL, 0x2)  # Bit 1 = global_rst

    def enable_and_configure(self, channel_mask=0xFF):
        """
        Standard initialization: enable global and specified channels.

        Args:
            channel_mask: 8-bit mask of channels to enable (default: all)
        """
        self.enable_global(True)
        self.enable_channels(channel_mask)

    # =========================================================================
    # Channel Control
    # =========================================================================

    def enable_channels(self, channel_mask):
        """
        Enable specified channels.

        Args:
            channel_mask: 8-bit mask (bit N = channel N enable)
        """
        self._add_write(ADDR_CHANNEL_ENABLE, channel_mask & 0xFF)

    def enable_channel(self, channel):
        """
        Enable a single channel.

        Args:
            channel: Channel number (0-7)
        """
        if channel < 0 or channel >= self.NUM_CHANNELS:
            raise ValueError(f"Channel {channel} out of range (0-7)")

        # Read current value, set bit
        current = self._state.get(ADDR_CHANNEL_ENABLE, 0)
        new_value = current | (1 << channel)
        self._add_write(ADDR_CHANNEL_ENABLE, new_value)

    def disable_channel(self, channel):
        """
        Disable a single channel.

        Args:
            channel: Channel number (0-7)
        """
        if channel < 0 or channel >= self.NUM_CHANNELS:
            raise ValueError(f"Channel {channel} out of range (0-7)")

        # Read current value, clear bit
        current = self._state.get(ADDR_CHANNEL_ENABLE, 0)
        new_value = current & ~(1 << channel)
        self._add_write(ADDR_CHANNEL_ENABLE, new_value)

    def reset_channel(self, channel):
        """
        Reset a single channel (self-clearing).

        Args:
            channel: Channel number (0-7)
        """
        if channel < 0 or channel >= self.NUM_CHANNELS:
            raise ValueError(f"Channel {channel} out of range (0-7)")

        self._add_write(ADDR_CHANNEL_RESET, 1 << channel)

    def reset_channels(self, channel_mask):
        """
        Reset specified channels.

        Args:
            channel_mask: 8-bit mask of channels to reset
        """
        self._add_write(ADDR_CHANNEL_RESET, channel_mask & 0xFF)

    # =========================================================================
    # Channel Kick-off (Descriptor Start)
    # =========================================================================

    def kick_off_channel(self, channel, desc_addr):
        """
        Kick off a channel by writing descriptor address.

        This writes to the CHx_CTRL_LOW and CHx_CTRL_HIGH registers
        which triggers descriptor fetch via apbtodescr.sv.

        Args:
            channel: Channel number (0-7)
            desc_addr: 64-bit descriptor address
        """
        if channel < 0 or channel >= self.NUM_CHANNELS:
            raise ValueError(f"Channel {channel} out of range (0-7)")

        addr_low = get_ch_ctrl_low_addr(channel)
        addr_high = get_ch_ctrl_high_addr(channel)

        self._add_write(addr_low, desc_addr & 0xFFFFFFFF)
        self._add_write(addr_high, (desc_addr >> 32) & 0xFFFFFFFF)

    def kick_off_channels(self, channel_desc_pairs):
        """
        Kick off multiple channels.

        Args:
            channel_desc_pairs: List of (channel, desc_addr) tuples
        """
        for channel, desc_addr in channel_desc_pairs:
            self.kick_off_channel(channel, desc_addr)

    # =========================================================================
    # Scheduler Configuration
    # =========================================================================

    def configure_scheduler(self, enable=True, timeout_en=True, err_en=True,
                            compl_en=True, perf_en=False):
        """
        Configure scheduler features.

        Args:
            enable: Master scheduler enable
            timeout_en: Enable timeout detection
            err_en: Enable error reporting
            compl_en: Enable completion reporting
            perf_en: Enable performance monitoring
        """
        value = (
            (1 if enable else 0) |
            (1 if timeout_en else 0) << 1 |
            (1 if err_en else 0) << 2 |
            (1 if compl_en else 0) << 3 |
            (1 if perf_en else 0) << 4
        )
        self._add_write(ADDR_SCHED_CONFIG, value)

    def set_scheduler_timeout(self, cycles):
        """
        Set scheduler timeout threshold.

        Args:
            cycles: Timeout in clock cycles (16-bit, max 65535)
        """
        self._add_write(ADDR_SCHED_TIMEOUT_CYCLES, cycles & 0xFFFF)

    # =========================================================================
    # Descriptor Engine Configuration
    # =========================================================================

    def configure_descriptor_engine(self, enable=True, prefetch=False, fifo_thresh=8):
        """
        Configure descriptor engine.

        Args:
            enable: Master descriptor engine enable
            prefetch: Enable descriptor prefetch
            fifo_thresh: Prefetch FIFO threshold (4 bits, 0-15)
        """
        value = (
            (1 if enable else 0) |
            (1 if prefetch else 0) << 1 |
            (fifo_thresh & 0xF) << 2
        )
        self._add_write(ADDR_DESCENG_CONFIG, value)

    def set_address_range_0(self, base, limit):
        """
        Set address range 0 for descriptor validation.

        Args:
            base: Base address (32-bit)
            limit: Limit address (32-bit)
        """
        self._add_write(ADDR_DESCENG_ADDR0_BASE, base & 0xFFFFFFFF)
        self._add_write(ADDR_DESCENG_ADDR0_LIMIT, limit & 0xFFFFFFFF)

    def set_address_range_1(self, base, limit):
        """
        Set address range 1 for descriptor validation.

        Args:
            base: Base address (32-bit)
            limit: Limit address (32-bit)
        """
        self._add_write(ADDR_DESCENG_ADDR1_BASE, base & 0xFFFFFFFF)
        self._add_write(ADDR_DESCENG_ADDR1_LIMIT, limit & 0xFFFFFFFF)

    # =========================================================================
    # AXI Transfer Configuration
    # =========================================================================

    def configure_axi_transfers(self, rd_beats=15, wr_beats=15):
        """
        Configure AXI read/write burst sizes.

        Args:
            rd_beats: Read burst beats (ARLEN value, 0-255 = 1-256 beats)
            wr_beats: Write burst beats (AWLEN value, 0-255 = 1-256 beats)
        """
        value = (rd_beats & 0xFF) | ((wr_beats & 0xFF) << 8)
        self._add_write(ADDR_AXI_XFER_CONFIG, value)

    # =========================================================================
    # Performance Profiler Configuration
    # =========================================================================

    def configure_profiler(self, enable=False, mode=0, clear=False):
        """
        Configure performance profiler.

        Args:
            enable: Enable profiler
            mode: Profiler mode (0=count, 1=histogram)
            clear: Clear counters (self-clearing)
        """
        value = (
            (1 if enable else 0) |
            (1 if mode else 0) << 1 |
            (1 if clear else 0) << 2
        )
        self._add_write(ADDR_PERF_CONFIG, value)

    # =========================================================================
    # Status Read Helpers (generate read addresses)
    # =========================================================================

    def get_status_addresses(self):
        """
        Get list of status register addresses for polling.

        Returns:
            Dict mapping register names to addresses
        """
        return {
            'GLOBAL_STATUS': ADDR_GLOBAL_STATUS,
            'VERSION': ADDR_VERSION,
            'CHANNEL_IDLE': ADDR_CHANNEL_IDLE,
            'DESC_ENGINE_IDLE': ADDR_DESC_ENGINE_IDLE,
            'SCHEDULER_IDLE': ADDR_SCHEDULER_IDLE,
            'SCHED_ERROR': ADDR_SCHED_ERROR,
            'AXI_RD_COMPLETE': ADDR_AXI_RD_COMPLETE,
            'AXI_WR_COMPLETE': ADDR_AXI_WR_COMPLETE,
            'MON_FIFO_STATUS': ADDR_MON_FIFO_STATUS,
            'MON_FIFO_COUNT': ADDR_MON_FIFO_COUNT,
        }

    def get_channel_state_address(self, channel):
        """Get address for channel state register."""
        if channel < 0 or channel >= self.NUM_CHANNELS:
            raise ValueError(f"Channel {channel} out of range (0-7)")
        return get_ch_state_addr(channel)

    def get_channel_kickoff_addresses(self, channel):
        """
        Get kick-off register addresses for a channel.

        Args:
            channel: Channel number (0-7)

        Returns:
            Dict with 'low' and 'high' addresses
        """
        if channel < 0 or channel >= self.NUM_CHANNELS:
            raise ValueError(f"Channel {channel} out of range (0-7)")
        return {
            'low': get_ch_ctrl_low_addr(channel),
            'high': get_ch_ctrl_high_addr(channel)
        }

    # =========================================================================
    # Monitor FIFO Status (Read-only)
    # =========================================================================

    @staticmethod
    def get_mon_fifo_status_addr():
        """Get monitor FIFO status register address."""
        return ADDR_MON_FIFO_STATUS

    @staticmethod
    def get_mon_fifo_count_addr():
        """Get monitor FIFO count register address."""
        return ADDR_MON_FIFO_COUNT

    @staticmethod
    def parse_mon_fifo_status(value):
        """
        Parse monitor FIFO status register value.

        Args:
            value: 32-bit register value from APB read

        Returns:
            Dict with parsed fields
        """
        return {
            'full': bool(value & 0x1),
            'empty': bool(value & 0x2),
            'overflow': bool(value & 0x4),
            'underflow': bool(value & 0x8)
        }

    @staticmethod
    def parse_mon_fifo_count(value):
        """
        Parse monitor FIFO count register value.

        Args:
            value: 32-bit register value from APB read

        Returns:
            FIFO entry count (16-bit)
        """
        return value & 0xFFFF

    # =========================================================================
    # All Read Addresses (for comprehensive status dump)
    # =========================================================================

    def get_all_read_addresses(self):
        """
        Get all register addresses for a complete status dump.

        Returns:
            Dict mapping register names to addresses (config + status)
        """
        addrs = self.get_status_addresses()

        # Add channel states
        for ch in range(self.NUM_CHANNELS):
            addrs[f'CH{ch}_STATE'] = get_ch_state_addr(ch)

        # Add config registers (RW but readable)
        addrs.update({
            'GLOBAL_CTRL': ADDR_GLOBAL_CTRL,
            'CHANNEL_ENABLE': ADDR_CHANNEL_ENABLE,
            'CHANNEL_RESET': ADDR_CHANNEL_RESET,
            'SCHED_TIMEOUT_CYCLES': ADDR_SCHED_TIMEOUT_CYCLES,
            'SCHED_CONFIG': ADDR_SCHED_CONFIG,
            'DESCENG_CONFIG': ADDR_DESCENG_CONFIG,
            'DESCENG_ADDR0_BASE': ADDR_DESCENG_ADDR0_BASE,
            'DESCENG_ADDR0_LIMIT': ADDR_DESCENG_ADDR0_LIMIT,
            'DESCENG_ADDR1_BASE': ADDR_DESCENG_ADDR1_BASE,
            'DESCENG_ADDR1_LIMIT': ADDR_DESCENG_ADDR1_LIMIT,
            'AXI_XFER_CONFIG': ADDR_AXI_XFER_CONFIG,
            'PERF_CONFIG': ADDR_PERF_CONFIG,
        })

        return addrs

    # =========================================================================
    # Default Configuration Presets
    # =========================================================================

    def apply_default_config(self):
        """
        Apply default configuration for basic operation.

        Enables:
        - Global enable
        - All 8 channels
        - Scheduler with timeout and error reporting
        - Descriptor engine (no prefetch)
        - 16-beat AXI bursts
        """
        self.enable_global(True)
        self.enable_channels(0xFF)
        self.configure_scheduler(enable=True, timeout_en=True, err_en=True,
                                 compl_en=True, perf_en=False)
        self.set_scheduler_timeout(1000)
        self.configure_descriptor_engine(enable=True, prefetch=False, fifo_thresh=8)
        self.set_address_range_0(0x00000000, 0xFFFFFFFF)  # Full range
        self.set_address_range_1(0x00000000, 0xFFFFFFFF)
        self.configure_axi_transfers(rd_beats=15, wr_beats=15)

    def apply_minimal_config(self, channel_mask=0x01):
        """
        Apply minimal configuration for single-channel test.

        Args:
            channel_mask: Channels to enable (default: channel 0 only)
        """
        self.enable_global(True)
        self.enable_channels(channel_mask)
        self.configure_scheduler(enable=True)
        self.configure_descriptor_engine(enable=True)

    # =========================================================================
    # Debug Helpers
    # =========================================================================

    def dump_pending_writes(self):
        """Print all pending writes (for debugging)."""
        print(f"StreamHelper: {len(self._pending_writes)} pending writes:")
        for addr, data in self._pending_writes:
            print(f"  0x{addr:03X} = 0x{data:08X}")

    def get_register_name(self, addr):
        """Get register name for an address (for debug output)."""
        addr_to_name = {
            0x100: 'GLOBAL_CTRL',
            0x104: 'GLOBAL_STATUS',
            0x108: 'VERSION',
            0x120: 'CHANNEL_ENABLE',
            0x124: 'CHANNEL_RESET',
            0x140: 'CHANNEL_IDLE',
            0x144: 'DESC_ENGINE_IDLE',
            0x148: 'SCHEDULER_IDLE',
            0x170: 'SCHED_ERROR',
            0x174: 'AXI_RD_COMPLETE',
            0x178: 'AXI_WR_COMPLETE',
            0x180: 'MON_FIFO_STATUS',
            0x184: 'MON_FIFO_COUNT',
            0x200: 'SCHED_TIMEOUT_CYCLES',
            0x204: 'SCHED_CONFIG',
            0x220: 'DESCENG_CONFIG',
            0x224: 'DESCENG_ADDR0_BASE',
            0x228: 'DESCENG_ADDR0_LIMIT',
            0x22C: 'DESCENG_ADDR1_BASE',
            0x230: 'DESCENG_ADDR1_LIMIT',
            0x2A0: 'AXI_XFER_CONFIG',
            0x2B0: 'PERF_CONFIG',
        }

        # Check channel kick-off registers (0x000-0x03F)
        if 0x000 <= addr <= 0x03F:
            channel = addr // 8
            is_high = (addr % 8) == 4
            return f"CH{channel}_CTRL_{'HIGH' if is_high else 'LOW'}"

        # Check channel state registers (0x150-0x16F)
        if 0x150 <= addr <= 0x16F:
            channel = (addr - 0x150) // 4
            return f"CH{channel}_STATE"

        return addr_to_name.get(addr, f"UNKNOWN_0x{addr:03X}")
