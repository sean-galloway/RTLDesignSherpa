# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: SourceDataPathAxisTestTB
# Purpose: RAPIDS Source Data Path AXIS Test Wrapper Testbench
#
# Documentation: projects/components/dma-ip/rapids/PRD.md
# Subsystem: rapids_macro
#
# Author: sean galloway
# Created: 2026-01-10

"""
RAPIDS Source Data Path AXIS Test Wrapper Testbench

Testbench for the src_data_path_axis_test module which wraps:
- 8x Scheduler instances (fed by GAXI descriptor masters)
- src_data_path_axis (AXI read -> SRAM -> AXIS master)

Interfaces:
- 8x Descriptor GAXI masters (one per channel)
- AXI4 read slave (responds to m_axi_ar*/r* signals)
- AXIS slave (monitors m_axis_* signals)

Test Flow:
1. Pre-load memory with test data
2. Send descriptors to schedulers via GAXI masters
3. Schedulers process descriptors and request reads
4. AXI slave returns data from memory
5. Verify AXIS output packets
"""

import os
import random
from typing import Dict, Any, Tuple, List
import time
import cocotb

# Framework imports
from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

# GAXI for descriptor interfaces
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_master

# AXIS for stream interface (slave to monitor output)
from CocoTBFramework.components.axis4.axis_factories import create_axis_slave

# AXI4 for memory interface (slave for reads)
from CocoTBFramework.components.axi4.axi4_factories import create_axi4_slave_rd


class SrcDataPathAxisTestTB(TBBase):
    """
    RAPIDS Source Data Path AXIS Test Wrapper Testbench.

    Tests the source path: Descriptors -> Schedulers -> AXI Read -> SRAM -> AXIS Output
    """

    def __init__(self, dut, clk=None, rst_n=None):
        super().__init__(dut)

        # Configuration from environment
        self.NUM_CHANNELS = self.convert_to_int(os.environ.get('TEST_NUM_CHANNELS', '8'))
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '64'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '512'))
        self.AXI_ID_WIDTH = self.convert_to_int(os.environ.get('TEST_AXI_ID_WIDTH', '8'))
        self.SRAM_DEPTH = self.convert_to_int(os.environ.get('TEST_SRAM_DEPTH', '4096'))
        self.CLK_PERIOD = self.convert_to_int(os.environ.get('TEST_CLK_PERIOD', '10'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        # Drain granularity under test. Default 1 matches the historical TB
        # setting; >1 is what exposed the source beat drop.
        self.DRAIN_SIZE = self.convert_to_int(os.environ.get('TEST_DRAIN_SIZE', '1'))

        # Initialize random generator
        random.seed(self.SEED)

        # Clock and reset
        self.clk = clk
        self.clk_name = clk._name if clk else 'clk'
        self.rst_n = rst_n

        # Derived parameters
        self.DESC_WIDTH = 256  # RAPIDS descriptor format
        self.STRB_WIDTH = self.DATA_WIDTH // 8

        # Address configuration
        self.BASE_ADDRESS = 0x10000000
        self.CHANNEL_OFFSET = 0x00100000

        # Component interfaces (set up in initialize_test)
        self.descriptor_masters = []  # 8 GAXI masters for descriptors
        self.axi_read_slave = None    # AXI slave to respond to reads
        self.axis_slave = None        # AXIS slave to monitor output

        # Memory model with pre-loaded data
        bytes_per_line = self.DATA_WIDTH // 8
        num_lines = (32 * self.CHANNEL_OFFSET) // bytes_per_line
        self.memory_model = MemoryModel(
            num_lines=num_lines,
            bytes_per_line=bytes_per_line
        )

        # Expected data for verification
        self.expected_data = {}  # addr -> data

        # Received AXIS packets
        self.received_packets = []

        # Timing configuration
        self.timing_configs = self._create_timing_configs()
        self.current_timing_profile = 'normal'
        self.timing_config = FlexRandomizer(self.timing_configs['normal'])

        # Test statistics
        self.test_stats = {
            'start_time': 0,
            'total_operations': 0,
            'successful_operations': 0,
            'failed_operations': 0,
            'descriptors_sent': 0,
            'axi_reads_completed': 0,
            'axis_packets_received': 0,
            'channel_operations': [0] * self.NUM_CHANNELS,
            'channel_errors': [0] * self.NUM_CHANNELS,
        }

        self.log.info(f"SourceDataPathAxisTestTB initialized: {self.NUM_CHANNELS} channels, "
                      f"DW={self.DATA_WIDTH}, AW={self.ADDR_WIDTH}")

    # =========================================================================
    # MANDATORY THREE METHODS
    # =========================================================================

    async def setup_clocks_and_reset(self):
        """Start clocks and perform reset sequence"""
        await self.start_clock(self.clk_name, freq=self.CLK_PERIOD, units='ns')

        # Set configuration signals before reset
        self.dut.cfg_axi_rd_xfer_beats.value = 8
        # cfg_drain_size: beats reserved per drain grant. The old comment here
        # claimed higher values "cause backpressure when small transfers are
        # queued" and pinned it to 1; that was this bug being read as a tuning
        # constraint -- see known_issues/resolved/drain_size_gt1_source_beat_drop.md.
        # Driven from TEST_DRAIN_SIZE so the sweep can exercise >1.
        self.dut.cfg_drain_size.value = self.DRAIN_SIZE
        self.dut.cfg_channel_reset.value = 0

        # Reset sequence
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 15)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 10)

        self.log.info("Clock started and reset complete")

    async def assert_reset(self):
        """Assert active-low reset"""
        self.rst_n.value = 0
        self.log.info("Reset asserted")

    async def deassert_reset(self):
        """Deassert reset"""
        self.rst_n.value = 1
        await self.wait_clocks(self.clk_name, 5)
        self.log.info("Reset deasserted")

    # =========================================================================
    # INTERFACE SETUP
    # =========================================================================

    def setup_interfaces(self):
        """Set up all test interfaces"""
        self.log.info("Setting up interfaces...")

        # Create 8 GAXI masters for descriptor interfaces
        # Signal naming: descriptor_N_valid, descriptor_N_ready, descriptor_N_packet, descriptor_N_error
        for i in range(self.NUM_CHANNELS):
            desc_master = create_gaxi_master(
                dut=self.dut,
                title=f"desc_ch{i}",
                prefix=f"descriptor_{i}_",
                clock=self.clk,
                log=self.log,
                multi_sig=True,
                field_config={
                    'packet': {'bits': self.DESC_WIDTH},
                    'error': {'bits': 1},
                }
            )
            self.descriptor_masters.append(desc_master)

        # AXI4 read slave to respond to m_axi_ar*/r* signals
        # base_addr translates system addresses (0x10000000+) to 0-based memory model offsets
        self.axi_read_slave = create_axi4_slave_rd(
            dut=self.dut,
            clock=self.clk,
            prefix="m_axi_",
            log=self.log,
            data_width=self.DATA_WIDTH,
            id_width=self.AXI_ID_WIDTH,
            addr_width=self.ADDR_WIDTH,
            user_width=1,
            multi_sig=True,
            memory_model=self.memory_model,
            base_addr=self.BASE_ADDRESS,
        )

        # AXIS slave to monitor m_axis_* output
        self.axis_slave = create_axis_slave(
            dut=self.dut,
            clock=self.clk,
            prefix="m_axis_",
            log=self.log,
            data_width=self.DATA_WIDTH,
            id_width=8,
            dest_width=4,
            user_width=1,
        )

        # Apply BFM timing profiles (env-driven). Defaults leave behavior
        # unchanged: AXI read slave 'fixed', GAXI descriptor masters 'backtoback'.
        self._apply_timing_from_env()

        self.log.info("Interface setup complete")

    def _apply_timing_from_env(self):
        """Read timing-profile env vars and apply them to the BFMs.

        AXI read slave (DUT is the read master, BFM is the responder):
          AR uses the 'slave' (ready_delay) config, R uses 'master' (valid_delay).
          Uniform TIMING_PROFILE (default 'fixed') with AXI_PROFILE_AR/_R overrides.
        GAXI descriptor masters (drive valid): GAXI_PROFILE_DESC, default
          GAXI_TIMING_PROFILE, default 'backtoback'.
        """
        import os
        axi_base = os.environ.get('TIMING_PROFILE', 'fixed')
        self.set_axi_timing(
            ar=os.environ.get('AXI_PROFILE_AR', axi_base),
            r=os.environ.get('AXI_PROFILE_R', axi_base),
        )
        gaxi_base = os.environ.get('GAXI_TIMING_PROFILE', 'backtoback')
        self.set_gaxi_timing_profile(os.environ.get('GAXI_PROFILE_DESC', gaxi_base))
        # AXIS egress (m_axis_tready backpressure applied by the output monitor).
        self.set_axis_timing(os.environ.get('AXIS_PROFILE', axi_base))

    def set_axis_timing(self, profile_name='fixed'):
        """Install the ready-backpressure randomizer on the AXIS slave BFM that
        owns m_axis_tready. 'default'/'fixed' and GAXI-only names leave the
        egress always-ready (preserve baseline)."""
        from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
        from TBClasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS
        p = 'constrained' if profile_name == 'mixed' else profile_name
        slave = self.axis_slave['slave']
        if p in (None, 'default', 'fixed') or p not in AXI_RANDOMIZER_CONFIGS:
            slave.set_randomizer(FlexRandomizer({'ready_delay': ([(0, 0)], [1])}))  # always ready
            self.log.info(f"AXIS slave timing profile: {profile_name} (always ready)")
            return
        slave.set_randomizer(FlexRandomizer(AXI_RANDOMIZER_CONFIGS[p]['slave']))
        self.log.info(f"AXIS slave timing profile: {p}")

    def set_axi_timing(self, ar='fixed', r='fixed'):
        """Apply timing profiles to the AXI read slave's AR/R channels.
        'mixed' -> constrained AR + slow_producer R."""
        from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
        from TBClasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS
        ar = 'constrained' if ar == 'mixed' else ar
        r = 'slow_producer' if r == 'mixed' else r

        def _cfg(name, section):
            if name not in AXI_RANDOMIZER_CONFIGS:
                self.log.warning(f"Unknown AXI timing profile '{name}', using 'fixed'")
                name = 'fixed'
            return FlexRandomizer(AXI_RANDOMIZER_CONFIGS[name][section])

        rd = self.axi_read_slave['interface']
        rd.ar_channel.randomizer = _cfg(ar, 'slave')   # drives arready
        rd.r_channel.randomizer = _cfg(r, 'master')    # drives rvalid
        self.log.info(f"AXI read-slave timing profiles: ar={ar}, r={r}")

    def set_gaxi_timing_profile(self, profile_name='backtoback'):
        """Apply a GAXI timing profile to all 8 descriptor masters (drive valid).
        'mixed' -> 'gaxi_realistic'. Each master gets its own FlexRandomizer
        (the randomizer is stateful, so instances must not be shared)."""
        from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
        from TBClasses.amba.amba_random_configs import GAXI_RANDOMIZER_CONFIGS
        if profile_name == 'mixed':
            profile_name = 'gaxi_realistic'
        if profile_name not in GAXI_RANDOMIZER_CONFIGS:
            self.log.warning(f"Unknown GAXI timing profile '{profile_name}', "
                             f"using 'backtoback'")
            profile_name = 'backtoback'
        master_cfg = GAXI_RANDOMIZER_CONFIGS[profile_name]['master']
        for m in self.descriptor_masters:
            m.randomizer = FlexRandomizer(master_cfg)
        self.log.info(f"GAXI descriptor masters timing profile: {profile_name}")

    async def initialize_test(self):
        """Initialize test environment"""
        self.log.info("Initializing test...")
        self.test_stats['start_time'] = time.time()

        # Set up all interfaces
        self.setup_interfaces()

        # Pre-load memory with test data
        await self._preload_memory()

        # Every beat the AXIS slave BFM accepts is filed by the framework
        # callback (rapids TASK-013; this was a hand-rolled tready/capture loop).
        if not getattr(self, '_axis_cb_installed', False):
            self.axis_slave['slave'].add_callback(self._on_axis_beat)
            self._axis_cb_installed = True
        self._axis_monitor_active = True

        self.log.info("Test initialization complete")

    def _on_axis_beat(self, pkt):
        """AXIS slave callback: record the accepted egress beat."""
        f = pkt.fields
        packet_data = {
            'tdata': int(f.get('data', 0)),
            'tstrb': int(f.get('strb', 0)),
            'tlast': int(f.get('last', 0)),
            'tid': int(f.get('id', 0)),
            'tdest': int(f.get('dest', 0)),
        }
        self.received_packets.append(packet_data)
        self.test_stats['axis_packets_received'] += 1
        if packet_data['tlast']:
            self.log.debug(f"AXIS packet complete: tid={packet_data['tid']}, "
                           f"tdest={packet_data['tdest']}")

    def stop_axis_monitor(self):
        """Stop the AXIS output monitor"""
        self._axis_monitor_active = False

    async def _preload_memory(self):
        """Pre-load memory with test data using base_addr-relative addressing.

        The memory model uses 0-based addressing. System addresses are translated
        to memory model offsets by subtracting BASE_ADDRESS via the AXI slave's
        base_addr parameter.

        Memory layout matches system address layout (offset = sys_addr - BASE_ADDRESS):
          Channel 0: offsets 0x000000 to 0x000FFF (sys 0x10000000-0x10000FFF)
          Channel 1: offsets 0x100000 to 0x100FFF (sys 0x10100000-0x10100FFF)
          etc.
        """
        self.log.info("Pre-loading memory...")
        bytes_per_line = self.DATA_WIDTH // 8

        for ch in range(self.NUM_CHANNELS):
            for i in range(64):
                # Memory offset = system address - BASE_ADDRESS
                # This matches what the AXI slave will calculate
                mem_offset = ch * self.CHANNEL_OFFSET + i * bytes_per_line

                # System address (used in descriptors and verification)
                sys_addr = self.BASE_ADDRESS + mem_offset

                # Create deterministic test pattern as integer
                data_int = ((ch << 56) | (i << 48) | (0xCAFE0000 + ch * 0x100 + i))
                data_int = data_int & ((1 << self.DATA_WIDTH) - 1)  # Mask to data width

                # Convert integer to bytearray (little-endian)
                data_bytes = bytearray(data_int.to_bytes(bytes_per_line, 'little'))
                self.memory_model.write(mem_offset, data_bytes)

                # Store expected data keyed by system address for verification
                self.expected_data[sys_addr] = data_int

        self.log.info(f"Pre-loaded {self.NUM_CHANNELS * 64} memory locations")

    # =========================================================================
    # TIMING CONFIGURATION
    # =========================================================================

    def _create_timing_configs(self) -> Dict[str, Dict]:
        """Create timing configuration profiles"""
        return {
            'fast': {
                'desc_delay': ([(0, 2), (3, 5)], [3, 1]),
                'axi_delay': ([(1, 3), (4, 8)], [2, 1]),
                'inter_op_delay': ([(1, 5)], [1])
            },
            'normal': {
                'desc_delay': ([(2, 8), (9, 15)], [2, 1]),
                'axi_delay': ([(5, 10), (11, 20)], [2, 1]),
                'inter_op_delay': ([(5, 15)], [1])
            },
            'slow': {
                'desc_delay': ([(10, 20), (21, 40)], [2, 1]),
                'axi_delay': ([(15, 30), (31, 50)], [2, 1]),
                'inter_op_delay': ([(20, 50)], [1])
            },
            'stress': {
                'desc_delay': ([(0, 1), (2, 5)], [3, 1]),
                'axi_delay': ([(0, 2), (3, 8)], [3, 1]),
                'inter_op_delay': ([(0, 3)], [1])
            }
        }

    def set_timing_profile(self, profile: str):
        """Set timing profile"""
        if profile in self.timing_configs:
            self.current_timing_profile = profile
            self.timing_config = FlexRandomizer(self.timing_configs[profile])
            self.log.info(f"Timing profile set to: {profile}")

    # =========================================================================
    # DESCRIPTOR HELPERS
    # =========================================================================

    def create_read_descriptor(self, channel: int, addr: int, beats: int, eos: bool = False,
                               length_bytes: int = None) -> int:
        """Create a RAPIDS read descriptor (256 bits).

        Byte-granular RAPIDS (rapids TASK-019): the length field is in BYTES.
        `beats` is scaled by the beat size so the beat-oriented tests read
        unchanged; `length_bytes` gives an exact byte length instead.

        Descriptor format (from scheduler.sv):
        - [63:0]    : src_addr - Source address (where to read FROM)
        - [127:64]  : dst_addr - Destination address (not used for source path test)
        - [159:128] : length - Transfer length in BEATS (32 bits)
        - [191:160] : next_descriptor_ptr - Address of next descriptor (0 = last)
        - [192]     : valid - Descriptor valid flag
        - [193]     : gen_irq - Generate interrupt on completion
        - [194]     : last - Last descriptor in chain flag
        - [199:196] : channel_id
        - [207:200] : desc_priority
        - [255:208] : reserved
        """
        desc = 0
        # Source address (where to read from)
        desc |= (addr & ((1 << 64) - 1))  # bits [63:0]
        # Destination address (not relevant for source path read, use 0)
        desc |= (0 << 64)  # bits [127:64]
        # Transfer length in BYTES
        nbytes = length_bytes if length_bytes is not None else beats * (self.DATA_WIDTH // 8)
        desc |= ((nbytes & 0xFFFFFFFF) << 128)  # bits [159:128]
        # Next descriptor pointer (0 = no chaining)
        desc |= (0 << 160)  # bits [191:160]
        # Valid flag (must be set for scheduler to process)
        desc |= (1 << 192)  # bit 192
        # gen_irq = 0
        # last flag
        if eos:
            desc |= (1 << 194)  # bit 194 = last descriptor in chain
        # Channel ID (informational)
        desc |= ((channel & 0xF) << 196)  # bits [199:196]
        return desc

    async def send_descriptor(self, channel: int, addr: int, beats: int, eos: bool = False,
                              length_bytes: int = None):
        """Send a descriptor to a specific channel"""
        if channel >= self.NUM_CHANNELS:
            raise ValueError(f"Invalid channel {channel}")

        desc = self.create_read_descriptor(channel, addr, beats, eos, length_bytes=length_bytes)

        # Send via GAXI master (factory returns GAXIMaster directly, not a dict)
        master = self.descriptor_masters[channel]
        packet = master.create_packet(packet=desc, error=0)
        await master.send(packet)

        self.test_stats['descriptors_sent'] += 1
        self.test_stats['channel_operations'][channel] += 1
        self.log.debug(f"Sent descriptor to ch{channel}: addr=0x{addr:X}, beats={beats}, eos={eos}")

    # =========================================================================
    # TEST METHODS
    # =========================================================================

    async def test_basic_descriptor_flow(self, num_descriptors: int = 8) -> Tuple[bool, Dict[str, Any]]:
        """Test basic descriptor flow through schedulers"""
        self.log.info(f"Testing basic descriptor flow ({num_descriptors} descriptors)...")

        successful = 0
        failed = 0

        for i in range(num_descriptors):
            try:
                channel = i % self.NUM_CHANNELS
                addr = self.BASE_ADDRESS + channel * self.CHANNEL_OFFSET + (i % 64) * (self.DATA_WIDTH // 8)
                beats = random.randint(1, 8)

                # Send descriptor
                await self.send_descriptor(channel, addr, beats)
                # The source path fetches its own data, so the channel must return to
                # idle; poll up to 1000 cycles (the old code accepted 'busy' as success).
                sched_idle = 0
                for _ in range(20):
                    await self.wait_clocks(self.clk_name, 50)
                    sched_idle = int(self.dut.sched_idle.value)
                    if (sched_idle >> channel) & 1:
                        break
                if (sched_idle >> channel) & 1:
                    successful += 1
                    self.test_stats['successful_operations'] += 1
                else:
                    self.log.error(f"Descriptor {i}: channel {channel} did not return to idle")
                    failed += 1
                    self.test_stats['failed_operations'] += 1

                delay = self.timing_config.next()['inter_op_delay']
                await self.wait_clocks(self.clk_name, delay)

            except Exception as e:
                self.log.error(f"Descriptor {i} failed: {e}")
                failed += 1
                self.test_stats['failed_operations'] += 1

        self.test_stats['total_operations'] += num_descriptors

        stats = {
            'successful': successful,
            'failed': failed,
            'total': num_descriptors,
            'success_rate': successful / num_descriptors if num_descriptors > 0 else 0
        }

        return failed == 0, stats

    async def test_multi_channel_operation(self, num_channels: int = 4, descriptors_per_channel: int = 2) -> Tuple[bool, Dict[str, Any]]:
        """Test multi-channel operation"""
        self.log.info(f"Testing multi-channel: {num_channels} channels, {descriptors_per_channel} desc/ch...")

        successful = 0
        failed = 0
        total = num_channels * descriptors_per_channel

        for ch in range(num_channels):
            for d in range(descriptors_per_channel):
                try:
                    addr = self.BASE_ADDRESS + ch * self.CHANNEL_OFFSET + d * (self.DATA_WIDTH // 8)
                    beats = 4

                    await self.send_descriptor(ch, addr, beats)
                    successful += 1
                    self.test_stats['successful_operations'] += 1

                    await self.wait_clocks(self.clk_name, 5)

                except Exception as e:
                    self.log.error(f"Ch{ch} desc{d} failed: {e}")
                    failed += 1
                    self.test_stats['failed_operations'] += 1

        # Wait for processing
        await self.wait_clocks(self.clk_name, 200)

        self.test_stats['total_operations'] += total

        stats = {
            'successful': successful,
            'failed': failed,
            'total': total,
            'channels_tested': num_channels,
            'success_rate': successful / total if total > 0 else 0
        }

        return failed == 0, stats

    async def test_axi_read_operations(self, num_operations: int = 12) -> Tuple[bool, Dict[str, Any]]:
        """Test AXI read operations"""
        self.log.info(f"Testing AXI read operations ({num_operations})...")

        successful = 0
        failed = 0

        for i in range(num_operations):
            try:
                channel = i % self.NUM_CHANNELS
                addr = self.BASE_ADDRESS + channel * self.CHANNEL_OFFSET + (i % 64) * (self.DATA_WIDTH // 8)
                beats = 4
                reads_before = int(self.dut.dbg_r_beats_rcvd.value)
                await self.send_descriptor(channel, addr, beats)
                await self.wait_clocks(self.clk_name, 100)
                # this descriptor's read must add exactly its beats to the cumulative counter
                dbg_reads = int(self.dut.dbg_r_beats_rcvd.value) - reads_before
                if dbg_reads != beats:
                    self.log.error(f"AXI read {i}: {dbg_reads} R beats for a {beats}-beat descriptor")
                if dbg_reads == beats:
                    successful += 1
                    self.test_stats['axi_reads_completed'] += 1
                    self.test_stats['successful_operations'] += 1
                else:
                    self.log.warning(f"AXI read {i}: no read beats received")
                    failed += 1
                    self.test_stats['failed_operations'] += 1

            except Exception as e:
                self.log.error(f"AXI read {i} failed: {e}")
                failed += 1
                self.test_stats['failed_operations'] += 1

        self.test_stats['total_operations'] += num_operations

        stats = {
            'successful': successful,
            'failed': failed,
            'total': num_operations,
            'success_rate': successful / num_operations if num_operations > 0 else 0
        }

        return failed == 0, stats

    async def test_axis_transmission(self, num_packets: int = 16) -> Tuple[bool, Dict[str, Any]]:
        """Test AXIS data transmission"""
        self.log.info(f"Testing AXIS transmission ({num_packets} packets)...")

        successful = 0
        failed = 0

        for i in range(num_packets):
            try:
                channel = i % self.NUM_CHANNELS
                addr = self.BASE_ADDRESS + channel * self.CHANNEL_OFFSET + (i % 64) * (self.DATA_WIDTH // 8)
                beats = random.randint(1, 4)
                sent_before = int(self.dut.dbg_axis_beats_sent.value)
                await self.send_descriptor(channel, addr, beats)
                await self.wait_clocks(self.clk_name, 150)
                # this descriptor must add exactly its beats to the egress counter
                axis_sent = int(self.dut.dbg_axis_beats_sent.value) - sent_before
                if axis_sent != beats:
                    self.log.error(f"AXIS packet {i}: {axis_sent} beats out for a {beats}-beat descriptor")
                if axis_sent == beats:
                    successful += 1
                    self.test_stats['axis_packets_received'] += 1
                    self.test_stats['successful_operations'] += 1
                else:
                    self.log.warning(f"AXIS packet {i}: no output detected")
                    failed += 1
                    self.test_stats['failed_operations'] += 1

                delay = self.timing_config.next()['axi_delay']
                await self.wait_clocks(self.clk_name, delay)

            except Exception as e:
                self.log.error(f"AXIS packet {i} failed: {e}")
                failed += 1
                self.test_stats['failed_operations'] += 1

        self.test_stats['total_operations'] += num_packets

        stats = {
            'successful': successful,
            'failed': failed,
            'total': num_packets,
            'success_rate': successful / num_packets if num_packets > 0 else 0
        }

        return failed == 0, stats

    def _memory_bytes(self, sys_addr: int, n: int) -> bytes:
        """The preloaded bytes at sys_addr.. (from the beat-keyed expected_data)."""
        bpb = self.DATA_WIDTH // 8
        out = bytearray()
        a = sys_addr
        while len(out) < n:
            beat_addr = a - a % bpb
            word = self.expected_data[beat_addr]
            b = word.to_bytes(bpb, 'little')
            take = b[a - beat_addr:]
            out += take
            a = beat_addr + bpb
        return bytes(out[:n])

    async def test_byte_packets(self) -> Tuple[bool, Dict[str, Any]]:
        """Byte-granular source (TASK-019): descriptors of arbitrary byte length
        at arbitrary byte addresses. The egress packet must carry exactly the
        bytes at src.., packed from lane 0, ceil(n / bpb) beats, tstrb full on
        every beat but a contiguous tail on the last, tlast on the last only."""
        bpb = self.DATA_WIDTH // 8
        cases = [  # (offset within the channel's preloaded region, bytes)
            (1, 1), (bpb - 1, 2), (7 % bpb, 100), (0, bpb + 5), (17 % bpb, 3 * bpb), (bpb * 3 + 5, 1),
        ]
        errors = []
        for i, (off, n) in enumerate(cases):
            ch = i % self.NUM_CHANNELS
            src = self.BASE_ADDRESS + ch * self.CHANNEL_OFFSET + off
            want = self._memory_bytes(src, n)
            n_before = len(self.received_packets)
            exp_beats = -(-n // bpb)
            await self.send_descriptor(ch, src, 0, length_bytes=n)
            got = []
            for _ in range(4000):
                await self.wait_clocks(self.clk_name, 1)
                got = [q for q in self.received_packets[n_before:] if q['tid'] == ch]
                if len(got) >= exp_beats:
                    break
            bad = []
            if len(got) != exp_beats:
                bad.append(f"{len(got)} beats, expected {exp_beats}")
            else:
                payload = bytearray()
                for k, q in enumerate(got):
                    strb = q['tstrb']
                    nb = bin(strb).count('1')
                    if strb != (1 << nb) - 1:
                        bad.append(f"beat {k} tstrb 0x{strb:X} is not contiguous from lane 0")
                    if k < exp_beats - 1 and nb != bpb:
                        bad.append(f"beat {k} tstrb 0x{strb:X} is partial before the last beat")
                    if bool(q['tlast']) != (k == exp_beats - 1):
                        bad.append(f"beat {k} tlast={q['tlast']}")
                    payload += q['tdata'].to_bytes(bpb, 'little')[:nb]
                if bytes(payload) != want:
                    bad.append(f"payload {payload.hex()} != memory {want.hex()}")
            self.log.info(f"  case {i}: ch{ch} src=0x{src:X} bytes={n} -> {len(got)} beats "
                          f"{'PASS' if not bad else 'FAIL'}")
            for b in bad:
                errors.append(f"case {i} (off {off}, {n} B): {b}")
            # let the channel settle before the next descriptor
            await self.wait_clocks(self.clk_name, 50)
        err = int(self.dut.sched_error.value)
        if err:
            errors.append(f"sched_error=0x{err:X}")
        for e in errors:
            self.log.error(f"  {e}")
        return (not errors), {'cases': len(cases), 'errors': errors}

    # ------------------------------------------------------------------
    # per-channel reset (rapids TASK-019)
    # ------------------------------------------------------------------
    async def _reset_channel(self, ch: int, cycles: int = 1):
        """Drive the per-channel cfg_channel_reset (a register level in the
        product: cycles=1 is a pulse, more is a held level)."""
        self.dut.cfg_channel_reset.value = 1 << ch
        await self.wait_clocks(self.clk_name, cycles)
        self.dut.cfg_channel_reset.value = 0
        await self.wait_clocks(self.clk_name, 4)

    def _err_bit(self, ch: int) -> int:
        return (int(self.dut.sched_error.value) >> ch) & 1

    def _beats_of(self, ch: int, n_before: int):
        return [q for q in self.received_packets[n_before:] if q['tid'] == ch]

    async def _wait_beats(self, ch: int, n_before: int, count: int, cycles: int = 4000) -> bool:
        for _ in range(cycles):
            if len(self._beats_of(ch, n_before)) >= count:
                return True
            await self.wait_clocks(self.clk_name, 1)
        return False

    async def _check_egress(self, tag: str, ch: int, src: int, n: int, n_before: int):
        """The packet of (src, n) must have come out on channel ch: exact
        bytes packed from lane 0, full tstrb but on the last beat, tlast last."""
        bpb = self.DATA_WIDTH // 8
        exp_beats = -(-n // bpb)
        want = self._memory_bytes(src, n)
        await self._wait_beats(ch, n_before, exp_beats)
        await self.wait_clocks(self.clk_name, 50)
        got = self._beats_of(ch, n_before)
        bad = []
        if len(got) != exp_beats:
            return [f"{tag}: {len(got)} beats, expected {exp_beats}"]
        payload = bytearray()
        for k, q in enumerate(got):
            nb = bin(q['tstrb']).count('1')
            if q['tstrb'] != (1 << nb) - 1 or (k < exp_beats - 1 and nb != bpb):
                bad.append(f"{tag}: beat {k} tstrb 0x{q['tstrb']:X}")
            if bool(q['tlast']) != (k == exp_beats - 1):
                bad.append(f"{tag}: beat {k} tlast={q['tlast']}")
            payload += q['tdata'].to_bytes(bpb, 'little')[:nb]
        if bytes(payload) != want:
            bad.append(f"{tag}: payload differs from memory")
        return bad

    async def test_channel_reset(self) -> Tuple[bool, Dict[str, Any]]:
        """rapids TASK-019 channel reset on the source path. Channel A is broken
        two ways -- an R-channel error and a transfer abandoned mid-flight --
        and reset with cfg_channel_reset (pulse, then held level) while channel
        B streams. After each reset A must be quiet (no more beats, error low
        and staying low) and run a good descriptor to completion with correct
        bytes, strobes and tlast, and B's packet must be complete and exact."""
        bpb = self.DATA_WIDTH // 8
        A, B = 1, self.NUM_CHANNELS - 1
        base = lambda ch: self.BASE_ADDRESS + ch * self.CHANNEL_OFFSET
        errors = []

        def expect_clean(tag):
            err = int(self.dut.sched_error.value)
            if err:
                errors.append(f"{tag}: sched_error=0x{err:X}")

        async def quiet(tag, ch):
            await self.wait_clocks(self.clk_name, 300)
            seen = len(self.received_packets)
            await self.wait_clocks(self.clk_name, 300)
            if self._beats_of(ch, seen):
                errors.append(f"{tag}: channel {ch} kept emitting beats after its reset")

        # 1. R error on a window of A's source, then reset under B traffic
        lo, hi = base(A) + 4 * bpb, base(A) + 10 * bpb
        self.axi_read_slave['interface'].resp_override = lambda a: 2 if lo <= a < hi else None
        src_a = base(A) + 4 * bpb + 3
        await self.send_descriptor(A, src_a, 0, length_bytes=3 * bpb)
        for _ in range(4000):
            if self._err_bit(A):
                break
            await self.wait_clocks(self.clk_name, 1)
        else:
            errors.append("rresp: sched_error[A] never asserted")
        if self._err_bit(B):
            errors.append("rresp: error leaked to channel B")
        src_b = base(B) + 5
        n_b = 20 * bpb + 5
        n_b_before = len(self.received_packets)
        await self.send_descriptor(B, src_b, 0, length_bytes=n_b)
        if not await self._wait_beats(B, n_b_before, 2):
            errors.append("rresp: channel B never started")
        await self._reset_channel(A, 1)
        self.axi_read_slave['interface'].resp_override = None
        for _ in range(60):
            await self.wait_clocks(self.clk_name, 1)
            if self._err_bit(A):
                errors.append("rresp: sched_error[A] re-asserted after reset")
                break
        errors += await self._check_egress("B during A reset (rresp)", B, src_b, n_b, n_b_before)
        await quiet("rresp", A)
        src_a = base(A) + 7
        n_a = 5 * bpb + 9
        n_before = len(self.received_packets)
        await self.send_descriptor(A, src_a, 0, length_bytes=n_a)
        errors += await self._check_egress("A after rresp reset", A, src_a, n_a, n_before)
        expect_clean("after rresp recovery")

        # 2. abandoned in flight: 12 beats requested, reset (held) after the
        # first one is out, while B streams a short packet
        src_a = base(A) + 2 * bpb
        n_before_a = len(self.received_packets)
        await self.send_descriptor(A, src_a, 0, length_bytes=12 * bpb)
        if not await self._wait_beats(A, n_before_a, 1):
            errors.append("abort: channel A never started")
        src_b = base(B) + 3 * bpb + 1
        n_b = 2 * bpb + 5
        n_b_before = len(self.received_packets)
        await self.send_descriptor(B, src_b, 0, length_bytes=n_b)
        await self._reset_channel(A, 4)
        errors += await self._check_egress("B during A reset (abort)", B, src_b, n_b, n_b_before)
        await quiet("abort", A)
        expect_clean("after abort")
        src_a = base(A) + 5
        n_a = 2 * bpb + 11
        n_before = len(self.received_packets)
        await self.send_descriptor(A, src_a, 0, length_bytes=n_a)
        errors += await self._check_egress("A after abort reset", A, src_a, n_a, n_before)
        await self.wait_clocks(self.clk_name, 50)
        expect_clean("final")
        for e in errors:
            self.log.error(f"  {e}")
        return (not errors), {'errors': errors}

    async def test_end_to_end_flow(self, num_transfers: int = 8) -> Tuple[bool, Dict[str, Any]]:
        """Test end-to-end data flow"""
        self.log.info(f"Testing end-to-end flow ({num_transfers} transfers)...")

        successful = 0
        failed = 0

        initial_axis_beats = int(self.dut.dbg_axis_beats_sent.value)

        for i in range(num_transfers):
            try:
                channel = i % self.NUM_CHANNELS
                addr = self.BASE_ADDRESS + channel * self.CHANNEL_OFFSET + (i % 64) * (self.DATA_WIDTH // 8)
                beats = random.randint(2, 8)
                n_before = len(self.received_packets)

                # Send descriptor
                await self.send_descriptor(channel, addr, beats, eos=(i == num_transfers - 1))

                # Wait for AXIS output with polling (up to 400 clocks)
                max_wait = 400
                waited = 0
                current_axis_beats = int(self.dut.dbg_axis_beats_sent.value)
                while current_axis_beats <= initial_axis_beats and waited < max_wait:
                    await self.wait_clocks(self.clk_name, 10)
                    waited += 10
                    current_axis_beats = int(self.dut.dbg_axis_beats_sent.value)

                # Check AXIS output, then the payload itself: the beats this
                # descriptor put on the egress must be the words preloaded at
                # addr.. (expected_data), in order, under this channel's tid.
                if current_axis_beats > initial_axis_beats:
                    # Under a backpressure profile the slave BFM accepts the
                    # beats slowly; give the whole burst time to drain.
                    for _ in range(2000):
                        got = [q['tdata'] for q in self.received_packets[n_before:] if q['tid'] == channel]
                        if len(got) >= beats:
                            break
                        await self.wait_clocks(self.clk_name, 1)
                    bpl = self.DATA_WIDTH // 8
                    want = [self.expected_data.get(addr + k * bpl) for k in range(beats)]
                    if got[:beats] != want:
                        failed += 1
                        self.test_stats['failed_operations'] += 1
                        self.log.error(f"E2E transfer {i} ch{channel}: egress payload differs from memory "
                                       f"({len(got)} beats captured, {beats} expected); "
                                       f"first={got[:1]} want={want[:1]}")
                        continue
                    successful += 1
                    self.test_stats['successful_operations'] += 1
                    initial_axis_beats = current_axis_beats
                    self.log.debug(f"E2E transfer {i} successful: ch{channel} (waited {waited} clks, payload verified)")
                else:
                    failed += 1
                    self.test_stats['failed_operations'] += 1
                    # Debug: log scheduler and datapath state
                    sched_idle = int(self.dut.sched_idle.value)
                    sched_state = int(self.dut.sched_state.value)
                    arb_request = int(self.dut.dbg_arb_request.value)
                    r_beats = int(self.dut.dbg_r_beats_rcvd.value)
                    sram_writes = int(self.dut.dbg_sram_writes.value)
                    sram_pending = int(self.dut.dbg_sram_bridge_pending.value)
                    sram_out_valid = int(self.dut.dbg_sram_bridge_out_valid.value)
                    self.log.warning(f"E2E transfer {i} failed: ch{channel}, no AXIS output after {waited} clks")
                    self.log.warning(f"  DEBUG: sched_idle={sched_idle:08b} sched_state[{channel}]={sched_state >> (channel*7) & 0x7F:02x}")
                    self.log.warning(f"  DEBUG: arb_request={arb_request:08b} r_beats={r_beats} sram_writes={sram_writes}")
                    self.log.warning(f"  DEBUG: sram_pending={sram_pending:08b} sram_out_valid={sram_out_valid:08b}")

            except Exception as e:
                self.log.error(f"E2E transfer {i} failed: {e}")
                failed += 1
                self.test_stats['failed_operations'] += 1

        self.test_stats['total_operations'] += num_transfers
        self.log.info(f"end-to-end: payload verified against memory on {successful}/{num_transfers} transfers")

        stats = {
            'successful': successful,
            'failed': failed,
            'total': num_transfers,
            'success_rate': successful / num_transfers if num_transfers > 0 else 0
        }

        return failed == 0, stats

    async def stress_test(self, num_operations: int = 32) -> Tuple[bool, Dict[str, Any]]:
        """Stress test with high throughput"""
        self.log.info(f"Running stress test ({num_operations} operations)...")

        successful = 0
        failed = 0

        for i in range(num_operations):
            try:
                channel = random.randint(0, self.NUM_CHANNELS - 1)
                offset = random.randint(0, 63) * (self.DATA_WIDTH // 8)
                addr = self.BASE_ADDRESS + channel * self.CHANNEL_OFFSET + offset
                beats = random.randint(1, 8)

                # Send descriptor
                await self.send_descriptor(channel, addr, beats)

                # Random short delay
                await self.wait_clocks(self.clk_name, random.randint(5, 20))

                successful += 1
                self.test_stats['successful_operations'] += 1

            except Exception as e:
                self.log.error(f"Stress op {i} failed: {e}")
                failed += 1
                self.test_stats['failed_operations'] += 1

        # Final wait for pipeline to drain
        await self.wait_clocks(self.clk_name, 500)

        self.test_stats['total_operations'] += num_operations

        stats = {
            'successful': successful,
            'failed': failed,
            'total': num_operations,
            'success_rate': successful / num_operations if num_operations > 0 else 0
        }

        return failed < (num_operations * 0.1), stats

    async def test_beat_conservation(self, num_descriptors: int = 12,
                                     beats_per_desc: int = 7) -> Tuple[bool, Dict[str, Any]]:
        """Every beat read from AXI must leave on AXIS. No beat may be dropped.

        This is the check the existing source tests do NOT make. They score a
        packet successful on `dbg_axis_beats_sent > 0` (test_axis_transmission)
        or `current > initial` (test_end_to_end_flow) -- "did anything come
        out", never "did everything come out". A partial drop passes both.

        The drain path reserves beats in whole blocks of cfg_drain_size while
        emitting them one at a time, so a mismatch between reservation and
        emission shows up here and nowhere else. beats_per_desc defaults to 7 so
        the transfer is deliberately NOT a multiple of typical drain sizes
        (1/2/4/8), which is where the original report saw the loss.

        See known_issues/resolved/drain_size_gt1_source_beat_drop.md.
        """
        self.log.info(f"Beat conservation: {num_descriptors} desc x {beats_per_desc} beats, "
                      f"cfg_drain_size={self.DRAIN_SIZE}")

        r_in0 = int(self.dut.dbg_r_beats_rcvd.value)
        axis0 = int(self.dut.dbg_axis_beats_sent.value)

        for i in range(num_descriptors):
            channel = i % self.NUM_CHANNELS
            addr = self.BASE_ADDRESS + channel * self.CHANNEL_OFFSET \
                   + (i % 64) * (self.DATA_WIDTH // 8)
            await self.send_descriptor(channel, addr, beats_per_desc,
                                       eos=(i == num_descriptors - 1))
            await self.wait_clocks(self.clk_name, 40)

        # Quiesce on EVIDENCE, not on a guess: poll until the AXIS beat counter
        # stops advancing. A fixed delay reads a still-draining pipeline as loss
        # -- the first version of this check used 1500 cycles and reported 25%
        # "loss" at cfg_drain_size=1, which is the shipped, known-good setting.
        # The 20000-clock bound fits the 84-beat default; a long transfer
        # (TEST_CONS_DESCS x TEST_CONS_BEATS) raises it through TEST_CONS_WAIT.
        max_wait = int(os.environ.get('TEST_CONS_WAIT', '20000'))
        settled_for = 0
        waited = 0
        last = int(self.dut.dbg_axis_beats_sent.value)
        while settled_for < 600 and waited < max_wait:
            await self.wait_clocks(self.clk_name, 50)
            waited += 50
            now = int(self.dut.dbg_axis_beats_sent.value)
            settled_for = settled_for + 50 if now == last else 0
            last = now
        self.log.info(f"quiesced after {waited} clocks "
                      f"(stable for {settled_for}); axis_beats_sent={last}")
        if waited >= max_wait:
            self.log.warning("quiesce bound hit -- counters may still be moving")

        r_in = int(self.dut.dbg_r_beats_rcvd.value) - r_in0
        axis = int(self.dut.dbg_axis_beats_sent.value) - axis0
        lost = r_in - axis

        stats = {
            'cfg_drain_size': self.DRAIN_SIZE,
            'beats_per_desc': beats_per_desc,
            'descriptors': num_descriptors,
            'beats_read_from_axi': r_in,
            'beats_sent_on_axis': axis,
            'beats_lost': lost,
            'loss_pct': round(100.0 * lost / r_in, 2) if r_in else 0.0,
        }
        self.log.info(f"Beat conservation: {stats}")
        if lost:
            self.log.error(f"BEAT LOSS: {lost} of {r_in} beats read from AXI never "
                           f"reached AXIS ({stats['loss_pct']}%) at "
                           f"cfg_drain_size={self.DRAIN_SIZE}")

        # r_in must be non-zero, or the test proved nothing (the failure mode
        # the existing tests fall into).
        if r_in == 0:
            self.log.error("no beats were read from AXI -- test is vacuous")
            return False, stats

        return lost == 0, stats
