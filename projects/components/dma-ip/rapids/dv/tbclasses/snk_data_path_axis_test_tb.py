# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: SinkDataPathAxisTestTB
# Purpose: RAPIDS Sink Data Path AXIS Test Wrapper Testbench
#
# Documentation: projects/components/dma-ip/rapids/PRD.md
# Subsystem: rapids_macro
#
# Author: sean galloway
# Created: 2026-01-10

"""
RAPIDS Sink Data Path AXIS Test Wrapper Testbench

Testbench for the snk_data_path_axis_test module which wraps:
- 8x Scheduler instances (fed by GAXI descriptor masters)
- snk_data_path_axis (AXIS slave -> SRAM -> AXI write)

Interfaces:
- 8x Descriptor GAXI masters (one per channel)
- AXIS master (to drive s_axis_* signals)
- AXI4 write slave (responds to m_axi_aw*/w*/b* signals)

Test Flow:
1. Send descriptors to schedulers via GAXI masters
2. Schedulers process descriptors and request writes
3. Send AXIS packets matching scheduler requests
4. Verify AXI writes to memory
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

# AXIS for stream interface
from CocoTBFramework.components.axis4.axis_factories import create_axis_master

# AXI4 for memory interface
from CocoTBFramework.components.axi4.axi4_factories import create_axi4_slave_wr


class SnkDataPathAxisTestTB(TBBase):
    """
    RAPIDS Sink Data Path AXIS Test Wrapper Testbench.

    Tests the sink path: Descriptors -> Schedulers -> AXIS -> SRAM -> AXI Write
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
        # Default 16 == the hardcode this replaces and the RDL reset
        # (AXI_XFER_CONFIG.ALLOC_SIZE = 8'd16), so existing cells are unchanged.
        self.ALLOC_SIZE = self.convert_to_int(os.environ.get('TEST_ALLOC_SIZE', '16'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))

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
        self.axis_master = None       # AXIS master to drive input
        self.axi_write_slave = None   # AXI slave to receive writes

        # Memory model for verification
        bytes_per_line = self.DATA_WIDTH // 8
        num_lines = (32 * self.CHANNEL_OFFSET) // bytes_per_line
        self.memory_model = MemoryModel(
            num_lines=num_lines,
            bytes_per_line=bytes_per_line,
            log=self.log
        )

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
            'axis_packets_sent': 0,
            'axi_writes_completed': 0,
            'channel_operations': [0] * self.NUM_CHANNELS,
            'channel_errors': [0] * self.NUM_CHANNELS,
        }

        self.log.info(f"SinkDataPathAxisTestTB initialized: {self.NUM_CHANNELS} channels, "
                      f"DW={self.DATA_WIDTH}, AW={self.ADDR_WIDTH}")

    # =========================================================================
    # MANDATORY THREE METHODS
    # =========================================================================

    async def setup_clocks_and_reset(self):
        """Start clocks and perform reset sequence"""
        await self.start_clock(self.clk_name, freq=self.CLK_PERIOD, units='ns')

        # Set configuration signals before reset
        self.dut.cfg_axi_wr_xfer_beats.value = 8
        # Driven from TEST_ALLOC_SIZE so the 0 case (clamp guard) is reachable.
        self.dut.cfg_alloc_size.value = self.ALLOC_SIZE
        self.pending_alloc_samples = []

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

        # AXIS master to drive s_axis_* signals
        self.axis_master = create_axis_master(
            dut=self.dut,
            clock=self.clk,
            prefix="s_axis_",
            log=self.log,
            data_width=self.DATA_WIDTH,
            id_width=8,
            dest_width=4,
            user_width=1,
        )

        # AXI4 write slave to respond to m_axi_* signals
        # Pass base_addr so slave subtracts it before accessing memory model
        self.axi_write_slave = create_axi4_slave_wr(
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
            base_addr=self.BASE_ADDRESS  # Convert absolute addresses to memory model offsets
        )

        # Apply BFM timing profiles (env-driven). Defaults leave behavior
        # unchanged: AXI write slave 'fixed', GAXI descriptor masters 'backtoback'.
        self._apply_timing_from_env()

        self.log.info("Interface setup complete")

    def _apply_timing_from_env(self):
        """Read timing-profile env vars and apply them to the BFMs.

        AXI write slave (DUT is the write master, BFM is the responder):
          AW/W use the 'slave' (ready_delay) config, B uses 'master' (valid_delay).
          Uniform TIMING_PROFILE (default 'fixed') with AXI_PROFILE_AW/_W/_B overrides.
        GAXI descriptor masters (drive valid): GAXI_PROFILE_DESC, default
          GAXI_TIMING_PROFILE, default 'backtoback'.
        """
        import os
        axi_base = os.environ.get('TIMING_PROFILE', 'fixed')
        self.set_axi_timing(
            aw=os.environ.get('AXI_PROFILE_AW', axi_base),
            w=os.environ.get('AXI_PROFILE_W', axi_base),
            b=os.environ.get('AXI_PROFILE_B', axi_base),
        )
        gaxi_base = os.environ.get('GAXI_TIMING_PROFILE', 'backtoback')
        self.set_gaxi_timing_profile(os.environ.get('GAXI_PROFILE_DESC', gaxi_base))
        # AXIS ingress master (drives s_axis_tvalid). Reuses the AXI profile set
        # (TIMING_PROFILE) unless AXIS_PROFILE overrides.
        self.set_axis_timing(os.environ.get('AXIS_PROFILE', axi_base))

    def set_axis_timing(self, profile_name='fixed'):
        """Apply a timing profile to the AXIS ingress master (drives tvalid ->
        'master'/valid_delay). 'default'/'fixed' and GAXI-only names leave the
        master at full speed (randomizer=None) to preserve baseline behavior."""
        from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
        from TBClasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS
        axis_if = self.axis_master['interface']  # factory returns a dict; GAXIMaster under 'interface'
        p = 'constrained' if profile_name == 'mixed' else profile_name
        # default/fixed and GAXI-only names: leave the factory-default randomizer
        # in place. (The AXIS master is a GAXIMaster that calls randomizer.next();
        # setting it to None breaks send, so we never null it.)
        if p in (None, 'default', 'fixed') or p not in AXI_RANDOMIZER_CONFIGS:
            self.log.info(f"AXIS master timing profile: {profile_name} (factory default, unchanged)")
            return
        axis_if.randomizer = FlexRandomizer(AXI_RANDOMIZER_CONFIGS[p]['master'])
        self.log.info(f"AXIS master timing profile: {p}")

    def set_axi_timing(self, aw='fixed', w='fixed', b='fixed'):
        """Apply timing profiles to the AXI write slave's AW/W/B channels.
        'mixed' -> constrained AW/W + slow_producer B."""
        from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
        from TBClasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS
        aw = 'constrained' if aw == 'mixed' else aw
        w = 'constrained' if w == 'mixed' else w
        b = 'slow_producer' if b == 'mixed' else b

        def _cfg(name, section):
            if name not in AXI_RANDOMIZER_CONFIGS:
                self.log.warning(f"Unknown AXI timing profile '{name}', using 'fixed'")
                name = 'fixed'
            return FlexRandomizer(AXI_RANDOMIZER_CONFIGS[name][section])

        wr = self.axi_write_slave['interface']
        wr.aw_channel.randomizer = _cfg(aw, 'slave')   # drives awready
        wr.w_channel.randomizer = _cfg(w, 'slave')     # drives wready
        wr.b_channel.randomizer = _cfg(b, 'master')    # drives bvalid
        self.log.info(f"AXI write-slave timing profiles: aw={aw}, w={w}, b={b}")

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

        # Initialize memory regions with 0-based line addressing
        bytes_per_line = self.DATA_WIDTH // 8
        for line_idx in range(min(512, self.memory_model.num_lines)):  # Initialize first 512 lines
            self.memory_model.write(line_idx * bytes_per_line, bytearray(bytes_per_line))

        self.log.info("Test initialization complete")

    # =========================================================================
    # TIMING CONFIGURATION
    # =========================================================================

    def _create_timing_configs(self) -> Dict[str, Dict]:
        """Create timing configuration profiles"""
        return {
            'fast': {
                'desc_delay': ([(0, 2), (3, 5)], [3, 1]),
                'axis_delay': ([(1, 3), (4, 8)], [2, 1]),
                'inter_op_delay': ([(1, 5)], [1])
            },
            'normal': {
                'desc_delay': ([(2, 8), (9, 15)], [2, 1]),
                'axis_delay': ([(5, 10), (11, 20)], [2, 1]),
                'inter_op_delay': ([(5, 15)], [1])
            },
            'slow': {
                'desc_delay': ([(10, 20), (21, 40)], [2, 1]),
                'axis_delay': ([(15, 30), (31, 50)], [2, 1]),
                'inter_op_delay': ([(20, 50)], [1])
            },
            'stress': {
                'desc_delay': ([(0, 1), (2, 5)], [3, 1]),
                'axis_delay': ([(0, 2), (3, 8)], [3, 1]),
                'inter_op_delay': ([(0, 3)], [1])
            }
        }

    def set_timing_profile(self, profile: str):
        """Set timing profile"""
        if profile in self.timing_configs:
            self.current_timing_profile = profile
            self.timing_config = FlexRandomizer(self.timing_configs[profile])
            self.log.info(f"Timing profile set to: {profile}")

    def get_timing_value(self, name: str) -> int:
        """Get a timing value from the randomizer"""
        values = self.timing_config.next()
        return values.get(name, 5)

    # =========================================================================
    # DESCRIPTOR HELPERS
    # =========================================================================

    def create_write_descriptor(self, channel: int, addr: int, beats: int, eos: bool = False,
                                length_bytes: int = None) -> int:
        """Create a RAPIDS write descriptor (256 bits).

        Byte-granular RAPIDS (rapids TASK-019): the length field is in BYTES.
        `beats` is scaled by the beat size so the beat-oriented tests read
        unchanged; `length_bytes` gives an exact byte length instead.

        RAPIDS Descriptor Format (from scheduler.sv):
          [63:0]    - src_addr:            Source address (must be aligned to data width)
          [127:64]  - dst_addr:            Destination address (must be aligned to data width)
          [159:128] - length:              Transfer length in BEATS (not bytes!)
          [191:160] - next_descriptor_ptr: Address of next descriptor (0 = last)
          [192]     - valid:               Descriptor valid flag  <-- CRITICAL!
          [193]     - gen_irq:             Generate interrupt on completion
          [194]     - last:                Last descriptor in chain flag
          [195]     - error:               Error flag
          [199:196] - channel_id:          Channel ID (informational)
          [207:200] - desc_priority:       Transfer priority
          [255:208] - reserved:            Reserved for future use

        For sink path (AXIS -> memory write):
          - src_addr = 0 (not used, data comes from AXIS)
          - dst_addr = memory address to write to
        """
        desc = 0
        # [63:0] src_addr - not used for sink path, set to 0
        desc |= 0
        # [127:64] dst_addr - destination memory address
        desc |= ((addr & ((1 << 64) - 1)) << 64)
        # [159:128] length - transfer BYTES
        nbytes = length_bytes if length_bytes is not None else beats * (self.DATA_WIDTH // 8)
        desc |= ((nbytes & 0xFFFFFFFF) << 128)
        # [191:160] next_descriptor_ptr - 0 for single descriptor
        desc |= (0 << 160)
        # [192] valid - MUST be set!
        desc |= (1 << 192)
        # [193] gen_irq - set if eos (end of stream = generate interrupt)
        if eos:
            desc |= (1 << 193)
        # [194] last - last descriptor in chain
        desc |= (1 << 194)  # Always last for single descriptors
        # [195] error - no error
        desc |= (0 << 195)
        # [199:196] channel_id
        desc |= ((channel & 0xF) << 196)
        # [207:200] desc_priority
        desc |= (0 << 200)
        return desc

    async def send_descriptor(self, channel: int, addr: int, beats: int, eos: bool = False,
                              length_bytes: int = None):
        """Send a descriptor to a specific channel"""
        if channel >= self.NUM_CHANNELS:
            raise ValueError(f"Invalid channel {channel}")

        desc = self.create_write_descriptor(channel, addr, beats, eos, length_bytes=length_bytes)

        # Debug: Print descriptor fields for verification
        self.log.info(f"=== DESCRIPTOR ch{channel} ===")
        self.log.info(f"  Full descriptor: 0x{desc:064X}")
        self.log.info(f"  [63:0]    src_addr:  0x{(desc >> 0) & ((1<<64)-1):016X}")
        self.log.info(f"  [127:64]  dst_addr:  0x{(desc >> 64) & ((1<<64)-1):016X}")
        self.log.info(f"  [159:128] length:    {(desc >> 128) & 0xFFFFFFFF} beats")
        self.log.info(f"  [191:160] next_ptr:  0x{(desc >> 160) & 0xFFFFFFFF:08X}")
        self.log.info(f"  [192]     valid:     {(desc >> 192) & 1}")
        self.log.info(f"  [193]     gen_irq:   {(desc >> 193) & 1}")
        self.log.info(f"  [194]     last:      {(desc >> 194) & 1}")
        self.log.info(f"  [195]     error:     {(desc >> 195) & 1}")
        self.log.info(f"  [199:196] chan_id:   {(desc >> 196) & 0xF}")

        # Send via GAXI master - use create_packet and send
        master = self.descriptor_masters[channel]
        packet = master.create_packet(packet=desc, error=0)
        await master.send(packet)

        self.test_stats['descriptors_sent'] += 1
        self.test_stats['channel_operations'][channel] += 1
        self.log.info(f"Sent descriptor to ch{channel}: addr=0x{addr:X}, beats={beats}, eos={eos}")

    # =========================================================================
    # AXIS HELPERS
    # =========================================================================

    async def send_axis_packet(self, channel: int, data: List[int], last: bool = True,
                               strbs: List[int] = None):
        """Queue an AXIS packet and return once it is IN FLIGHT, not accepted.

        The byte-granular ingress (TASK-019) holds s_axis_tready low until the
        channel's packet record arrives from its scheduler, so a test that
        streams first and describes second (every beat-era test here) would
        deadlock on a blocking send. The beats are driven by a background
        task; await wait_axis_sent() when acceptance itself matters.
        strbs: per-beat tstrb (default all bytes)."""
        task = cocotb.start_soon(self._drive_axis_packet(channel, list(data), last, strbs))
        self._axis_tasks = getattr(self, '_axis_tasks', [])
        self._axis_tasks.append(task)
        await self.wait_clocks(self.clk_name, 1)
        return task

    async def _drive_axis_packet(self, channel: int, data: List[int], last: bool, strbs: List[int]):
        axis_interface = self.axis_master['interface']
        full = (1 << self.STRB_WIDTH) - 1
        for i, beat_data in enumerate(data):
            is_last = last and (i == len(data) - 1)
            packet = axis_interface.create_packet(
                data=beat_data,
                strb=(strbs[i] if strbs else full),
                id=channel,
                dest=0,
                user=0,
                last=int(is_last)
            )
            await axis_interface.send(packet)
        self.test_stats['axis_packets_sent'] += 1

    async def wait_axis_sent(self, timeout_cycles: int = 20000) -> bool:
        """Wait until every queued AXIS beat has been accepted."""
        tasks = getattr(self, '_axis_tasks', [])
        for _ in range(timeout_cycles):
            if all(t.done() for t in tasks):
                self._axis_tasks = []
                return True
            await self.wait_clocks(self.clk_name, 1)
        return False

    # ------------------------------------------------------------------
    # byte-granular helpers (rapids TASK-019)
    # ------------------------------------------------------------------
    @staticmethod
    def pack_bytes(payload: bytes, bpb: int):
        """Packed stream beats for a byte payload: (data words, tstrb per beat)."""
        words, strbs = [], []
        for i in range(0, len(payload), bpb):
            chunk = payload[i:i + bpb]
            words.append(int.from_bytes(chunk.ljust(bpb, b'\0'), 'little'))
            strbs.append((1 << len(chunk)) - 1)
        return words, strbs

    def _compare_bytes(self, relative_addr: int, payload: bytes, background: int) -> str:
        """The payload bytes must sit at relative_addr..; the rest of the beats
        they touch must still hold the background byte."""
        bpb = self.DATA_WIDTH // 8
        lo = relative_addr - relative_addr % bpb
        hi = relative_addr + len(payload)
        hi = hi + (-hi % bpb)
        got = bytes(self.memory_model.read(lo, hi - lo))
        exp = bytearray([background] * (hi - lo))
        exp[relative_addr - lo:relative_addr - lo + len(payload)] = payload
        if got != bytes(exp):
            first = next(i for i in range(len(exp)) if got[i] != exp[i])
            return (f"byte 0x{lo + first:X}: memory 0x{got[first]:02X}, expected 0x{exp[first]:02X} "
                    f"(payload {len(payload)} B at 0x{relative_addr:X})")
        return ""

    async def test_byte_packets(self) -> Tuple[bool, Dict[str, Any]]:
        """Byte-granular sink (TASK-019): packets of arbitrary byte length to
        arbitrary byte addresses. The bytes must land exactly where the
        descriptor says, the surrounding bytes of the touched beats must keep
        their background, and no error may be flagged. Cases: one byte at an
        offset, a beat that straddles two memory beats, a long unaligned
        packet, an aligned partial tail, a packet spanning a 4 KB boundary."""
        bpb = self.DATA_WIDTH // 8
        bg = 0x5A
        cases = [  # (offset from the channel's base, bytes)
            (1, 1), (bpb - 1, 2), (7 % bpb, 100), (0, bpb + 5), (17 % bpb, 3 * bpb),
            (0x1000 - 2 * bpb + 3, 6 * bpb + 11),
        ]
        errors = []
        for i, (off, n) in enumerate(cases):
            ch = i % self.NUM_CHANNELS
            base = self.BASE_ADDRESS + ch * self.CHANNEL_OFFSET + i * 0x4000
            addr = base + off
            payload = bytes(random.getrandbits(8) for _ in range(n))
            rel = addr - self.BASE_ADDRESS
            lo = rel - rel % bpb
            span = (off % bpb) + n
            span = span + (-span % bpb)
            self.memory_model.write(lo, bytearray([bg] * span))
            words, strbs = self.pack_bytes(payload, bpb)
            await self.send_descriptor(ch, addr, 0, length_bytes=n)
            await self.send_axis_packet(ch, words, last=True, strbs=strbs)
            bad = "nothing landed"
            for _ in range(40):
                await self.wait_clocks(self.clk_name, 50)
                bad = self._compare_bytes(rel, payload, bg)
                if not bad:
                    break
            err = int(self.dut.sched_error.value)
            self.log.info(f"  case {i}: ch{ch} addr=0x{addr:X} bytes={n} ({len(words)} stream beats) "
                          f"-> {'PASS' if not bad and not err else 'FAIL'}")
            if bad:
                errors.append(f"case {i} (off {off}, {n} B): {bad}")
            if err:
                errors.append(f"case {i}: sched_error=0x{err:X}")
        # packet contract: a packet longer than its descriptor flags the channel
        ch = self.NUM_CHANNELS - 1
        addr = self.BASE_ADDRESS + ch * self.CHANNEL_OFFSET + 0x20000
        words, strbs = self.pack_bytes(bytes(range(40)), bpb)
        await self.send_descriptor(ch, addr, 0, length_bytes=39)
        await self.send_axis_packet(ch, words, last=True, strbs=strbs)
        flagged = False
        for _ in range(40):
            await self.wait_clocks(self.clk_name, 20)
            if (int(self.dut.sched_error.value) >> ch) & 1:
                flagged = True
                break
        self.log.info(f"  contract: 40-byte packet on a 39-byte descriptor -> "
                      f"{'flagged' if flagged else 'NOT flagged'}")
        if not flagged:
            errors.append("length mismatch did not raise sched_error")
        for e in errors:
            self.log.error(f"  {e}")
        return (not errors), {'cases': len(cases) + 1, 'errors': errors}

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
                addr = self.BASE_ADDRESS + channel * self.CHANNEL_OFFSET + i * 0x1000
                beats = random.randint(1, 8)

                # A descriptor with no data behind it can never complete, so give
                # the channel its beats first and require the transfer to finish
                # (the old scenario sent bare descriptors and passed either way).
                test_data = [random.getrandbits(self.DATA_WIDTH) for _ in range(beats)]
                await self.send_axis_packet(channel, test_data, last=True)
                await self.wait_clocks(self.clk_name, 10)

                # Send descriptor
                await self.send_descriptor(channel, addr, beats)

                # Wait for scheduler to process (poll up to 1000 cycles)
                sched_idle = 0
                for _ in range(20):
                    await self.wait_clocks(self.clk_name, 50)
                    sched_idle = int(self.dut.sched_idle.value)
                    if (sched_idle >> channel) & 1:
                        break

                # Check scheduler state
                if (sched_idle >> channel) & 1:
                    # Scheduler returned to idle (processed descriptor)
                    successful += 1
                    self.test_stats['successful_operations'] += 1
                else:
                    self.log.error(f"Descriptor {i}: channel {channel} did not return to idle")
                    failed += 1
                    self.test_stats['failed_operations'] += 1

                delay = self.get_timing_value('inter_op_delay')
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

        # Send descriptors to multiple channels
        for ch in range(num_channels):
            for d in range(descriptors_per_channel):
                try:
                    addr = self.BASE_ADDRESS + ch * self.CHANNEL_OFFSET + d * 0x1000
                    beats = 4

                    await self.send_descriptor(ch, addr, beats)
                    successful += 1
                    self.test_stats['successful_operations'] += 1

                    # Small delay between sends
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

    async def test_axis_reception(self, num_packets: int = 16) -> Tuple[bool, Dict[str, Any]]:
        """Test AXIS data reception

        CRITICAL: Data flow is AXIS -> SRAM -> AXI Write
        We must send AXIS data BEFORE the descriptor so there's data in SRAM
        for the write engine to drain when the scheduler commands the write.
        """
        self.log.info(f"Testing AXIS reception ({num_packets} packets)...")

        # Sample the reservation counter across the whole ingress window. Without
        # this, the sink tests cannot see an alloc-accounting fault at all: they
        # score a packet on whether send_axis_packet threw, so ~64 beats pass
        # cleanly while r_pending_alloc sits underflowed at 16'hFFFF.
        self.pending_alloc_samples = []
        _pa_sampler = cocotb.start_soon(self.sample_pending_alloc(cycles=2000))

        successful = 0
        failed = 0

        for i in range(num_packets):
            try:
                channel = i % self.NUM_CHANNELS
                beats = random.randint(1, 4)

                # Generate test data
                test_data = [random.getrandbits(self.DATA_WIDTH) for _ in range(beats)]

                addr = self.BASE_ADDRESS + channel * self.CHANNEL_OFFSET + i * 0x1000

                # CRITICAL FIX: Send AXIS data FIRST!
                # Data must be in SRAM before scheduler can command write engine
                await self.send_axis_packet(channel, test_data, last=True)
                await self.wait_clocks(self.clk_name, 10)

                # NOW send descriptor to command scheduler to drain SRAM
                await self.send_descriptor(channel, addr, beats)

                # Wait for processing
                await self.wait_clocks(self.clk_name, 50)

                successful += 1
                self.test_stats['successful_operations'] += 1

                delay = self.get_timing_value('axis_delay')
                await self.wait_clocks(self.clk_name, delay)

            except Exception as e:
                self.log.error(f"AXIS packet {i} failed: {e}")
                failed += 1
                self.test_stats['failed_operations'] += 1

        self.test_stats['total_operations'] += num_packets

        _pa_sampler.kill()
        self.assert_pending_alloc_sane()

        stats = {
            'successful': successful,
            'failed': failed,
            'total': num_packets,
            'success_rate': successful / num_packets if num_packets > 0 else 0
        }

        return failed == 0, stats

    def get_scheduler_state_str(self, state_val: int) -> str:
        """Convert scheduler state one-hot value to string"""
        # From rapids_pkg.sv channel_state_t (one-hot encoded)
        # CH_IDLE=0, CH_FETCH_DESC=1, CH_XFER_DATA=2, CH_COMPLETE=3, CH_NEXT_DESC=4, CH_ERROR=5
        states = ['IDLE', 'FETCH_DESC', 'XFER_DATA', 'COMPLETE', 'NEXT_DESC', 'ERROR', 'UNK']
        for i, name in enumerate(states[:-1]):
            if state_val == (1 << i):
                return name
        return f"UNKNOWN({state_val:02X})"

    def debug_scheduler_state(self, channel: int):
        """Debug output for scheduler state"""
        try:
            sched_idle = int(self.dut.sched_idle.value)
            sched_state_arr = self.dut.sched_state.value
            sched_error = int(self.dut.sched_error.value)

            # Try to get state for this channel
            ch_state = int(sched_state_arr[channel]) if hasattr(sched_state_arr, '__getitem__') else int(sched_state_arr)
            ch_idle = (sched_idle >> channel) & 1
            ch_error = (sched_error >> channel) & 1

            self.log.info(f"  Scheduler ch{channel}: state={self.get_scheduler_state_str(ch_state)}, "
                         f"idle={ch_idle}, error={ch_error}")
        except Exception as e:
            self.log.warning(f"  Could not read scheduler state for ch{channel}: {e}")

    def _compare_memory(self, relative_addr: int, beats) -> str:
        """Compare consecutive beats in the AXI slave's memory with the words that
        went in on AXIS. Returns '' when every beat matches, else a description.
        (The old check accepted any non-zero byte at the first beat.)"""
        bpb = self.DATA_WIDTH // 8
        mask = (1 << self.DATA_WIDTH) - 1
        for b, word in enumerate(beats):
            got = self.memory_model.bytearray_to_integer(self.memory_model.read(relative_addr + b * bpb, bpb))
            if got != (int(word) & mask):
                return f"beat {b} at 0x{relative_addr + b * bpb:X}: memory 0x{got:X}, sent 0x{int(word) & mask:X}"
        return ""

    async def test_axi_write_operations(self, num_operations: int = 12) -> Tuple[bool, Dict[str, Any]]:
        """Test AXI write operations

        CRITICAL: Data flow is AXIS -> SRAM -> AXI Write
        We must send AXIS data BEFORE the descriptor so there's data in SRAM
        for the write engine to drain when the scheduler commands the write.

        TIMING FIX: The full data path (AXIS->SRAM->drain->AXI W->B response) takes
        1000+ clocks per operation. We separate stimulus from verification:
        1. Phase 1: Send all AXIS data + descriptors (quick)
        2. Phase 2: Wait for all AXI writes to complete
        3. Phase 3: Verify all memory locations
        """
        self.log.info(f"Testing AXI write operations ({num_operations})...")

        # Track operation metadata for later verification
        operations = []
        beats = 4

        # =========================================================================
        # PHASE 1: STIMULUS - Send all AXIS data and descriptors
        # =========================================================================
        self.log.info("=== PHASE 1: Sending all stimulus ===")

        for i in range(num_operations):
            try:
                channel = i % self.NUM_CHANNELS
                addr = self.BASE_ADDRESS + channel * self.CHANNEL_OFFSET + i * 0x1000
                test_data = [0xDEAD0000 + i + b for b in range(beats)]

                self.log.info(f"Op {i}: ch{channel} addr=0x{addr:08X}")

                # Store operation metadata for verification
                operations.append({
                    'index': i,
                    'channel': channel,
                    'addr': addr,
                    'beats': beats,
                    'test_data': test_data
                })

                # Send AXIS data FIRST (into SRAM buffer)
                await self.send_axis_packet(channel, test_data, last=True)

                # Small wait for AXIS data to buffer
                await self.wait_clocks(self.clk_name, 10)

                # Send descriptor (triggers scheduler to drain SRAM to AXI)
                await self.send_descriptor(channel, addr, beats)

                # Small inter-operation delay
                await self.wait_clocks(self.clk_name, 5)

            except Exception as e:
                self.log.error(f"Stimulus for op {i} failed: {e}")

        # =========================================================================
        # PHASE 2: WAIT - Allow all AXI writes to complete
        # =========================================================================
        # The data path takes 100-200 clocks per operation, plus pipeline delays.
        # With 8 channels sharing one AXI interface, operations are serialized.
        # Wait: base_time + (operations * time_per_op)
        clocks_per_op = 150  # Empirically determined from timing analysis
        total_wait = num_operations * clocks_per_op + 500  # Extra margin

        self.log.info(f"=== PHASE 2: Waiting {total_wait} clocks for all writes to complete ===")
        await self.wait_clocks(self.clk_name, total_wait)

        # =========================================================================
        # PHASE 3: VERIFICATION - Check all memory locations
        # =========================================================================
        self.log.info("=== PHASE 3: Verifying all memory writes ===")

        successful = 0
        failed = 0

        for op in operations:
            i = op['index']
            addr = op['addr']
            channel = op['channel']

            # Check memory model for write
            bytes_to_read = self.DATA_WIDTH // 8
            relative_addr = addr - self.BASE_ADDRESS

            try:
                bad = self._compare_memory(relative_addr, op['test_data'])
                if not bad:
                    successful += 1
                    self.test_stats['axi_writes_completed'] += 1
                    self.test_stats['successful_operations'] += 1
                    self.log.info(f"Op {i} ch{channel}: PASS - {op['beats']} beats match at 0x{addr:X}")
                else:
                    self.log.error(f"Op {i} ch{channel}: FAIL - {bad}")
                    failed += 1
                    self.test_stats['failed_operations'] += 1
            except Exception as e:
                self.log.warning(f"Op {i} ch{channel}: FAIL - memory read error at 0x{addr:X}: {e}")
                failed += 1
                self.test_stats['failed_operations'] += 1

        self.test_stats['total_operations'] += num_operations

        stats = {
            'successful': successful,
            'failed': failed,
            'total': num_operations,
            'success_rate': successful / num_operations if num_operations > 0 else 0
        }

        self.log.info(f"AXI write operations: {stats}")
        return failed == 0, stats

    async def test_end_to_end_flow(self, num_transfers: int = 8) -> Tuple[bool, Dict[str, Any]]:
        """Test end-to-end data flow

        CRITICAL: Data flow is AXIS -> SRAM -> AXI Write
        We must send AXIS data BEFORE the descriptor so there's data in SRAM
        for the write engine to drain when the scheduler commands the write.
        """
        self.log.info(f"Testing end-to-end flow ({num_transfers} transfers)...")

        successful = 0
        failed = 0

        for i in range(num_transfers):
            try:
                channel = i % self.NUM_CHANNELS
                addr = self.BASE_ADDRESS + channel * self.CHANNEL_OFFSET + i * 0x2000
                beats = random.randint(2, 8)
                test_data = [random.getrandbits(self.DATA_WIDTH) for _ in range(beats)]

                # CRITICAL FIX: Send AXIS data FIRST!
                # Data must be in SRAM before scheduler can command write engine
                await self.send_axis_packet(channel, test_data, last=True)
                await self.wait_clocks(self.clk_name, 20)

                # NOW send descriptor - tells scheduler to drain SRAM to memory
                await self.send_descriptor(channel, addr, beats, eos=(i == num_transfers - 1))

                # Wait for the write to LAND, rather than assuming a fixed
                # delay. This used to wait exactly 150 clocks and read once,
                # so a transfer that needed longer -- more beats, or the
                # shared AXI interface still draining another channel -- read
                # back zeros and was reported as "no memory write". That is
                # why this test failed intermittently (7 of 8 transfers
                # passing) with nothing wrong in the DUT. Same total budget
                # or better: up to 20 x 50 = 1000 clocks, and a transfer that
                # genuinely never writes still fails, just later.
                bytes_to_read = self.DATA_WIDTH // 8
                relative_addr = addr - self.BASE_ADDRESS
                mem_data = None
                for _ in range(20):
                    await self.wait_clocks(self.clk_name, 50)
                    mem_data = self.memory_model.read(relative_addr, bytes_to_read)
                    if mem_data and any(b != 0 for b in mem_data):
                        break
                bad = self._compare_memory(relative_addr, test_data)
                if not bad:
                    successful += 1
                    self.test_stats['successful_operations'] += 1
                    self.log.debug(f"E2E transfer {i} successful: ch{channel}, addr=0x{addr:X}")
                else:
                    self.log.error(f"E2E transfer {i}: {bad}")
                    failed += 1
                    self.test_stats['failed_operations'] += 1
                    self.log.warning(f"E2E transfer {i} failed: no memory write")

            except Exception as e:
                self.log.error(f"E2E transfer {i} failed: {e}")
                failed += 1
                self.test_stats['failed_operations'] += 1

        self.test_stats['total_operations'] += num_transfers

        stats = {
            'successful': successful,
            'failed': failed,
            'total': num_transfers,
            'success_rate': successful / num_transfers if num_transfers > 0 else 0
        }

        return failed == 0, stats

    async def _wait_memory(self, relative_addr: int, beats, polls: int, clocks: int = 100) -> str:
        """Poll the AXI slave's memory until every beat landed, or the budget
        (polls x clocks) runs out. Returns '' on success, else the mismatch."""
        bad = "nothing landed"
        for _ in range(polls):
            await self.wait_clocks(self.clk_name, clocks)
            bad = self._compare_memory(relative_addr, beats)
            if not bad:
                return ""
        return bad

    async def test_residue_full_burst(self) -> Tuple[bool, Dict[str, Any]]:
        """rapids BUG-009, second mechanism: a packet that ends mid-segment
        shifts the ingress allocation phase, and a later transfer whose burst
        equals the buffer depth must still complete.

        The ingress allocates SRAM in ALLOC_SIZE segments. Before the fix it
        allocated only whole segments, so after a 4-beat packet (12 beats of
        its segment left allocated) the last 4 slots of a 128-deep buffer could
        never be allocated again until something drained -- and the write
        engine, waiting for a 128-beat burst, needed exactly those slots. On
        the Genesys 2 the second run accepted 124 beats and issued no AW.
        Here: a 4-beat transfer, then 2 x depth beats with the burst set to the
        depth; the second transfer must land in memory."""
        depth = self.SRAM_DEPTH // self.NUM_CHANNELS   # the DUT's SRAM_DEPTH is the total; per channel is what the burst sees
        ch = 0
        addr = self.BASE_ADDRESS + ch * self.CHANNEL_OFFSET
        short = [random.getrandbits(self.DATA_WIDTH) for _ in range(4)]
        await self.send_axis_packet(ch, short, last=True)
        await self.wait_clocks(self.clk_name, 20)
        await self.send_descriptor(ch, addr, len(short))
        bad = await self._wait_memory(addr - self.BASE_ADDRESS, short, polls=20)
        if bad:
            return False, {'phase': 'short transfer', 'error': bad}
        self.log.info("short transfer landed; ingress now holds a partial segment")

        self.dut.cfg_axi_wr_xfer_beats.value = depth - 1
        await self.wait_clocks(self.clk_name, 5)
        # 32 buffers' worth, as on the board (4096 beats at 128 deep): the
        # partial allocations the residue forces recur at every refill, and the
        # allocation-view race they expose (an allocation that returns to
        # "nothing pending" before the space view reports it) needs the
        # repetition to surface.
        n = 32 * depth
        data = [random.getrandbits(self.DATA_WIDTH) for _ in range(n)]
        addr2 = addr + 0x8000
        # The packet is longer than the buffer, so it can only finish while the
        # engine drains: descriptor first, the packet streams in the background.
        await self.send_descriptor(ch, addr2, n)
        sender = cocotb.start_soon(self.send_axis_packet(ch, data, last=True))
        bad = await self._wait_memory(addr2 - self.BASE_ADDRESS, data, polls=800, clocks=100)
        if bad:
            sender.cancel()   # the ingress is wedged; do not hang the test on it
            self.log.error(f"full-depth burst after a partial segment: {bad}")
            return False, {'phase': 'full-depth burst', 'depth': depth, 'error': bad}
        await sender
        return True, {'phase': 'done', 'depth': depth, 'beats': n}

    async def stress_test(self, num_operations: int = 32) -> Tuple[bool, Dict[str, Any]]:
        """Stress test with high throughput

        CRITICAL: Data flow is AXIS -> SRAM -> AXI Write
        We must send AXIS data BEFORE the descriptor so there's data in SRAM
        for the write engine to drain when the scheduler commands the write.
        """
        self.log.info(f"Running stress test ({num_operations} operations)...")

        successful = 0
        failed = 0

        for i in range(num_operations):
            try:
                channel = random.randint(0, self.NUM_CHANNELS - 1)
                addr = self.BASE_ADDRESS + channel * self.CHANNEL_OFFSET + random.randint(0, 0xFFFF) * 64
                beats = random.randint(1, 8)
                test_data = [random.getrandbits(self.DATA_WIDTH) for _ in range(beats)]

                # CRITICAL FIX: Send AXIS data FIRST!
                # Data must be in SRAM before scheduler can command write engine
                await self.send_axis_packet(channel, test_data, last=True)

                # Random delay after data
                delay = random.randint(1, 10)
                await self.wait_clocks(self.clk_name, delay)

                # NOW send descriptor - tells scheduler to drain SRAM to memory
                await self.send_descriptor(channel, addr, beats)

                # Short wait
                await self.wait_clocks(self.clk_name, random.randint(10, 30))

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

    def assert_pending_alloc_sane(self):
        """Reserved beats can never exceed the SRAM that backs them.

        This is the check the existing sink tests do NOT make.
        test_axis_reception scores a packet on whether send_axis_packet threw --
        never on the reservation accounting -- so it sends ~64 beats and passes
        even while r_pending_alloc sits at 16'hFFFF. The alloc path computes
        pending + alloc_size - 1 when it allocates and consumes in the same
        cycle, so an alloc_size of 0 underflows 0 -> 16'hFFFF and licenses 65535
        unreserved beats. Bounding pending by SRAM_DEPTH is what makes that
        visible.

        Armed: raises if it never sampled, so a silent pass cannot masquerade
        as a clean one.
        """
        if not self.pending_alloc_samples:
            raise AssertionError(
                'pending_alloc check never sampled -- the check is not armed')
        worst = max(self.pending_alloc_samples)
        # Self-validation: with a non-zero reservation size and traffic sent,
        # pending MUST have been observed non-zero at some point. An all-zero
        # trace means the observation point is broken (wrong hierarchy path or
        # wrong slicing), not that the design is healthy -- and a broken
        # observation point passes the bound check trivially.
        if self.ALLOC_SIZE > 0 and worst == 0:
            raise AssertionError(
                f'observation point appears broken: {len(self.pending_alloc_samples)} '
                f'samples of r_pending_alloc were all zero while cfg_alloc_size='
                f'{self.ALLOC_SIZE} and AXIS traffic was sent. Check the hierarchy '
                f'path and the packed-array decode before trusting this check.')
        if worst > self.SRAM_DEPTH:
            raise AssertionError(
                f'r_pending_alloc reached {worst} (0x{worst:04x}), which exceeds '
                f'SRAM_DEPTH={self.SRAM_DEPTH}: beats reserved that the SRAM '
                f'cannot hold. cfg_alloc_size={self.ALLOC_SIZE}. '
                f'{len(self.pending_alloc_samples)} samples taken.')
        self.log.info(
            f'pending_alloc proof: max {worst} <= SRAM_DEPTH {self.SRAM_DEPTH} '
            f'over {len(self.pending_alloc_samples)} samples '
            f'(cfg_alloc_size={self.ALLOC_SIZE})')

    async def sample_pending_alloc(self, cycles: int = 400):
        """Record r_pending_alloc across the ingress window."""
        for _ in range(cycles):
            await self.wait_clocks(self.clk_name, 1)
            try:
                # r_pending_alloc is logic [NC-1:0][15:0]. Indexing .value[ch]
                # selects a single BIT, not a channel word -- that read 'max 0'
                # at cfg_alloc_size=16 and would have passed on the 0xFFFF
                # underflow too. Decode the packed value into 16-bit fields.
                raw = int(self.dut.u_sink_data_path_axis.r_pending_alloc.value)
                for ch in range(self.NUM_CHANNELS):
                    self.pending_alloc_samples.append((raw >> (16 * ch)) & 0xFFFF)
            except Exception:
                # Single sample failure must not mask the run; an empty sample
                # list is what assert_pending_alloc_sane treats as unarmed.
                pass
