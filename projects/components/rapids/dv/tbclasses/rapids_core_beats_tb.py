# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: RapidsCoreBeatsTB
# Purpose: RAPIDS Core (beats) top-level integration testbench
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids_top_beats
#
# Author: sean galloway
# Created: 2026-06-30

"""
RAPIDS Core (beats) top-level integration testbench.

rapids_core_beats integrates:
  - scheduler_group_array  (APB descriptor kick + descriptor engines + schedulers)
  - sink_data_path         (External fill -> SRAM -> AXI write to memory)
  - source_data_path       (AXI read from memory -> SRAM -> External drain)

External interfaces driven / responded to by this TB (all via framework BFMs
where the interface is a real handshake):
  - apb_valid/ready/addr [NC]       : per-channel descriptor kick (packed bus ->
                                      profile-driven inject delay; see _apb_rnd)
  - m_axi_desc_*  (256-bit read)    : descriptor fetch      -> AXI4 read slave  (desc_mem)
  - m_axi_rd_*    (DW read)         : source data read      -> AXI4 read slave  (rd_mem)
  - m_axi_wr_*    (DW write)        : sink data write       -> AXI4 write slave (wr_mem)
  - snk_fill_*    (id+data)         : sink ingress          -> GAXI master
  - src_drain_*                     : source egress         -> manual drain reader
  - mon_valid/ready/packet (64b)    : monitor bus           -> consumer coroutine

End-to-end per descriptor (src_addr, dst_addr, length):
  SOURCE : rd_mem[src_addr] (preloaded pattern) -> core reads -> src_drain -> TB
           collects -> compare to preloaded pattern.
  SINK   : TB fills known pattern via snk_fill -> core writes -> wr_mem[dst_addr]
           -> TB reads back -> compare to filled pattern.
"""

import os
import random
from typing import Dict, Any, List, Tuple, Optional

import cocotb
from cocotb.triggers import RisingEdge

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_master
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.axi4.axi4_factories import create_axi4_slave_rd, create_axi4_slave_wr


class RapidsCoreBeatsTB(TBBase):
    """Top-level integration testbench for rapids_core_beats."""

    def __init__(self, dut, clk=None, rst_n=None):
        super().__init__(dut)

        # Configuration from environment
        self.NUM_CHANNELS = self.convert_to_int(os.environ.get('TEST_NUM_CHANNELS', '8'))
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '64'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '512'))
        self.AXI_ID_WIDTH = self.convert_to_int(os.environ.get('TEST_AXI_ID_WIDTH', '8'))
        self.SRAM_DEPTH = self.convert_to_int(os.environ.get('TEST_SRAM_DEPTH', '512'))
        self.CLK_PERIOD = self.convert_to_int(os.environ.get('TEST_CLK_PERIOD', '10'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.SEED)

        self.DESC_WIDTH = 256
        self.STRB_WIDTH = self.DATA_WIDTH // 8
        self.chan_id_width = (self.NUM_CHANNELS - 1).bit_length() if self.NUM_CHANNELS > 1 else 1

        # Clock / reset
        self.clk = clk if clk is not None else dut.clk
        self.clk_name = self.clk._name if hasattr(self.clk, '_name') else 'clk'
        self.rst_n = rst_n if rst_n is not None else dut.rst_n

        # Address regions (each memory model is 0-based; base_addr translates)
        self.DESC_BASE = 0x3000_0000          # descriptor storage (m_axi_desc); non-zero
                                              # (descriptor engine treats addr 0 as a null ptr)
        self.SRC_BASE = 0x1000_0000           # source data (m_axi_rd)
        self.DST_BASE = 0x2000_0000           # sink data destination (m_axi_wr)
        self.CHANNEL_OFFSET = 0x0010_0000

        bpl = self.DATA_WIDTH // 8
        self.desc_mem = MemoryModel(num_lines=4096, bytes_per_line=32, log=self.log)
        self.rd_mem = MemoryModel(num_lines=(32 * self.CHANNEL_OFFSET) // bpl,
                                  bytes_per_line=bpl, log=self.log)
        self.wr_mem = MemoryModel(num_lines=(32 * self.CHANNEL_OFFSET) // bpl,
                                  bytes_per_line=bpl, log=self.log)

        # BFMs (created in setup after reset)
        self.desc_slave = None      # m_axi_desc read slave (256-bit)
        self.rd_slave = None        # m_axi_rd read slave (source data)
        self.wr_slave = None        # m_axi_wr write slave (sink data)
        self.snk_fill_master = None  # snk_fill ingress GAXI master
        self._apb_rnd = None         # APB inject-delay randomizer (packed bus)

        # Verification bookkeeping
        self.expected_src = {}       # channel -> list[int] expected drained beats
        self.drained = {ch: [] for ch in range(self.NUM_CHANNELS)}
        self.filled = {}             # channel -> list[int] filled beats (sink)
        self.mon_packets = []
        self._drain_active = False
        self.test_errors = []

    # =========================================================================
    # MANDATORY THREE METHODS
    # =========================================================================

    async def setup_clocks_and_reset(self):
        await self.start_clock(self.clk_name, freq=self.CLK_PERIOD, units='ns')
        self._configure()               # cfg_* before reset
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 15)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 15)
        self._create_bfms()

    async def assert_reset(self):
        self.rst_n.value = 0
        # Idle the raw-driven inputs during reset
        self.dut.apb_valid.value = 0
        self.dut.apb_addr.value = 0
        self.dut.snk_fill_alloc_req.value = 0
        self.dut.snk_fill_alloc_size.value = 0
        self.dut.snk_fill_alloc_id.value = 0
        self.dut.src_drain_req.value = 0
        self.dut.src_drain_size.value = 0
        self.dut.src_drain_read.value = 0
        self.dut.src_drain_id.value = 0
        self.dut.mon_ready.value = 1

    async def deassert_reset(self):
        self.rst_n.value = 1

    # =========================================================================
    # CONFIGURATION
    # =========================================================================

    def _configure(self):
        """Drive cfg_* before reset (mirrors scheduler_group_array + data-path cfg)."""
        d = self.dut
        d.cfg_channel_enable.value = (1 << self.NUM_CHANNELS) - 1
        d.cfg_channel_reset.value = 0
        d.cfg_sched_enable.value = 1
        d.cfg_sched_timeout_cycles.value = 100000
        d.cfg_sched_timeout_enable.value = 1
        d.cfg_sched_err_enable.value = 1
        d.cfg_sched_compl_enable.value = 1
        d.cfg_sched_perf_enable.value = 0

        d.cfg_desceng_enable.value = 1
        d.cfg_desceng_prefetch.value = 1
        d.cfg_desceng_fifo_thresh.value = 4
        d.cfg_desceng_addr0_base.value = 0
        d.cfg_desceng_addr0_limit.value = 0xFFFF_FFFF_FFFF_FFFF
        d.cfg_desceng_addr1_base.value = 0
        d.cfg_desceng_addr1_limit.value = 0xFFFF_FFFF_FFFF_FFFF

        d.cfg_desc_mon_enable.value = 1
        d.cfg_desc_mon_err_enable.value = 1
        d.cfg_desc_mon_perf_enable.value = 0
        d.cfg_desc_mon_timeout_enable.value = 1
        d.cfg_desc_mon_timeout_cycles.value = 100000
        d.cfg_desc_mon_latency_thresh.value = 1000
        d.cfg_desc_mon_pkt_mask.value = 0xFFFF
        d.cfg_desc_mon_err_select.value = 0
        for m in ('err', 'timeout', 'compl', 'thresh', 'perf', 'addr', 'debug'):
            getattr(d, f'cfg_desc_mon_{m}_mask').value = 0xFF

        # AXI transfer beat counts (burst sizing for rd/wr engines)
        d.cfg_axi_rd_xfer_beats.value = 8
        d.cfg_axi_wr_xfer_beats.value = 8

    # =========================================================================
    # BFM SETUP + TIMING PROFILES
    # =========================================================================

    def _create_bfms(self):
        # m_axi_desc: 256-bit descriptor read slave
        self.desc_slave = create_axi4_slave_rd(
            dut=self.dut, clock=self.clk, prefix="m_axi_desc_", log=self.log,
            data_width=self.DESC_WIDTH, id_width=self.AXI_ID_WIDTH,
            addr_width=self.ADDR_WIDTH, user_width=1, multi_sig=True,
            memory_model=self.desc_mem, base_addr=self.DESC_BASE)

        # m_axi_rd: source data read slave
        self.rd_slave = create_axi4_slave_rd(
            dut=self.dut, clock=self.clk, prefix="m_axi_rd_", log=self.log,
            data_width=self.DATA_WIDTH, id_width=self.AXI_ID_WIDTH,
            addr_width=self.ADDR_WIDTH, user_width=1, multi_sig=True,
            memory_model=self.rd_mem, base_addr=self.SRC_BASE)

        # m_axi_wr: sink data write slave
        self.wr_slave = create_axi4_slave_wr(
            dut=self.dut, clock=self.clk, prefix="m_axi_wr_", log=self.log,
            data_width=self.DATA_WIDTH, id_width=self.AXI_ID_WIDTH,
            addr_width=self.ADDR_WIDTH, user_width=1, multi_sig=True,
            memory_model=self.wr_mem, base_addr=self.DST_BASE)

        # snk_fill: sink ingress master (id + data)
        fc = FieldConfig()
        fc.add_field(FieldDefinition(name='id', bits=self.chan_id_width,
                                     format='dec', description='channel id'))
        fc.add_field(FieldDefinition(name='data', bits=self.DATA_WIDTH,
                                     format='hex', description='fill data'))
        self.snk_fill_master = create_gaxi_master(
            dut=self.dut, title='snk_fill', prefix='snk_fill', clock=self.clk,
            field_config=fc, multi_sig=True, log=self.log)

        self._apply_timing_from_env()

    def _apply_timing_from_env(self):
        axi_base = os.environ.get('TIMING_PROFILE', 'fixed')
        self.set_axi_timing_profile(axi_base)
        self.set_gaxi_timing_profile(os.environ.get('GAXI_TIMING_PROFILE', 'backtoback'))

    def set_axi_timing_profile(self, profile_name='fixed'):
        """Apply an AXI profile to the three AXI memory slaves.

        Read slaves (desc, rd): AR uses 'slave'/ready_delay, R uses 'master'/valid_delay.
        Write slave (wr): AW/W use 'slave', B uses 'master'. 'mixed' maps to
        constrained (ar/aw/w) + slow_producer (r/b)."""
        from TBClasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS
        ready_p = 'constrained' if profile_name == 'mixed' else profile_name
        valid_p = 'slow_producer' if profile_name == 'mixed' else profile_name

        def cfg(name, section):
            if name not in AXI_RANDOMIZER_CONFIGS:
                if name not in (None, 'default', 'fixed'):
                    self.log.warning(f"Unknown AXI timing profile '{name}', using 'fixed'")
                name = 'fixed'
            return FlexRandomizer(AXI_RANDOMIZER_CONFIGS[name][section])

        for rd in (self.desc_slave, self.rd_slave):
            rd['interface'].ar_channel.randomizer = cfg(ready_p, 'slave')
            rd['interface'].r_channel.randomizer = cfg(valid_p, 'master')
        wr = self.wr_slave['interface']
        wr.aw_channel.randomizer = cfg(ready_p, 'slave')
        wr.w_channel.randomizer = cfg(ready_p, 'slave')
        wr.b_channel.randomizer = cfg(valid_p, 'master')
        self.log.info(f"AXI memory-slave timing profile: {profile_name}")

    def set_gaxi_timing_profile(self, profile_name='backtoback'):
        """Apply a GAXI profile to the snk_fill master + APB inject-delay randomizer."""
        from TBClasses.amba.amba_random_configs import GAXI_RANDOMIZER_CONFIGS
        if profile_name == 'mixed':
            profile_name = 'gaxi_realistic'
        if profile_name not in GAXI_RANDOMIZER_CONFIGS:
            self.log.warning(f"Unknown GAXI timing profile '{profile_name}', using 'backtoback'")
            profile_name = 'backtoback'
        cfg = GAXI_RANDOMIZER_CONFIGS[profile_name]
        self.snk_fill_master.randomizer = FlexRandomizer(cfg['master'])
        self._apb_rnd = FlexRandomizer(cfg['master'])
        self.log.info(f"GAXI snk_fill + APB-kick timing profile: {profile_name}")

    # =========================================================================
    # PACKED-BUS HELPERS (apb_valid/apb_addr are [NC] / [NC][AW])
    # =========================================================================

    def _set_packed_bit(self, signal, bit_index, value):
        cur = int(signal.value) if signal.value.is_resolvable else 0
        if value:
            cur |= (1 << bit_index)
        else:
            cur &= ~(1 << bit_index)
        signal.value = cur

    def _get_packed_bit(self, signal, bit_index):
        try:
            return (int(signal.value) >> bit_index) & 1
        except Exception:
            return 0

    def _set_array_element(self, signal, element_index, element_width, value):
        try:
            cur = int(signal.value)
        except Exception:
            cur = 0
        mask = ((1 << element_width) - 1) << (element_index * element_width)
        cur &= ~mask
        cur |= (value & ((1 << element_width) - 1)) << (element_index * element_width)
        signal.value = cur

    def _get_array_element(self, signal, element_index, element_width):
        try:
            return (int(signal.value) >> (element_index * element_width)) & ((1 << element_width) - 1)
        except Exception:
            return 0

    # =========================================================================
    # DESCRIPTOR + MEMORY HELPERS
    # =========================================================================

    def create_descriptor(self, src_addr, dst_addr, length, gen_irq=False,
                          last=True, channel_id=0) -> int:
        desc = 0
        desc |= (src_addr & ((1 << 64) - 1))
        desc |= (dst_addr & ((1 << 64) - 1)) << 64
        desc |= (length & 0xFFFFFFFF) << 128
        desc |= (0 << 160)                       # next_descriptor_ptr
        desc |= (1 << 192)                        # valid
        desc |= ((1 if gen_irq else 0) << 193)   # gen_irq
        desc |= ((1 if last else 0) << 194)       # last
        desc |= (0 << 195)                        # error
        desc |= ((channel_id & 0xF) << 196)
        return desc

    def _mem_write(self, mem, base, addr, nbeats_or_bytes):
        pass  # placeholder (unused)

    def register_descriptor(self, desc_addr, desc_data):
        """Write a 256-bit descriptor into desc_mem at desc_addr."""
        data_bytes = bytearray(desc_data.to_bytes(32, 'little'))
        self.desc_mem.write(desc_addr - self.DESC_BASE, data_bytes)

    def preload_source(self, src_addr, beats: List[int]):
        """Preload rd_mem so the source path reads a known pattern from src_addr."""
        bpl = self.DATA_WIDTH // 8
        off = src_addr - self.SRC_BASE
        for i, val in enumerate(beats):
            self.rd_mem.write(off + i * bpl, bytearray(val.to_bytes(bpl, 'little')))

    def read_sink(self, dst_addr, nbeats) -> List[int]:
        """Read back what the sink path wrote to wr_mem at dst_addr."""
        bpl = self.DATA_WIDTH // 8
        off = dst_addr - self.DST_BASE
        out = []
        for i in range(nbeats):
            b = self.wr_mem.read(off + i * bpl, bpl)
            out.append(int.from_bytes(bytes(b), 'little'))
        return out

    # =========================================================================
    # STIMULUS: APB kick, sink fill, source drain
    # =========================================================================

    def _dump_status(self, tag):
        def rd(sig):
            try:
                return int(getattr(self.dut, sig).value)
            except Exception:
                return -1
        self.log.info(f"[STATUS {tag}] system_idle={rd('system_idle')} "
                      f"scheduler_idle=0x{rd('scheduler_idle'):x} "
                      f"descriptor_engine_idle=0x{rd('descriptor_engine_idle'):x} "
                      f"sched_error=0x{rd('sched_error'):x} "
                      f"sched_rd_error=0x{rd('sched_rd_error'):x} "
                      f"sched_wr_error=0x{rd('sched_wr_error'):x} "
                      f"scheduler_state=0x{rd('scheduler_state'):x} "
                      f"apb_valid=0x{rd('apb_valid'):x} apb_ready=0x{rd('apb_ready'):x}")
        self.log.info(f"[DBG    {tag}] r_beats_rcvd={rd('dbg_r_beats_rcvd')} "
                      f"sram_writes={rd('dbg_sram_writes')} "
                      f"rd_all_complete=0x{rd('dbg_rd_all_complete'):x} "
                      f"arb_request=0x{rd('dbg_arb_request'):x} "
                      f"snk_bridge_pending=0x{rd('dbg_snk_sram_bridge_pending'):x} "
                      f"src_bridge_pending=0x{rd('dbg_src_sram_bridge_pending'):x} "
                      f"snk_space_free0={self._get_array_element(self.dut.snk_fill_space_free, 0, (self.SRAM_DEPTH).bit_length())} "
                      f"src_avail0={self._get_array_element(self.dut.src_drain_data_avail, 0, (self.SRAM_DEPTH).bit_length())}")

    async def send_apb_request(self, channel, addr, timeout=200) -> bool:
        """Kick channel to fetch a descriptor at addr (packed apb bus)."""
        if self._apb_rnd is not None:
            delay = int(self._apb_rnd.get_delay('valid_delay'))
            if delay > 0:
                await self.wait_clocks(self.clk_name, delay)
        self._set_packed_bit(self.dut.apb_valid, channel, 1)
        self._set_array_element(self.dut.apb_addr, channel, self.ADDR_WIDTH, addr)
        # apb_ready is combinational (high while the engine can accept); it drops
        # the cycle the kick is consumed. Check ready BEFORE stepping the clock so
        # we observe the valid&&ready handshake cycle, then advance one edge.
        accepted = False
        for _ in range(timeout):
            if self._get_packed_bit(self.dut.apb_ready, channel) == 1:
                await self.wait_clocks(self.clk_name, 1)
                accepted = True
                break
            await self.wait_clocks(self.clk_name, 1)
        self._set_packed_bit(self.dut.apb_valid, channel, 0)
        if not accepted:
            self.log.warning(f"APB kick timeout ch{channel} addr=0x{addr:X}")
            self._dump_status(f"timeout ch{channel}")
            self.test_errors.append(f"apb_timeout_ch{channel}")
        return accepted

    async def alloc_sink(self, channel, size):
        """Reserve sink SRAM space for the fill (one-cycle request)."""
        self.dut.snk_fill_alloc_req.value = 1
        self.dut.snk_fill_alloc_size.value = size
        self.dut.snk_fill_alloc_id.value = channel
        await self.wait_clocks(self.clk_name, 1)
        self.dut.snk_fill_alloc_req.value = 0

    async def fill_sink(self, channel, beats: List[int]):
        """Fill the sink ingress with beats (GAXI master, id+data)."""
        self.filled.setdefault(channel, [])
        for val in beats:
            pkt = self.snk_fill_master.create_packet(id=channel, data=val)
            await self.snk_fill_master.send(pkt)
            self.filled[channel].append(val)

    def _drain_avail(self, channel):
        return self._get_packed_bit(self.dut.src_drain_valid, channel)

    async def source_drainer(self):
        """Background coroutine: continuously drain any channel that has source
        egress data available, collecting beats into self.drained."""
        self._drain_active = True
        scw = (self.SRAM_DEPTH).bit_length()
        while self._drain_active:
            await RisingEdge(self.dut.clk)
            for ch in range(self.NUM_CHANNELS):
                if self._drain_avail(ch):
                    # request + read one beat from this channel
                    self._set_packed_bit(self.dut.src_drain_req, ch, 1)
                    self._set_array_element(self.dut.src_drain_size, ch, 8, 1)
                    self.dut.src_drain_id.value = ch
                    self.dut.src_drain_read.value = 1
                    await RisingEdge(self.dut.clk)
                    if self._drain_avail(ch):
                        try:
                            self.drained[ch].append(int(self.dut.src_drain_data.value))
                        except Exception:
                            pass
                    self.dut.src_drain_read.value = 0
                    self._set_packed_bit(self.dut.src_drain_req, ch, 0)
                    break

    async def monbus_consumer(self):
        """Background coroutine: collect monbus packets (mon_ready held high)."""
        self.dut.mon_ready.value = 1
        while self._drain_active:
            await RisingEdge(self.dut.clk)
            try:
                if int(self.dut.mon_valid.value) == 1 and int(self.dut.mon_ready.value) == 1:
                    self.mon_packets.append(int(self.dut.mon_packet.value))
            except Exception:
                pass

    async def desc_snoop(self):
        """Passive snoop of the m_axi_desc AR/R channels to confirm what the
        descriptor engine requested and received (debug bring-up aid)."""
        while self._drain_active:
            await RisingEdge(self.dut.clk)
            try:
                if int(self.dut.m_axi_desc_arvalid.value) == 1 and int(self.dut.m_axi_desc_arready.value) == 1:
                    self.log.debug(f"[DESC-AR] addr=0x{int(self.dut.m_axi_desc_araddr.value):X} "
                                   f"len={int(self.dut.m_axi_desc_arlen.value)} "
                                   f"size={int(self.dut.m_axi_desc_arsize.value)}")
                if int(self.dut.m_axi_desc_rvalid.value) == 1 and int(self.dut.m_axi_desc_rready.value) == 1:
                    self.log.debug(f"[DESC-R] data=0x{int(self.dut.m_axi_desc_rdata.value):064X} "
                                   f"resp={int(self.dut.m_axi_desc_rresp.value)} "
                                   f"last={int(self.dut.m_axi_desc_rlast.value)}")
            except Exception:
                pass

    async def initialize_test(self):
        """Start background monitors (drainer + monbus consumer)."""
        self._drain_active = True
        cocotb.start_soon(self.source_drainer())
        cocotb.start_soon(self.monbus_consumer())
        cocotb.start_soon(self.desc_snoop())
        await self.wait_clocks(self.clk_name, 2)

    def finalize_test(self):
        self._drain_active = False

    # =========================================================================
    # STATUS HELPERS
    # =========================================================================

    def is_system_idle(self) -> bool:
        try:
            return int(self.dut.system_idle.value) == 1
        except Exception:
            return False

    def scheduler_idle(self, channel) -> bool:
        return self._get_packed_bit(self.dut.scheduler_idle, channel) == 1

    async def wait_system_idle(self, timeout_cycles=20000) -> bool:
        for _ in range(timeout_cycles):
            await self.wait_clocks(self.clk_name, 1)
            if self.is_system_idle():
                return True
        return False

    # =========================================================================
    # TEST METHODS
    # =========================================================================

    async def _run_channel_transfer(self, channel, beats, desc_slot=0):
        """Set up + kick one descriptor on a channel. Returns (src_addr,dst_addr,pattern)."""
        desc_addr = self.DESC_BASE + channel * 0x1000 + desc_slot * 0x100
        src_addr = self.SRC_BASE + channel * self.CHANNEL_OFFSET + desc_slot * 0x4000
        dst_addr = self.DST_BASE + channel * self.CHANNEL_OFFSET + desc_slot * 0x4000

        # Preload source memory with a known per-(channel,beat) pattern.
        src_pattern = [(0x5000_0000_0000_0000 + (channel << 40) + (desc_slot << 24) + i)
                       for i in range(beats)]
        self.preload_source(src_addr, src_pattern)
        self.expected_src.setdefault(channel, []).extend(src_pattern)

        # Register the descriptor for the descriptor engine to fetch.
        desc = self.create_descriptor(src_addr, dst_addr, beats, channel_id=channel)
        self.register_descriptor(desc_addr, desc)

        # Sink fill pattern (what we expect written to wr_mem[dst_addr]).
        snk_pattern = [(0xA000_0000_0000_0000 + (channel << 40) + (desc_slot << 24) + i)
                       for i in range(beats)]

        # Reserve sink space, kick the descriptor, then fill the ingress.
        await self.alloc_sink(channel, beats)
        await self.send_apb_request(channel, desc_addr)
        await self.fill_sink(channel, snk_pattern)
        return src_addr, dst_addr, snk_pattern

    async def test_single_channel(self, channel=0, beats=8) -> Tuple[bool, Dict[str, Any]]:
        """Single-channel end-to-end DMA with data-integrity scoreboard."""
        self.log.info(f"=== Single-channel E2E: ch{channel}, {beats} beats ===")
        src_addr, dst_addr, snk_pattern = await self._run_channel_transfer(channel, beats)

        await self.wait_system_idle(timeout_cycles=20000)
        await self.wait_clocks(self.clk_name, 200)

        return self._score([channel], {channel: [(dst_addr, snk_pattern, beats)]})

    async def test_multi_channel(self, num_channels=4, beats=4) -> Tuple[bool, Dict[str, Any]]:
        """Concurrent multi-channel end-to-end DMA."""
        self.log.info(f"=== Multi-channel E2E: {num_channels} channels, {beats} beats ===")
        sink_expect = {}
        chans = list(range(min(num_channels, self.NUM_CHANNELS)))
        for ch in chans:
            _, dst_addr, snk_pattern = await self._run_channel_transfer(ch, beats)
            sink_expect[ch] = [(dst_addr, snk_pattern, beats)]

        await self.wait_system_idle(timeout_cycles=40000)
        await self.wait_clocks(self.clk_name, 400)
        return self._score(chans, sink_expect)

    async def stress_test(self, num_transfers=16, beats=4) -> Tuple[bool, Dict[str, Any]]:
        """Back-to-back transfers spread across channels."""
        self.log.info(f"=== Stress: {num_transfers} transfers ===")
        sink_expect = {}
        for i in range(num_transfers):
            ch = i % self.NUM_CHANNELS
            slot = i // self.NUM_CHANNELS
            _, dst_addr, snk_pattern = await self._run_channel_transfer(ch, beats, desc_slot=slot)
            sink_expect.setdefault(ch, []).append((dst_addr, snk_pattern, beats))
            await self.wait_clocks(self.clk_name, 10)

        await self.wait_system_idle(timeout_cycles=60000)
        await self.wait_clocks(self.clk_name, 500)
        chans = sorted(sink_expect.keys())
        return self._score(chans, sink_expect)

    # =========================================================================
    # SCOREBOARD
    # =========================================================================

    def _score(self, channels, sink_expect) -> Tuple[bool, Dict[str, Any]]:
        errors = list(self.test_errors)

        # SINK direction: wr_mem[dst_addr] must equal filled pattern.
        for ch in channels:
            for (dst_addr, pattern, nbeats) in sink_expect.get(ch, []):
                got = self.read_sink(dst_addr, nbeats)
                if got != pattern:
                    mism = sum(1 for a, b in zip(got, pattern) if a != b)
                    errors.append(f"sink ch{ch} @0x{dst_addr:X}: {mism}/{nbeats} beats mismatch")

        # SOURCE direction: drained beats must equal preloaded pattern (order-preserving).
        for ch in channels:
            exp = self.expected_src.get(ch, [])
            got = self.drained.get(ch, [])
            if len(got) < len(exp):
                errors.append(f"source ch{ch}: drained {len(got)}/{len(exp)} beats")
            else:
                mism = sum(1 for a, b in zip(got, exp) if a != b)
                if mism:
                    errors.append(f"source ch{ch}: {mism} drained-beat mismatches")

        stats = {
            'channels': channels,
            'mon_packets': len(self.mon_packets),
            'errors': errors,
        }
        if errors:
            for e in errors:
                self.log.error(f"  SCOREBOARD: {e}")
        else:
            self.log.info("  SCOREBOARD: all source/sink data verified")
        return (len(errors) == 0), stats
