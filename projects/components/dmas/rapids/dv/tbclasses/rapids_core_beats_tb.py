# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: RapidsCoreBeatsTB
# Purpose: RAPIDS Core (beats) SPLIT-core integration testbench
#
# Documentation: projects/components/dmas/rapids/PRD.md
# Subsystem: rapids_macro_beats
#
# Author: sean galloway
# Created: 2026-06-30

"""
RAPIDS Core (beats) SPLIT-core integration testbench.

rapids_core_beats is now a thin wrapper over TWO wholly-independent halves:
  - SOURCE half (u_src): memory -> AXIS.  Descriptor's src_addr is read from
    system memory (m_axi_rd) into SRAM and streamed out on m_axis (tid=channel).
  - SINK   half (u_snk): AXIS -> memory.  Incoming s_axis beats (tid=channel)
    are buffered into SRAM and written to system memory (m_axi_wr) at dst_addr.

Each half is configured via raw cfg_* inputs (src_/snk_ prefixed) and kicked via
its own packed APB descriptor-kick bus (src_apb_*/snk_apb_*). Descriptors are
fetched by the descriptor engine from a 256-bit AXI4 read slave (per half).

External interfaces driven / responded to by this TB:
  - src_apb_valid/ready/addr [NC]   : SOURCE per-channel descriptor kick
  - snk_apb_valid/ready/addr [NC]   : SINK   per-channel descriptor kick
  - src_m_axi_desc_* (256b read)    : SOURCE descriptor fetch -> AXI4 read slave
  - snk_m_axi_desc_* (256b read)    : SINK   descriptor fetch -> AXI4 read slave
  - m_axi_rd_*  (DW read)           : SOURCE data read  -> AXI4 read slave (rd_mem)
  - m_axi_wr_*  (DW write)          : SINK   data write -> AXI4 write slave (wr_mem)
  - m_axis_*    (DW stream out)     : SOURCE egress  -> captured by TB monitor
  - s_axis_*    (DW stream in)      : SINK   ingress -> driven by AXIS master
  - {src,snk}_m_axi_ctrlrd/ctrlwr_* : Phase-2 control masters -> quiescent AXI
                                       slaves (tied off so AR/AW never hang)
  - mon_valid/ready/packet          : single monitor bus (mon_ready held high)
"""

import os
import random
from typing import Dict, Any, List, Tuple

import cocotb
from cocotb.triggers import RisingEdge

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.axi4.axi4_factories import (
    create_axi4_slave_rd, create_axi4_slave_wr)
from CocoTBFramework.components.axis4.axis_factories import (
    create_axis_master, create_axis_slave)


class RapidsCoreBeatsTB(TBBase):
    """Split-core integration testbench for rapids_core_beats."""

    def __init__(self, dut, clk=None, rst_n=None):
        super().__init__(dut)

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

        # Clock / reset
        self.clk = clk if clk is not None else dut.clk
        self.clk_name = self.clk._name if hasattr(self.clk, '_name') else 'clk'
        self.rst_n = rst_n if rst_n is not None else dut.rst_n

        # Address regions (each memory model is 0-based; base_addr translates)
        self.DESC_BASE = 0x3000_0000    # descriptor storage (non-zero: 0 = null ptr)
        self.SRC_BASE = 0x1000_0000     # source data (m_axi_rd)
        self.DST_BASE = 0x2000_0000     # sink data destination (m_axi_wr)
        self.CHANNEL_OFFSET = 0x0010_0000

        bpl = self.DATA_WIDTH // 8
        self.desc_src_mem = MemoryModel(num_lines=4096, bytes_per_line=32, log=self.log)
        self.desc_snk_mem = MemoryModel(num_lines=4096, bytes_per_line=32, log=self.log)
        self.rd_mem = MemoryModel(num_lines=(32 * self.CHANNEL_OFFSET) // bpl,
                                  bytes_per_line=bpl, log=self.log)
        self.wr_mem = MemoryModel(num_lines=(32 * self.CHANNEL_OFFSET) // bpl,
                                  bytes_per_line=bpl, log=self.log)
        # Small memory models backing the (unused) Phase-2 control masters.
        self.ctrl_mem = {}

        # BFMs (created after reset)
        self.desc_src_slave = None
        self.desc_snk_slave = None
        self.rd_slave = None
        self.wr_slave = None
        self.axis_master = None       # drives s_axis_* (sink ingress)
        self.axis_out_slave = None    # consumes m_axis_* (source egress)
        self.ctrl_slaves = []

        # source-egress capture (background monitor)
        self.captured_axis = {ch: [] for ch in range(self.NUM_CHANNELS)}
        self._mon_active = False
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
        d = self.dut
        # Idle the raw-driven inputs during reset (fill/drain are GONE).
        d.src_apb_valid.value = 0
        d.src_apb_addr.value = 0
        d.snk_apb_valid.value = 0
        d.snk_apb_addr.value = 0
        # AXIS ingress idle until the master BFM takes over.
        d.s_axis_tvalid.value = 0
        # AXIS egress + monitor consumers held ready.
        d.m_axis_tready.value = 1
        d.mon_ready.value = 1

    async def deassert_reset(self):
        self.rst_n.value = 1

    # =========================================================================
    # CONFIGURATION (raw cfg_* inputs, per half)
    # =========================================================================

    def _cfg_half(self, pfx: str):
        """Drive one half's src_/snk_ prefixed cfg_* inputs."""
        d = self.dut

        def s(name, val):
            getattr(d, f'{pfx}_{name}').value = val

        s('cfg_channel_enable', (1 << self.NUM_CHANNELS) - 1)
        s('cfg_channel_reset', 0)

        s('cfg_sched_enable', 1)
        s('cfg_sched_timeout_cycles', 1_000_000)
        s('cfg_sched_timeout_limit', 0xFF)
        s('cfg_sched_timeout_enable', 0)   # disable timeout->error in basic tests
        s('cfg_sched_err_enable', 1)
        s('cfg_sched_compl_enable', 1)
        s('cfg_sched_perf_enable', 0)

        s('cfg_desceng_enable', 1)
        s('cfg_desceng_prefetch', 1)
        s('cfg_desceng_fifo_thresh', 4)
        s('cfg_desceng_addr0_base', 0)
        s('cfg_desceng_addr0_limit', 0xFFFF_FFFF_FFFF_FFFF)
        s('cfg_desceng_addr1_base', 0)
        s('cfg_desceng_addr1_limit', 0xFFFF_FFFF_FFFF_FFFF)

        s('cfg_ctrlrd_max_try', 1)
        s('tick_1us', 0)

        s('cfg_desc_mon_enable', 1)
        s('cfg_desc_mon_err_enable', 1)
        s('cfg_desc_mon_perf_enable', 0)
        s('cfg_desc_mon_timeout_enable', 0)
        s('cfg_desc_mon_timeout_cycles', 1_000_000)
        s('cfg_desc_mon_latency_thresh', 100_000)
        s('cfg_desc_mon_pkt_mask', 0xFFFF)
        s('cfg_desc_mon_err_select', 0)
        for m in ('err', 'timeout', 'compl', 'thresh', 'perf', 'addr', 'debug'):
            getattr(d, f'{pfx}_cfg_desc_mon_{m}_mask').value = 0xFF

    def _configure(self):
        """Drive cfg_* before reset for BOTH halves + direction-unique cfg."""
        d = self.dut
        self._cfg_half('src')
        self._cfg_half('snk')

        # Direction-unique config (no prefix).
        d.cfg_axi_rd_xfer_beats.value = 8   # source read burst sizing
        d.cfg_drain_size.value = 1          # source: min beats before egress arb
        d.cfg_axi_wr_xfer_beats.value = 8   # sink write burst sizing
        d.cfg_alloc_size.value = 16         # sink: SRAM alloc per AXIS fill

    # =========================================================================
    # BFM SETUP
    # =========================================================================

    def _create_bfms(self):
        d = self.dut

        # Descriptor fetch read slaves (256-bit), one per half.
        self.desc_src_slave = create_axi4_slave_rd(
            dut=d, clock=self.clk, prefix="src_m_axi_desc_", log=self.log,
            data_width=self.DESC_WIDTH, id_width=self.AXI_ID_WIDTH,
            addr_width=self.ADDR_WIDTH, user_width=1, multi_sig=True,
            memory_model=self.desc_src_mem, base_addr=self.DESC_BASE)
        self.desc_snk_slave = create_axi4_slave_rd(
            dut=d, clock=self.clk, prefix="snk_m_axi_desc_", log=self.log,
            data_width=self.DESC_WIDTH, id_width=self.AXI_ID_WIDTH,
            addr_width=self.ADDR_WIDTH, user_width=1, multi_sig=True,
            memory_model=self.desc_snk_mem, base_addr=self.DESC_BASE)

        # Source data read slave (memory -> source).
        self.rd_slave = create_axi4_slave_rd(
            dut=d, clock=self.clk, prefix="m_axi_rd_", log=self.log,
            data_width=self.DATA_WIDTH, id_width=self.AXI_ID_WIDTH,
            addr_width=self.ADDR_WIDTH, user_width=1, multi_sig=True,
            memory_model=self.rd_mem, base_addr=self.SRC_BASE)

        # Sink data write slave (sink -> memory).
        self.wr_slave = create_axi4_slave_wr(
            dut=d, clock=self.clk, prefix="m_axi_wr_", log=self.log,
            data_width=self.DATA_WIDTH, id_width=self.AXI_ID_WIDTH,
            addr_width=self.ADDR_WIDTH, user_width=1, multi_sig=True,
            memory_model=self.wr_mem, base_addr=self.DST_BASE)

        # Phase-2 control masters: quiescent 32-bit AXI slaves so AR/AW never hang.
        for pfx in ('src_m_axi_ctrlrd_', 'snk_m_axi_ctrlrd_'):
            self.ctrl_mem[pfx] = MemoryModel(num_lines=256, bytes_per_line=4, log=self.log)
            self.ctrl_slaves.append(create_axi4_slave_rd(
                dut=d, clock=self.clk, prefix=pfx, log=self.log,
                data_width=32, id_width=self.AXI_ID_WIDTH,
                addr_width=self.ADDR_WIDTH, user_width=1, multi_sig=True,
                memory_model=self.ctrl_mem[pfx], base_addr=0))
        for pfx in ('src_m_axi_ctrlwr_', 'snk_m_axi_ctrlwr_'):
            self.ctrl_mem[pfx] = MemoryModel(num_lines=256, bytes_per_line=4, log=self.log)
            self.ctrl_slaves.append(create_axi4_slave_wr(
                dut=d, clock=self.clk, prefix=pfx, log=self.log,
                data_width=32, id_width=self.AXI_ID_WIDTH,
                addr_width=self.ADDR_WIDTH, user_width=1, multi_sig=True,
                memory_model=self.ctrl_mem[pfx], base_addr=0))

        # AXIS master drives s_axis_* (sink ingress).
        self.axis_master = create_axis_master(
            dut=d, clock=self.clk, prefix="s_axis_", log=self.log,
            data_width=self.DATA_WIDTH, id_width=8, dest_width=4, user_width=1)

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

    # =========================================================================
    # DESCRIPTOR + MEMORY HELPERS
    # =========================================================================

    def create_descriptor(self, src_addr, dst_addr, length, gen_irq=False,
                          last=True, channel_id=0) -> int:
        desc = 0
        desc |= (src_addr & ((1 << 64) - 1))
        desc |= (dst_addr & ((1 << 64) - 1)) << 64
        desc |= (length & 0xFFFFFFFF) << 128
        desc |= (0 << 160)                        # next_descriptor_ptr
        desc |= (1 << 192)                        # valid
        desc |= ((1 if gen_irq else 0) << 193)
        desc |= ((1 if last else 0) << 194)
        desc |= (0 << 195)                        # error
        desc |= ((channel_id & 0xF) << 196)
        return desc

    def register_descriptor(self, mem, desc_addr, desc_data):
        """Write a 256-bit descriptor into a desc memory model at desc_addr."""
        mem.write(desc_addr - self.DESC_BASE, bytearray(desc_data.to_bytes(32, 'little')))

    def preload_source(self, src_addr, beats: List[int]):
        bpl = self.DATA_WIDTH // 8
        off = src_addr - self.SRC_BASE
        for i, val in enumerate(beats):
            self.rd_mem.write(off + i * bpl, bytearray(val.to_bytes(bpl, 'little')))

    def read_sink(self, dst_addr, nbeats) -> List[int]:
        bpl = self.DATA_WIDTH // 8
        off = dst_addr - self.DST_BASE
        out = []
        for i in range(nbeats):
            b = self.wr_mem.read(off + i * bpl, bpl)
            out.append(int.from_bytes(bytes(b), 'little'))
        return out

    # =========================================================================
    # STIMULUS: APB kick (per half), AXIS send, egress capture
    # =========================================================================

    async def send_apb_request(self, half, channel, addr, timeout=500) -> bool:
        """Kick a channel to fetch a descriptor at addr (packed apb bus)."""
        valid_sig = getattr(self.dut, f'{half}_apb_valid')
        addr_sig = getattr(self.dut, f'{half}_apb_addr')
        rdy_sig = getattr(self.dut, f'{half}_apb_ready')

        self._set_packed_bit(valid_sig, channel, 1)
        self._set_array_element(addr_sig, channel, self.ADDR_WIDTH, addr)
        accepted = False
        for _ in range(timeout):
            if self._get_packed_bit(rdy_sig, channel) == 1:
                await self.wait_clocks(self.clk_name, 1)
                accepted = True
                break
            await self.wait_clocks(self.clk_name, 1)
        self._set_packed_bit(valid_sig, channel, 0)
        if not accepted:
            self.log.warning(f"APB kick timeout {half} ch{channel} addr=0x{addr:X}")
            self.test_errors.append(f"apb_timeout_{half}_ch{channel}")
        return accepted

    async def send_axis_packet(self, channel, beats: List[int]):
        """Drive a sink-ingress packet on s_axis (tid=channel; tlast on final)."""
        axis = self.axis_master['interface']
        n = len(beats)
        for i, val in enumerate(beats):
            pkt = axis.create_packet(
                data=val,
                strb=(1 << self.STRB_WIDTH) - 1,
                id=channel,
                dest=0,
                user=0,
                last=int(i == n - 1),
            )
            await axis.send(pkt)

    async def axis_egress_monitor(self):
        """Background: hold m_axis_tready high, capture source-egress beats."""
        self._mon_active = True
        self.dut.m_axis_tready.value = 1
        while self._mon_active:
            await RisingEdge(self.dut.clk)
            try:
                if (int(self.dut.m_axis_tvalid.value) == 1 and
                        int(self.dut.m_axis_tready.value) == 1):
                    tid = int(self.dut.m_axis_tid.value) & (self.NUM_CHANNELS - 1)
                    self.captured_axis.setdefault(tid, []).append(
                        int(self.dut.m_axis_tdata.value))
            except Exception:
                pass

    async def monbus_consumer(self):
        self.dut.mon_ready.value = 1
        while self._mon_active:
            await RisingEdge(self.dut.clk)

    async def initialize_test(self):
        self._mon_active = True
        cocotb.start_soon(self.axis_egress_monitor())
        cocotb.start_soon(self.monbus_consumer())
        await self.wait_clocks(self.clk_name, 2)

    def finalize_test(self):
        self._mon_active = False

    # =========================================================================
    # STATUS HELPERS
    # =========================================================================

    async def wait_half_idle(self, half, timeout_cycles=20000) -> bool:
        sig = getattr(self.dut, f'{half}_system_idle')
        for _ in range(timeout_cycles):
            await self.wait_clocks(self.clk_name, 1)
            try:
                if int(sig.value) == 1:
                    return True
            except Exception:
                pass
        return False

    # =========================================================================
    # TEST METHODS
    # =========================================================================

    async def test_source_path(self, channel=0, beats=4) -> Tuple[bool, Dict[str, Any]]:
        """SOURCE: memory -> AXIS. Preload memory, kick descriptor, capture m_axis."""
        self.log.info(f"=== SOURCE path: ch{channel}, {beats} beats ===")
        desc_addr = self.DESC_BASE + channel * 0x1000
        src_addr = self.SRC_BASE + channel * self.CHANNEL_OFFSET

        pattern = [(0x5000_0000_0000_0000 + (channel << 40) + i) for i in range(beats)]
        self.preload_source(src_addr, pattern)

        desc = self.create_descriptor(src_addr, 0, beats, channel_id=channel)
        self.register_descriptor(self.desc_src_mem, desc_addr, desc)

        await self.send_apb_request('src', channel, desc_addr)

        # Poll for egress completion (all beats captured) with timeout.
        for _ in range(4000):
            await self.wait_clocks(self.clk_name, 1)
            if len(self.captured_axis.get(channel, [])) >= beats:
                break
        await self.wait_clocks(self.clk_name, 50)

        got = self.captured_axis.get(channel, [])
        errors = list(self.test_errors)
        if len(got) < beats:
            errors.append(f"source ch{channel}: captured {len(got)}/{beats} beats")
        else:
            mism = sum(1 for a, b in zip(got[:beats], pattern) if a != b)
            if mism:
                errors.append(f"source ch{channel}: {mism}/{beats} beat mismatches")
                for i, (a, b) in enumerate(zip(got[:beats], pattern)):
                    if a != b:
                        self.log.error(f"  beat[{i}] got=0x{a:X} exp=0x{b:X}")
        stats = {'captured': len(got), 'expected': beats, 'errors': errors}
        if errors:
            for e in errors:
                self.log.error(f"  SCOREBOARD: {e}")
        else:
            self.log.info(f"  SCOREBOARD: source verified ({beats} beats)")
        return (len(errors) == 0), stats

    async def test_sink_path(self, channel=0, beats=4) -> Tuple[bool, Dict[str, Any]]:
        """SINK: AXIS -> memory. Kick descriptor, stream s_axis, verify wr_mem."""
        self.log.info(f"=== SINK path: ch{channel}, {beats} beats ===")
        desc_addr = self.DESC_BASE + channel * 0x1000
        dst_addr = self.DST_BASE + channel * self.CHANNEL_OFFSET

        pattern = [(0xA000_0000_0000_0000 + (channel << 40) + i) for i in range(beats)]

        desc = self.create_descriptor(0, dst_addr, beats, channel_id=channel)
        self.register_descriptor(self.desc_snk_mem, desc_addr, desc)

        # Stream AXIS data into SRAM FIRST (buffers per-channel), then kick drain.
        await self.send_axis_packet(channel, pattern)
        await self.wait_clocks(self.clk_name, 20)
        await self.send_apb_request('snk', channel, desc_addr)

        # Wait for the write path to drain to memory.
        await self.wait_half_idle('snk', timeout_cycles=20000)
        await self.wait_clocks(self.clk_name, 200)

        got = self.read_sink(dst_addr, beats)
        errors = list(self.test_errors)
        if got != pattern:
            mism = sum(1 for a, b in zip(got, pattern) if a != b)
            errors.append(f"sink ch{channel} @0x{dst_addr:X}: {mism}/{beats} beats mismatch")
            for i, (a, b) in enumerate(zip(got, pattern)):
                if a != b:
                    self.log.error(f"  beat[{i}] got=0x{a:X} exp=0x{b:X}")
        stats = {'errors': errors}
        if errors:
            for e in errors:
                self.log.error(f"  SCOREBOARD: {e}")
        else:
            self.log.info(f"  SCOREBOARD: sink verified ({beats} beats)")
        return (len(errors) == 0), stats
