# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: RapidsBeatsTopTB
# Purpose: rapids_beats_top APB -> register -> config smoke testbench
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids_beats_top
#
# Author: sean galloway
# Created: 2026-07-02

"""
Config-only smoke testbench for rapids_beats_top.

This TB exercises ONLY the APB -> register -> config path (USE_AXI_MONITORS=0):

    s_apb_* -> apb_slave -> cmdrsp_router -> peakrdl_to_cmdrsp
            -> rapids_regs (PeakRDL) -> rapids_config_block -> rapids_core_beats

Everything except the APB slave is tied off / idled so the DUT never launches a
descriptor fetch or data transfer and cannot hang. Register access is BY NAME
via RegisterMap(rapids_regmap.py): addresses are resolved only through the
register map (get_register_offset_map), never hardcoded.

The smoke sequence:
  1. Read VERSION + GLOBAL_STATUS (proves the APB->regblock read path is alive).
  2. Write/read-back several RW base-config registers (proves the write path and
     the whole config chain is functional).
  3. Confirm system_idle / sched_error are resolvable (no X / no hang) after reset.

APB address width note: the base config registers live at 0x100-0x3FF, which a
12-bit APB paddr fully reaches. The monitor block lives at 0x1000+ and needs a
13-bit APB (see stream_top monbus tests); this smoke stays in the base range so
12 bits suffice.
"""

import os
import sys

import cocotb
from cocotb.triggers import RisingEdge

# Framework utilities (PYTHONPATH includes bin/)
from TBClasses.shared.utilities import get_repo_root
from TBClasses.shared.tbbase import TBBase

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from TBClasses.apb.register_map import RegisterMap

# By-name register description generated from rapids_regs.rdl. Using RegisterMap
# means a register split/relocation needs NO TB changes -- only rapids_regmap.py
# is regenerated.
RAPIDS_REGMAP_PATH = os.path.join(
    repo_root, 'projects/components/rapids/rtl/rapids_regmap.py')


class RapidsBeatsTopTB(TBBase):
    """Config-path smoke testbench for rapids_beats_top."""

    def __init__(self, dut):
        super().__init__(dut)

        # Parameters (env-overridable, defaults mirror the RTL defaults).
        self.NUM_CHANNELS = self.convert_to_int(os.environ.get('TEST_NUM_CHANNELS', '8'))
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '64'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '512'))
        self.AXI_ID_WIDTH = self.convert_to_int(os.environ.get('TEST_AXI_ID_WIDTH', '8'))
        self.CLK_PERIOD = self.convert_to_int(os.environ.get('TEST_CLK_PERIOD', '10'))
        self.apb_addr_width = self.convert_to_int(os.environ.get('TEST_APB_ADDR_WIDTH', '12'))
        self.apb_data_width = self.convert_to_int(os.environ.get('TEST_APB_DATA_WIDTH', '32'))

        # Clock / reset (rapids_beats_top uses aclk / aresetn).
        self.clk = dut.aclk
        self.clk_name = 'aclk'
        self.rst_n = dut.aresetn

        # APB master BFM (created in init_apb_master, after reset).
        self.apb_master = None

        # By-name register map. Addresses come ONLY from rapids_regmap.py.
        self.reg_map = RegisterMap(
            RAPIDS_REGMAP_PATH,
            apb_data_width=self.apb_data_width,
            apb_addr_width=self.apb_addr_width,
            start_address=0,
            log=self.log,
        )
        self.reg_offsets = self.reg_map.get_register_offset_map()
        # Reverse map for human-readable logging (offset -> name).
        self._offset_names = {off: name for name, off in self.reg_offsets.items()}

    # =========================================================================
    # MANDATORY THREE METHODS
    # =========================================================================

    async def setup_clocks_and_reset(self):
        """Start clock, tie off/idle everything, reset, then bring up APB master."""
        await self.start_clock(self.clk_name, freq=self.CLK_PERIOD, units='ns')
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 15)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 15)
        await self.init_apb_master()

    async def assert_reset(self):
        """Assert active-low reset and idle every non-APB input so nothing hangs."""
        self.rst_n.value = 0
        d = self.dut

        # Monitor CAM sync-clear (unused with USE_AXI_MONITORS=0).
        d.cam_clear.value = 0

        # APB inputs idle until the APB master takes over (post-reset).
        d.s_apb_psel.value = 0
        d.s_apb_penable.value = 0
        d.s_apb_pwrite.value = 0
        d.s_apb_paddr.value = 0
        d.s_apb_pwdata.value = 0
        d.s_apb_pstrb.value = 0

        # AXI descriptor-fetch master response inputs -> idle (no transactions).
        d.m_axi_desc_arready.value = 0
        d.m_axi_desc_rid.value = 0
        d.m_axi_desc_rdata.value = 0
        d.m_axi_desc_rresp.value = 0
        d.m_axi_desc_rlast.value = 0
        d.m_axi_desc_rvalid.value = 0

        # AXI data-read master response inputs -> idle.
        d.m_axi_rd_arready.value = 0
        d.m_axi_rd_rid.value = 0
        d.m_axi_rd_rdata.value = 0
        d.m_axi_rd_rresp.value = 0
        d.m_axi_rd_rlast.value = 0
        d.m_axi_rd_rvalid.value = 0

        # AXI data-write master response inputs -> idle.
        d.m_axi_wr_awready.value = 0
        d.m_axi_wr_wready.value = 0
        d.m_axi_wr_bid.value = 0
        d.m_axi_wr_bresp.value = 0
        d.m_axi_wr_bvalid.value = 0

        # Sink fill network inputs -> idle (no ingress).
        d.snk_fill_alloc_req.value = 0
        d.snk_fill_alloc_size.value = 0
        d.snk_fill_alloc_id.value = 0
        d.snk_fill_valid.value = 0
        d.snk_fill_id.value = 0
        d.snk_fill_data.value = 0

        # Source drain network inputs -> idle (no egress).
        d.src_drain_req.value = 0
        d.src_drain_size.value = 0
        d.src_drain_read.value = 0
        d.src_drain_id.value = 0

        # AXI-Lite monitor group (tied off internally with USE_AXI_MONITORS=0,
        # but drive the external inputs to safe idle values regardless).
        d.s_axil_err_arvalid.value = 0
        d.s_axil_err_araddr.value = 0
        d.s_axil_err_arprot.value = 0
        d.s_axil_err_rready.value = 0
        d.m_axil_mon_awready.value = 1
        d.m_axil_mon_wready.value = 1
        d.m_axil_mon_bvalid.value = 0
        d.m_axil_mon_bresp.value = 0

        # Monitor cfg inputs -> 0.
        d.cfg_mon_base_addr.value = 0
        d.cfg_mon_limit_addr.value = 0
        d.cfg_mon_flush_watermark.value = 0

    async def deassert_reset(self):
        """Release active-low reset."""
        self.rst_n.value = 1

    # =========================================================================
    # APB MASTER + BY-NAME REGISTER ACCESS
    # =========================================================================

    async def init_apb_master(self):
        """Bring up the framework APB master on s_apb_* (mirrors stream_core_tb)."""
        from CocoTBFramework.components.apb.apb_components import APBMaster
        from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
        from TBClasses.amba.amba_random_configs import APB_MASTER_RANDOMIZER_CONFIGS

        if not hasattr(self.dut, 's_apb_paddr'):
            raise RuntimeError("DUT has no APB interface (s_apb_paddr missing)")

        # rapids_beats_top runs the apb_slave on aclk (pclk = aclk), so the APB
        # master must use aclk.
        self.apb_master = APBMaster(
            entity=self.dut,
            title='RAPIDS APB Master',
            prefix='s_apb',
            clock=self.clk,
            bus_width=self.apb_data_width,
            addr_width=self.apb_addr_width,
            randomizer=FlexRandomizer(APB_MASTER_RANDOMIZER_CONFIGS['fixed']),
            log=self.log,
        )
        await self.apb_master.reset_bus()
        self.log.info("APB master initialized for rapids_beats_top configuration")

    def reg_offset(self, reg_name):
        """Resolve a register's APB offset BY NAME via the RegisterMap.

        Raises KeyError (with a count of known regs) on a typo / stale name so a
        regmap regen mismatch fails loudly rather than silently mis-addressing.
        """
        try:
            return self.reg_offsets[reg_name]
        except KeyError:
            raise KeyError(
                f"register '{reg_name}' not in rapids_regmap.py "
                f"(offset map has {len(self.reg_offsets)} regs)") from None

    async def write_reg(self, reg_name, value):
        """Write an APB register BY NAME (address resolved from rapids_regmap.py)."""
        return await self.write_apb_register(self.reg_offset(reg_name), value,
                                             reg_name=reg_name)

    async def read_reg(self, reg_name):
        """Read an APB register BY NAME (address resolved from rapids_regmap.py)."""
        return await self.read_apb_register(self.reg_offset(reg_name),
                                            reg_name=reg_name)

    async def write_apb_register(self, addr, data, reg_name=None):
        """APB write using the framework APB master (busy_send -> blocking)."""
        if self.apb_master is None:
            raise RuntimeError("APB master not initialized. Call init_apb_master() first.")
        from CocoTBFramework.components.apb.apb_packet import APBPacket

        packet = APBPacket(
            pwrite=1,
            paddr=addr,
            pwdata=data,
            pstrb=0xF,
            pprot=0,
            data_width=self.apb_data_width,
            addr_width=self.apb_addr_width,
            strb_width=self.apb_data_width // 8,
        )
        await self.apb_master.busy_send(packet)
        await RisingEdge(self.clk)

        name = reg_name or self._offset_names.get(addr, f"0x{addr:03X}")
        self.log.info(f"APB WRITE: {name} (0x{addr:03X}) = 0x{data:08X}")

    async def read_apb_register(self, addr, reg_name=None):
        """APB read using the framework APB master. Returns the 32-bit prdata."""
        if self.apb_master is None:
            raise RuntimeError("APB master not initialized. Call init_apb_master() first.")
        from CocoTBFramework.components.apb.apb_packet import APBPacket

        packet = APBPacket(
            pwrite=0,
            paddr=addr,
            pwdata=0,
            pstrb=0xF,
            pprot=0,
            data_width=self.apb_data_width,
            addr_width=self.apb_addr_width,
            strb_width=self.apb_data_width // 8,
        )
        await self.apb_master.busy_send(packet)
        await RisingEdge(self.clk)

        data = packet.fields.get('prdata', 0)
        name = reg_name or self._offset_names.get(addr, f"0x{addr:03X}")
        self.log.info(f"APB READ:  {name} (0x{addr:03X}) = 0x{data:08X}")
        return int(data)

    # =========================================================================
    # STATUS
    # =========================================================================

    def read_status_signals(self):
        """Return (system_idle, sched_error) top outputs; assert they are sane.

        Raises AssertionError if either output is unresolvable (X/Z), which would
        indicate the DUT is stuck / uninitialized rather than idle.
        """
        si_val = self.dut.system_idle.value
        se_val = self.dut.sched_error.value
        assert si_val.is_resolvable, f"system_idle is X/Z: {si_val}"
        assert se_val.is_resolvable, f"sched_error is X/Z: {se_val}"
        system_idle = int(si_val)
        sched_error = int(se_val)
        self.log.info(f"STATUS: system_idle={system_idle}, sched_error=0x{sched_error:X}")
        return system_idle, sched_error


# =============================================================================
# DATAPATH TESTBENCH (extends the config-only smoke TB)
# =============================================================================

import random  # noqa: E402
from typing import Dict, Any, List, Tuple  # noqa: E402

import cocotb  # noqa: E402
from cocotb.triggers import RisingEdge  # noqa: E402

from CocoTBFramework.components.shared.memory_model import MemoryModel  # noqa: E402
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer  # noqa: E402
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_master  # noqa: E402
from CocoTBFramework.components.shared.field_config import (  # noqa: E402
    FieldConfig, FieldDefinition)
from CocoTBFramework.components.axi4.axi4_factories import (  # noqa: E402
    create_axi4_slave_rd, create_axi4_slave_wr)


class RapidsBeatsTopDatapathTB(RapidsBeatsTopTB):
    """End-to-end datapath testbench for rapids_beats_top.

    Extends the config-only smoke TB (RapidsBeatsTopTB) so it inherits the APB
    master + BY-NAME register access unchanged, then adds the FULL beats
    datapath rig ported verbatim from RapidsCoreBeatsTB (memory models, three
    AXI slaves, the snk_fill GAXI master, the src_drain reader, descriptor
    creation, and the source/sink data-integrity scoreboard).

    The ONLY differences vs the core rig, both handled here:
      - config is applied over APB by NAME (see _configure_via_apb) instead of
        poking cfg_* nets directly, and
      - descriptor kickoff is via the per-channel APB kickoff register pair
        (CH<n>_KICKOFF_LOW/HIGH @ 0x000-0x03F -> apbtodescr -> core apb_valid)
        instead of driving the core's apb_valid/apb_addr bus.

    All the m_axi_*/snk_fill_*/src_drain_* top ports match the core exactly, so
    the BFM-creation code transfers unchanged. The parent's assert_reset idles
    every non-APB input for the duration of reset; the datapath BFMs are created
    AFTER reset (in setup_clocks_and_reset) and take over driving from there,
    so the reset-time tie-offs never fight the real drivers.
    """

    def __init__(self, dut):
        super().__init__(dut)

        # Datapath sizing (env-overridable; mirror the core rig defaults).
        self.SRAM_DEPTH = self.convert_to_int(os.environ.get('TEST_SRAM_DEPTH', '512'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.SEED)

        self.DESC_WIDTH = 256
        self.STRB_WIDTH = self.DATA_WIDTH // 8
        self.chan_id_width = (self.NUM_CHANNELS - 1).bit_length() if self.NUM_CHANNELS > 1 else 1

        # Address regions (each memory model is 0-based; base_addr translates).
        # Identical to RapidsCoreBeatsTB so behaviour matches the core rig.
        self.DESC_BASE = 0x3000_0000        # descriptor storage (m_axi_desc); non-zero
        self.SRC_BASE = 0x1000_0000         # source data (m_axi_rd)
        self.DST_BASE = 0x2000_0000         # sink data destination (m_axi_wr)
        self.CHANNEL_OFFSET = 0x0010_0000

        bpl = self.DATA_WIDTH // 8
        self.desc_mem = MemoryModel(num_lines=4096, bytes_per_line=32, log=self.log)
        self.rd_mem = MemoryModel(num_lines=(32 * self.CHANNEL_OFFSET) // bpl,
                                  bytes_per_line=bpl, log=self.log)
        self.wr_mem = MemoryModel(num_lines=(32 * self.CHANNEL_OFFSET) // bpl,
                                  bytes_per_line=bpl, log=self.log)

        # BFMs (created after reset).
        self.desc_slave = None
        self.rd_slave = None
        self.wr_slave = None
        self.snk_fill_master = None

        # Verification bookkeeping.
        self.expected_src = {}
        self.drained = {ch: [] for ch in range(self.NUM_CHANNELS)}
        self.filled = {}
        self._drain_active = False
        self.test_errors = []

    # =========================================================================
    # SETUP: reset (idle) -> APB master -> config-by-name -> datapath BFMs
    # =========================================================================

    async def setup_clocks_and_reset(self):
        # Parent brings up clock, idles every input, resets, and starts the APB
        # master. We then apply config over APB and attach the datapath BFMs.
        await super().setup_clocks_and_reset()
        await self._configure_via_apb()
        self._create_bfms()

    # =========================================================================
    # CONFIG VIA APB (BY NAME)
    # =========================================================================

    async def _configure_via_apb(self):
        """Program the core config over APB using BY-NAME register access.

        Field encodings resolved from rapids_regmap.py (all fields verified):
          SCHED_CONFIG : SCHED_EN[0] TIMEOUT_EN[1] ERR_EN[2] COMPL_EN[3] PERF_EN[4]
          DESCENG_CONFIG: DESCENG_EN[0] PREFETCH_EN[1] FIFO_THRESH[5:2]
          AXI_XFER_CONFIG: RD_XFER_BEATS[7:0] WR_XFER_BEATS[15:8]
          GLOBAL_CTRL  : GLOBAL_EN[0] GLOBAL_RST[1]
          CHANNEL_ENABLE: CH_EN[NUM_CHANNELS-1:0]
        Values mirror RapidsCoreBeatsTB._configure() so top behaviour == core.
        """
        all_ch = (1 << self.NUM_CHANNELS) - 1

        # --- scheduler ---
        await self.write_reg('SCHED_TIMEOUT_CYCLES', 100000)
        await self.write_reg('SCHED_TIMEOUT_LIMIT', 1)   # escalate after one window
        # SCHED_EN | TIMEOUT_EN | ERR_EN | COMPL_EN (PERF off)
        await self.write_reg('SCHED_CONFIG', 0b0_1111)

        # --- descriptor engine ---
        # DESCENG_EN | PREFETCH_EN | FIFO_THRESH=4 (4<<2 = 0x10)
        await self.write_reg('DESCENG_CONFIG', 0x1 | 0x2 | (4 << 2))
        # Address window must cover the descriptor storage region so fetch /
        # chaining validation passes. base=0, limit=0xFFFFFFFF covers DESC_BASE
        # (0x3000_0000). The config block zero-extends these 32-bit regs to 64.
        await self.write_reg('DESCENG_ADDR0_BASE', 0x0000_0000)
        await self.write_reg('DESCENG_ADDR0_LIMIT', 0xFFFF_FFFF)
        await self.write_reg('DESCENG_ADDR1_BASE', 0x0000_0000)
        await self.write_reg('DESCENG_ADDR1_LIMIT', 0xFFFF_FFFF)

        # --- AXI burst sizing (rd/wr engines): 8 beats each ---
        await self.write_reg('AXI_XFER_CONFIG', (8 << 8) | 8)

        # --- enable channels, then globally enable last ---
        await self.write_reg('CHANNEL_ENABLE', all_ch)
        await self.write_reg('GLOBAL_CTRL', 0x1)  # GLOBAL_EN (avoid GLOBAL_RST[1])

        # Let config propagate through rapids_config_block into the core.
        await self.wait_clocks(self.clk_name, 10)
        self.log.info("rapids_beats_top configured via APB (by name)")

    # =========================================================================
    # KICKOFF VIA APB (per-channel LOW/HIGH kickoff register pair)
    # =========================================================================

    def _kickoff_low_offset(self, channel):
        """apbtodescr channel LOW kickoff offset: BASE + channel*8 (bit[2]=0)."""
        return 0x000 + channel * 0x008

    def _kickoff_high_offset(self, channel):
        """apbtodescr channel HIGH kickoff offset: BASE + channel*8 + 4 (bit[2]=1)."""
        return 0x004 + channel * 0x008

    async def kick_off_channel(self, channel, descriptor_addr):
        """Kick a channel by writing the 64-bit descriptor address to its
        LOW/HIGH kickoff register pair (consumed by apbtodescr -> core
        apb_valid/apb_addr). The HIGH write blocks in the APB slave until the
        descriptor engine has accepted the kick (apbtodescr ROUTE state), so a
        completed pair == an accepted descriptor."""
        desc_low = descriptor_addr & 0xFFFF_FFFF
        desc_high = (descriptor_addr >> 32) & 0xFFFF_FFFF
        await self.write_apb_register(self._kickoff_low_offset(channel), desc_low,
                                      reg_name=f"CH{channel}_KICKOFF_LOW")
        await self.write_apb_register(self._kickoff_high_offset(channel), desc_high,
                                      reg_name=f"CH{channel}_KICKOFF_HIGH")
        self.log.info(f"Kicked off ch{channel} via APB with descriptor @ 0x{descriptor_addr:016X}")

    # =========================================================================
    # BFM SETUP + TIMING PROFILES (ported from RapidsCoreBeatsTB)
    # =========================================================================

    def _create_bfms(self):
        self.desc_slave = create_axi4_slave_rd(
            dut=self.dut, clock=self.clk, prefix="m_axi_desc_", log=self.log,
            data_width=self.DESC_WIDTH, id_width=self.AXI_ID_WIDTH,
            addr_width=self.ADDR_WIDTH, user_width=1, multi_sig=True,
            memory_model=self.desc_mem, base_addr=self.DESC_BASE)

        self.rd_slave = create_axi4_slave_rd(
            dut=self.dut, clock=self.clk, prefix="m_axi_rd_", log=self.log,
            data_width=self.DATA_WIDTH, id_width=self.AXI_ID_WIDTH,
            addr_width=self.ADDR_WIDTH, user_width=1, multi_sig=True,
            memory_model=self.rd_mem, base_addr=self.SRC_BASE)

        self.wr_slave = create_axi4_slave_wr(
            dut=self.dut, clock=self.clk, prefix="m_axi_wr_", log=self.log,
            data_width=self.DATA_WIDTH, id_width=self.AXI_ID_WIDTH,
            addr_width=self.ADDR_WIDTH, user_width=1, multi_sig=True,
            memory_model=self.wr_mem, base_addr=self.DST_BASE)

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
        self.set_axi_timing_profile(os.environ.get('TIMING_PROFILE', 'fixed'))
        self.set_gaxi_timing_profile(os.environ.get('GAXI_TIMING_PROFILE', 'backtoback'))

    def set_axi_timing_profile(self, profile_name='fixed'):
        from TBClasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS
        ready_p = 'constrained' if profile_name == 'mixed' else profile_name
        valid_p = 'slow_producer' if profile_name == 'mixed' else profile_name

        def cfg(name, section):
            if name not in AXI_RANDOMIZER_CONFIGS:
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
        from TBClasses.amba.amba_random_configs import GAXI_RANDOMIZER_CONFIGS
        if profile_name == 'mixed':
            profile_name = 'gaxi_realistic'
        if profile_name not in GAXI_RANDOMIZER_CONFIGS:
            profile_name = 'backtoback'
        cfg = GAXI_RANDOMIZER_CONFIGS[profile_name]
        self.snk_fill_master.randomizer = FlexRandomizer(cfg['master'])
        self.log.info(f"GAXI snk_fill timing profile: {profile_name}")

    # =========================================================================
    # PACKED-BUS HELPERS (src_drain_* are [NC] / [NC][W])
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
    # DESCRIPTOR + MEMORY HELPERS (ported from RapidsCoreBeatsTB)
    # =========================================================================

    def create_descriptor(self, src_addr, dst_addr, length, gen_irq=False,
                          last=True, channel_id=0) -> int:
        desc = 0
        desc |= (src_addr & ((1 << 64) - 1))
        desc |= (dst_addr & ((1 << 64) - 1)) << 64
        desc |= (length & 0xFFFFFFFF) << 128
        desc |= (0 << 160)                        # next_descriptor_ptr
        desc |= (1 << 192)                         # valid
        desc |= ((1 if gen_irq else 0) << 193)    # gen_irq
        desc |= ((1 if last else 0) << 194)        # last
        desc |= (0 << 195)                         # error
        desc |= ((channel_id & 0xF) << 196)
        return desc

    def register_descriptor(self, desc_addr, desc_data):
        data_bytes = bytearray(desc_data.to_bytes(32, 'little'))
        self.desc_mem.write(desc_addr - self.DESC_BASE, data_bytes)

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
    # STIMULUS: sink alloc/fill, source drain
    # =========================================================================

    async def alloc_sink(self, channel, size):
        self.dut.snk_fill_alloc_req.value = 1
        self.dut.snk_fill_alloc_size.value = size
        self.dut.snk_fill_alloc_id.value = channel
        await self.wait_clocks(self.clk_name, 1)
        self.dut.snk_fill_alloc_req.value = 0

    async def fill_sink(self, channel, beats: List[int]):
        self.filled.setdefault(channel, [])
        for val in beats:
            pkt = self.snk_fill_master.create_packet(id=channel, data=val)
            await self.snk_fill_master.send(pkt)
            self.filled[channel].append(val)

    def _drain_avail(self, channel):
        return self._get_packed_bit(self.dut.src_drain_valid, channel)

    async def source_drainer(self):
        """Background coroutine: drain any channel with source egress available,
        collecting beats into self.drained (identical logic to the core rig,
        retargeted to aclk)."""
        self._drain_active = True
        while self._drain_active:
            await RisingEdge(self.clk)
            for ch in range(self.NUM_CHANNELS):
                if self._drain_avail(ch):
                    self._set_packed_bit(self.dut.src_drain_req, ch, 1)
                    self._set_array_element(self.dut.src_drain_size, ch, 8, 1)
                    self.dut.src_drain_id.value = ch
                    self.dut.src_drain_read.value = 1
                    await RisingEdge(self.clk)
                    if self._drain_avail(ch):
                        try:
                            self.drained[ch].append(int(self.dut.src_drain_data.value))
                        except Exception:
                            pass
                    self.dut.src_drain_read.value = 0
                    self._set_packed_bit(self.dut.src_drain_req, ch, 0)
                    break

    async def initialize_test(self):
        self._drain_active = True
        cocotb.start_soon(self.source_drainer())
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

    async def wait_system_idle(self, timeout_cycles=20000) -> bool:
        for _ in range(timeout_cycles):
            await self.wait_clocks(self.clk_name, 1)
            if self.is_system_idle():
                return True
        return False

    # =========================================================================
    # END-TO-END TRANSFER + SCOREBOARD
    # =========================================================================

    async def _run_channel_transfer(self, channel, beats, desc_slot=0):
        """Set up + kick one descriptor on a channel via APB.
        Returns (src_addr, dst_addr, sink_pattern)."""
        desc_addr = self.DESC_BASE + channel * 0x1000 + desc_slot * 0x100
        src_addr = self.SRC_BASE + channel * self.CHANNEL_OFFSET + desc_slot * 0x4000
        dst_addr = self.DST_BASE + channel * self.CHANNEL_OFFSET + desc_slot * 0x4000

        src_pattern = [(0x5000_0000_0000_0000 + (channel << 40) + (desc_slot << 24) + i)
                       for i in range(beats)]
        self.preload_source(src_addr, src_pattern)
        self.expected_src.setdefault(channel, []).extend(src_pattern)

        desc = self.create_descriptor(src_addr, dst_addr, beats, channel_id=channel)
        self.register_descriptor(desc_addr, desc)

        snk_pattern = [(0xA000_0000_0000_0000 + (channel << 40) + (desc_slot << 24) + i)
                       for i in range(beats)]

        await self.alloc_sink(channel, beats)
        await self.kick_off_channel(channel, desc_addr)   # <-- APB kickoff (by name)
        await self.fill_sink(channel, snk_pattern)
        return src_addr, dst_addr, snk_pattern

    async def test_single_channel(self, channel=0, beats=8) -> Tuple[bool, Dict[str, Any]]:
        """Single-channel end-to-end DMA with source+sink data-integrity check."""
        self.log.info(f"=== Top datapath E2E: ch{channel}, {beats} beats ===")
        src_addr, dst_addr, snk_pattern = await self._run_channel_transfer(channel, beats)
        await self.wait_system_idle(timeout_cycles=20000)
        await self.wait_clocks(self.clk_name, 200)
        return self._score([channel], {channel: [(dst_addr, snk_pattern, beats)]})

    async def test_multi_descriptor(self, channel=0, beats=6, ndesc=2) -> Tuple[bool, Dict[str, Any]]:
        """One channel, multiple sequential descriptors (distinct slots)."""
        self.log.info(f"=== Top datapath E2E: ch{channel}, {ndesc} descriptors x {beats} beats ===")
        sink_expect = {channel: []}
        for slot in range(ndesc):
            _, dst_addr, snk_pattern = await self._run_channel_transfer(channel, beats, desc_slot=slot)
            sink_expect[channel].append((dst_addr, snk_pattern, beats))
            await self.wait_system_idle(timeout_cycles=20000)
            await self.wait_clocks(self.clk_name, 50)
        await self.wait_clocks(self.clk_name, 200)
        return self._score([channel], sink_expect)

    def _score(self, channels, sink_expect) -> Tuple[bool, Dict[str, Any]]:
        errors = list(self.test_errors)

        # SINK: wr_mem[dst_addr] must equal the filled pattern.
        for ch in channels:
            for (dst_addr, pattern, nbeats) in sink_expect.get(ch, []):
                got = self.read_sink(dst_addr, nbeats)
                if got != pattern:
                    mism = sum(1 for a, b in zip(got, pattern) if a != b)
                    errors.append(f"sink ch{ch} @0x{dst_addr:X}: {mism}/{nbeats} beats mismatch")

        # SOURCE: drained beats must equal the preloaded pattern (order-preserving).
        for ch in channels:
            exp = self.expected_src.get(ch, [])
            got = self.drained.get(ch, [])
            if len(got) < len(exp):
                errors.append(f"source ch{ch}: drained {len(got)}/{len(exp)} beats")
            else:
                mism = sum(1 for a, b in zip(got, exp) if a != b)
                if mism:
                    errors.append(f"source ch{ch}: {mism} drained-beat mismatches")

        stats = {'channels': channels, 'errors': errors,
                 'drained': {ch: len(self.drained.get(ch, [])) for ch in channels}}
        if errors:
            for e in errors:
                self.log.error(f"  SCOREBOARD: {e}")
        else:
            self.log.info("  SCOREBOARD: all source/sink data verified")
        return (len(errors) == 0), stats
