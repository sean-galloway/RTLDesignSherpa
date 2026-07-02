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
