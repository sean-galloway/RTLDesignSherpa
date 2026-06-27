# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Test-bench harness for ddr2_lpddr2_core_macro (AXI-to-DFI macro).

Same shape as DDR2LPDDR2TopTB but WITHOUT APB / CSR — the core macro's
cfg surface (memtype, t_refi, t_rcd, ...) is driven directly by this
TB at reset, so there's no need for the APBMaster + RegisterMap pair
the top-level TB carries.

Two live BFMs:
  * AXI4MasterWrite + AXI4MasterRead    → host AXI traffic
  * DFISlavePHY + MemoryModel           → DFI loopback with preloadable
                                          DRAM

Use `set_axi_timing_per_channel(aw=, w=, b=, ar=, r=)` to apply a
different AXI_RANDOMIZER_CONFIGS profile to each AXI channel — feeds
the profile-sweep matrix.
"""

from __future__ import annotations

import logging
from typing import Optional

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, RisingEdge, Timer

from CocoTBFramework.components.axi4.axi4_interfaces import (
    AXI4MasterRead, AXI4MasterWrite,
)
from CocoTBFramework.components.dfi.dfi_base import DFIBase
from CocoTBFramework.components.dfi.dfi_signals import DFIVersion, MemoryType
from CocoTBFramework.components.dfi.dfi_slave_phy import DFISlavePHY
from CocoTBFramework.components.dfi.dram_state import (
    AddressMapping, DramStateModel, ViolationPolicy,
)
from CocoTBFramework.components.dfi.jedec_timings import builtin_timings
from CocoTBFramework.components.shared.memory_model import MemoryModel


# DDR2 timing defaults — match what the CSR-driven path normally programs.
# Derived from ddr2-650-mt47h64m16hr.
_DDR2_DEFAULTS = dict(
    t_refi  = 1024,  # mc_clk cycles between refreshes (loose for sim)
    t_rcd   = 4,
    t_rp    = 4,
    t_ras   = 11,
    t_rc    = 15,
    t_wr    = 4,
    t_wtr   = 2,
    t_rtp   = 4,
    t_faw   = 18,
    t_rrd   = 3,
    t_phy_wrlat   = 4,
    t_rddata_en   = 4,
)


class DDR2LPDDR2CoreMacroTB:
    """End-to-end TB for ddr2_lpddr2_core_macro."""

    def __init__(self, dut, *, mc_period_ns: int = 7,
                 axi_data_width: int = 64, axi_id_width: int = 4,
                 axi_addr_width: int = 32,
                 num_ranks: int = 1, num_banks: int = 8,
                 row_width: int = 14, col_width: int = 10) -> None:
        self.dut = dut
        self.log = logging.getLogger("ddr2_lpddr2_core_macro_tb")
        self.log.setLevel(logging.INFO)
        self.mc_period_ns = mc_period_ns
        self.axi_data_width = axi_data_width
        self.axi_id_width = axi_id_width
        self.axi_addr_width = axi_addr_width

        self.num_ranks = num_ranks
        self.num_banks = num_banks
        self.row_width = row_width
        self.col_width = col_width
        self.bytes_per_beat = axi_data_width // 8

        mapping_str = ("rank|row|bank|col" if num_ranks > 1
                       else "row|bank|col")
        self.mapping = AddressMapping(
            num_ranks=num_ranks,
            num_banks=num_banks,
            num_rows=1 << row_width,
            num_cols=1 << col_width,
            mapping=mapping_str,
        )

        num_lines = num_ranks * num_banks * (1 << row_width) * (1 << col_width)
        self.memory = MemoryModel(
            num_lines=num_lines,
            bytes_per_line=self.bytes_per_beat,
            log=self.log,
        )

        # Same BL=4 lock-step contract as the top-level TB.
        self.dram_bl = 4
        self.dfi_base = DFIBase(
            dfi_version=DFIVersion.V2_1,
            memory_type=MemoryType.DDR2,
            timings=builtin_timings("ddr2-650-mt47h64m16hr"),
            mapping=self.mapping,
            beats_per_burst=self.dram_bl,
        )

        self.axi_master_wr: Optional[AXI4MasterWrite] = None
        self.axi_master_rd: Optional[AXI4MasterRead] = None
        self.dfi_slave: Optional[DFISlavePHY] = None

    async def reset(self, *, mem_type: str = "DDR2",
                    init_complete_delay: int = 20) -> None:
        self.dut.memtype_i.value      = 1 if mem_type.upper() == "LPDDR2" else 0
        self.dut.t_refi_i.value       = _DDR2_DEFAULTS["t_refi"]
        self.dut.t_rcd_i.value        = _DDR2_DEFAULTS["t_rcd"]
        self.dut.t_rp_i.value         = _DDR2_DEFAULTS["t_rp"]
        self.dut.t_ras_i.value        = _DDR2_DEFAULTS["t_ras"]
        self.dut.t_rc_i.value         = _DDR2_DEFAULTS["t_rc"]
        self.dut.t_wr_i.value         = _DDR2_DEFAULTS["t_wr"]
        self.dut.t_wtr_i.value        = _DDR2_DEFAULTS["t_wtr"]
        self.dut.t_rtp_i.value        = _DDR2_DEFAULTS["t_rtp"]
        self.dut.t_faw_i.value        = _DDR2_DEFAULTS["t_faw"]
        self.dut.t_rrd_i.value        = _DDR2_DEFAULTS["t_rrd"]
        self.dut.t_phy_wrlat_i.value  = _DDR2_DEFAULTS["t_phy_wrlat"]
        self.dut.t_rddata_en_i.value  = _DDR2_DEFAULTS["t_rddata_en"]
        self.dut.rd_in_order_i.value  = 1
        self.dut.enable_pde_i.value   = 0
        self.dut.enable_sref_i.value  = 0

        # DFI-side inputs the BFM doesn't drive
        self.dut.phy_dfi_init_complete.value = 0
        self.dut.phy_dfi_ctrlupd_ack.value   = 0
        self.dut.phy_dfi_phyupd_req.value    = 0
        self.dut.phy_dfi_phyupd_type.value   = 0

        cocotb.start_soon(Clock(self.dut.mc_clk,
                                self.mc_period_ns, units="ns").start())

        self.dut.mc_rst_n.value = 0
        await Timer(80, units="ns")
        self.dut.mc_rst_n.value = 1
        await ClockCycles(self.dut.mc_clk, 10)

        async def _init_complete_after(n: int) -> None:
            await ClockCycles(self.dut.mc_clk, n)
            self.dut.phy_dfi_init_complete.value = 1
        cocotb.start_soon(_init_complete_after(init_complete_delay))

    def init_dfi_slave(self, *, strict_violations: bool = False) -> DFISlavePHY:
        self.dfi_slave = DFISlavePHY(
            self.dut, self.dut.mc_clk,
            base=self.dfi_base, memory=self.memory,
        )
        if not strict_violations:
            self.dfi_slave.dram = DramStateModel(
                timings=self.dfi_base.timings,
                num_banks=self.dfi_base.mapping.num_banks,
                policy=ViolationPolicy(hard=frozenset()),
            )
        return self.dfi_slave

    def init_axi_masters(self) -> tuple[AXI4MasterWrite, AXI4MasterRead]:
        self.axi_master_wr = AXI4MasterWrite(
            self.dut, self.dut.mc_clk, prefix="s_axi",
            data_width=self.axi_data_width, id_width=self.axi_id_width,
            addr_width=self.axi_addr_width, log=self.log,
        )
        self.axi_master_rd = AXI4MasterRead(
            self.dut, self.dut.mc_clk, prefix="s_axi",
            data_width=self.axi_data_width, id_width=self.axi_id_width,
            addr_width=self.axi_addr_width, log=self.log,
        )
        return self.axi_master_wr, self.axi_master_rd

    def set_axi_timing_per_channel(
        self,
        aw: str = "fast",
        w:  str = "fast",
        b:  str = "fast",
        ar: str = "fast",
        r:  str = "fast",
    ) -> None:
        from CocoTBFramework.components.shared.flex_randomizer import (
            FlexRandomizer,
        )
        from TBClasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS

        if self.axi_master_wr is None or self.axi_master_rd is None:
            raise RuntimeError(
                "init_axi_masters() must be called first"
            )
        for name in (aw, w, b, ar, r):
            if name not in AXI_RANDOMIZER_CONFIGS:
                raise ValueError(f"unknown profile '{name}'")
        m = "master"
        s = "slave"
        self.axi_master_wr.aw_channel.randomizer = FlexRandomizer(
            AXI_RANDOMIZER_CONFIGS[aw][m])
        self.axi_master_wr.w_channel.randomizer  = FlexRandomizer(
            AXI_RANDOMIZER_CONFIGS[w][m])
        self.axi_master_wr.b_channel.randomizer  = FlexRandomizer(
            AXI_RANDOMIZER_CONFIGS[b][s])
        self.axi_master_rd.ar_channel.randomizer = FlexRandomizer(
            AXI_RANDOMIZER_CONFIGS[ar][m])
        self.axi_master_rd.r_channel.randomizer  = FlexRandomizer(
            AXI_RANDOMIZER_CONFIGS[r][s])
        self.log.info(
            "AXI per-channel timing: aw=%s w=%s b=%s ar=%s r=%s",
            aw, w, b, ar, r,
        )

    def preload_memory(self, byte_addr: int, data: bytes | bytearray) -> None:
        if not isinstance(data, (bytes, bytearray)):
            raise TypeError(f"data must be bytes/bytearray, got {type(data)}")
        self.memory.write(byte_addr, bytearray(data))

    def peek_memory(self, byte_addr: int, length: int) -> bytearray:
        return self.memory.read(byte_addr, length)

    async def wait_for_init_done(self, timeout_cycles: int = 10_000) -> None:
        for _ in range(timeout_cycles):
            await RisingEdge(self.dut.mc_clk)
            if int(self.dut.status_init_done.value):
                self.log.info("init_done observed")
                return
        raise TimeoutError(
            f"status_init_done did not assert within {timeout_cycles} cycles"
        )
