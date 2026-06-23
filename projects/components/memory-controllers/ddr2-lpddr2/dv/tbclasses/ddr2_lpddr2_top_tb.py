# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Test-bench harness for ddr2_lpddr2_top.

Glues:
  - APBMaster + RegisterMap                       → CSR programming
  - AXI4MasterWrite + AXI4MasterRead              → host traffic
  - AXI4Sequence + run_axi4_sequence              → canned workloads
  - Minimal DFI terminator coroutine              → keeps the bus alive

The DFI side is a stub today (asserts dfi_init_complete after reset
and parks rddata = 0). End-to-end DRAM loopback will come from
DFISlavePHY once a JedecTimings preset is wired up.
"""

from __future__ import annotations

import logging
import os
from typing import Optional, Sequence

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, RisingEdge, Timer

from CocoTBFramework.components.apb.apb_components import APBMaster
from CocoTBFramework.components.apb.apb_packet import APBPacket
from CocoTBFramework.components.axi4.axi4_interfaces import (
    AXI4MasterRead, AXI4MasterWrite,
)
from CocoTBFramework.components.axi4.axi4_sequence import (
    AXI4Sequence, run_axi4_sequence,
)

from TBClasses.apb.register_map import RegisterMap


class DDR2LPDDR2TopTB:
    """End-to-end TB for ddr2_lpddr2_top."""

    REGMAP_FILE = os.path.join(
        os.path.dirname(__file__), "ddr2_lpddr2_regmap.py"
    )

    def __init__(self, dut, *, mc_period_ns: int = 7, pclk_period_ns: int = 10,
                 axi_data_width: int = 64, axi_id_width: int = 4,
                 axi_addr_width: int = 32) -> None:
        self.dut = dut
        self.log = logging.getLogger("ddr2_lpddr2_top_tb")
        self.log.setLevel(logging.INFO)
        self.mc_period_ns = mc_period_ns
        self.pclk_period_ns = pclk_period_ns
        self.axi_data_width = axi_data_width
        self.axi_id_width = axi_id_width
        self.axi_addr_width = axi_addr_width

        self.apb_master: Optional[APBMaster] = None
        self.axi_master_wr: Optional[AXI4MasterWrite] = None
        self.axi_master_rd: Optional[AXI4MasterRead] = None
        self.reg_map: Optional[RegisterMap] = None

    # ---- bring-up ---------------------------------------------------------

    async def reset(self) -> None:
        """Apply mc_clk + pclk reset; tie off externals; release."""
        # Tie off non-CSR control inputs
        self.dut.memtype_i.value      = 0   # memtype_e DDR2
        self.dut.t_phy_wrlat_i.value  = 4
        self.dut.t_rddata_en_i.value  = 4
        self.dut.rd_in_order_i.value  = 1
        self.dut.cap_lookahead_max_i.value = 0
        self.dut.cap_synth_mask_i.value    = 0b111

        # Tie off DFI inputs (PHY side)
        self.dut.dfi_init_complete_i.value = 0
        self.dut.dfi_rddata_i.value        = 0
        self.dut.dfi_rddata_valid_i.value  = 0
        self.dut.dfi_ctrlupd_ack_i.value   = 0
        self.dut.dfi_phyupd_req_i.value    = 0
        self.dut.dfi_phyupd_type_i.value   = 0

        # Tie off APB master signals (will be re-driven by APBMaster)
        self.dut.s_apb_PSEL.value    = 0
        self.dut.s_apb_PENABLE.value = 0
        self.dut.s_apb_PADDR.value   = 0
        self.dut.s_apb_PWRITE.value  = 0
        self.dut.s_apb_PWDATA.value  = 0
        self.dut.s_apb_PSTRB.value   = 0
        self.dut.s_apb_PPROT.value   = 0

        cocotb.start_soon(Clock(self.dut.mc_clk,
                                self.mc_period_ns, units="ns").start())
        cocotb.start_soon(Clock(self.dut.pclk,
                                self.pclk_period_ns, units="ns").start())

        self.dut.mc_rst_n.value = 0
        self.dut.presetn.value  = 0
        await Timer(80, units="ns")
        self.dut.mc_rst_n.value = 1
        self.dut.presetn.value  = 1
        await ClockCycles(self.dut.mc_clk, 10)

        # Start the DFI terminator coroutine — it asserts init_complete and
        # parks rddata at 0.
        cocotb.start_soon(self._dfi_terminator())

    async def _dfi_terminator(self) -> None:
        """Minimal DFI 'PHY': wait a few cycles, assert init_complete, idle."""
        await ClockCycles(self.dut.mc_clk, 20)
        self.dut.dfi_init_complete_i.value = 1
        # Idle forever — read returns are not modeled yet.
        while True:
            await ClockCycles(self.dut.mc_clk, 1000)

    # ---- BFM bring-up -----------------------------------------------------

    def init_register_map(self) -> RegisterMap:
        self.reg_map = RegisterMap(
            self.REGMAP_FILE,
            apb_data_width=32, apb_addr_width=12,
            start_address=0x0, log=self.log,
        )
        return self.reg_map

    def init_apb_master(self) -> APBMaster:
        self.apb_master = APBMaster(
            entity=self.dut, title="DDR2 CSR APB", prefix="s_apb",
            clock=self.dut.pclk, bus_width=32, addr_width=12, log=self.log,
        )
        return self.apb_master

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

    # ---- High-level APIs --------------------------------------------------

    async def apb_program_register(self, register: str, field: str,
                                   value: int) -> None:
        """Use the RegisterMap to encode one field-write, send via APB.

        RegisterMap's `write()` expects `value` to already be positioned
        at the field's absolute bit offset. Shift the user-supplied
        value here so callers can pass the "field value" naturally
        (e.g. `apb_program_register('REFRESH_TUNING', 'page_policy_or',
        0x2)` instead of `... 0x2 << 2`).
        """
        if self.reg_map is None:
            self.init_register_map()
        if self.apb_master is None:
            raise RuntimeError("call init_apb_master() first")
        offset = self.reg_map.registers[register][field]["offset"]
        lsb = int(offset.split(":")[-1])
        self.reg_map.write(register, field, value << lsb)
        cycles = self.reg_map.generate_apb_cycles()
        for c in cycles:
            await self.apb_master.busy_send(c)
            await RisingEdge(self.dut.pclk)

    async def apb_read_register(self, address: int) -> int:
        if self.apb_master is None:
            raise RuntimeError("call init_apb_master() first")
        packet = APBPacket(
            pwrite=0, paddr=address, pwdata=0, pstrb=0xF, pprot=0,
            data_width=32, addr_width=12, strb_width=4,
        )
        await self.apb_master.busy_send(packet)
        await RisingEdge(self.dut.pclk)
        return int(packet.fields.get("prdata", 0))

    async def wait_for_init_done(self, timeout_cycles: int = 10_000) -> None:
        """Poll STATUS.init_done until set, or timeout."""
        for _ in range(timeout_cycles):
            val = await self.apb_read_register(0x004)  # STATUS
            if val & 0x1:
                self.log.info("init_done observed")
                return
            await ClockCycles(self.dut.pclk, 50)
        raise AssertionError("init_done never asserted within timeout")

    async def run_sequence(self, seq: AXI4Sequence) -> Sequence[dict]:
        if self.axi_master_wr is None or self.axi_master_rd is None:
            raise RuntimeError("call init_axi_masters() first")
        return await run_axi4_sequence(
            seq, master_wr=self.axi_master_wr,
            master_rd=self.axi_master_rd, log=self.log,
        )
