# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: axi_id_side_table_tb
# Purpose: Cocotb TB for axi_id_side_table — a per-AXI-ID metadata
#          side-table. The FUB captures AW/AR attributes on the host
#          handshake and replays user/qos at completion + scheduling
#          time. Pre-G-01-style regressions on this block would
#          silently zero out the per-ID metadata at the lookup stage,
#          which the integration tests above don't catch because they
#          don't check ARUSER → RUSER echo or AWQOS → wr_cmd_cam qos.

"""TB for axi_id_side_table.

The FUB has four lookup contracts the consumer relies on:

  * `aw_push_qos_o   == r_aw_tab[aw_push_id_i].qos`
  * `aw_compl_user_o == r_aw_tab[aw_compl_id_i].user`
  * `ar_push_qos_o   == r_ar_tab[ar_push_id_i].qos`
  * `ar_compl_user_o == r_ar_tab[ar_compl_id_i].user`

The TB drives the AW/AR write strobes with distinct per-ID metadata,
then asserts each lookup returns the captured value. Also verifies:

  * ID re-use (second AW with same id overwrites the first).
  * AW writes don't perturb AR's table (cross-channel isolation).
"""

from __future__ import annotations

import logging
import os
import random
from dataclasses import dataclass
from typing import Optional

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer

from TBClasses.shared.tbbase import TBBase


_NBA_SETTLE_PS = 100


@dataclass
class Meta:
    user:   int = 0
    cache:  int = 0
    prot:   int = 0
    qos:    int = 0
    region: int = 0
    size:   int = 0
    burst:  int = 0


class AxiIdSideTableTB(TBBase):
    CLK = 10  # ns

    def __init__(self, dut) -> None:
        super().__init__(dut)
        self.dut = dut
        self.log = logging.getLogger("axi_id_side_table_tb")
        self.log.setLevel(logging.INFO)
        self.AXI_ID_WIDTH   = self.convert_to_int(
            os.environ.get("AXI_ID_WIDTH",   "4"))
        self.AXI_USER_WIDTH = self.convert_to_int(
            os.environ.get("AXI_USER_WIDTH", "8"))
        self.MASK_ID   = (1 << self.AXI_ID_WIDTH)   - 1
        self.MASK_USER = (1 << self.AXI_USER_WIDTH) - 1
        self.SEED      = self.convert_to_int(os.environ.get("SEED", "1"))

    async def setup_clocks_and_reset(self):
        cocotb.start_soon(Clock(self.dut.aclk, self.CLK, units="ns").start())
        self._drive_idle()
        self.dut.aresetn.value = 0
        await Timer(80, units="ns")
        self.dut.aresetn.value = 1
        await self.wait_clocks("aclk", 4)

    def _drive_idle(self) -> None:
        self.dut.aw_we_i.value     = 0
        self.dut.aw_id_i.value     = 0
        self.dut.aw_user_i.value   = 0
        self.dut.aw_cache_i.value  = 0
        self.dut.aw_prot_i.value   = 0
        self.dut.aw_qos_i.value    = 0
        self.dut.aw_region_i.value = 0
        self.dut.aw_size_i.value   = 0
        self.dut.aw_burst_i.value  = 0
        self.dut.ar_we_i.value     = 0
        self.dut.ar_id_i.value     = 0
        self.dut.ar_user_i.value   = 0
        self.dut.ar_cache_i.value  = 0
        self.dut.ar_prot_i.value   = 0
        self.dut.ar_qos_i.value    = 0
        self.dut.ar_region_i.value = 0
        self.dut.ar_size_i.value   = 0
        self.dut.ar_burst_i.value  = 0
        self.dut.aw_push_id_i.value  = 0
        self.dut.aw_compl_id_i.value = 0
        self.dut.ar_push_id_i.value  = 0
        self.dut.ar_compl_id_i.value = 0

    # ---- write ----

    async def write_aw(self, axid: int, m: Meta) -> None:
        self.dut.aw_we_i.value     = 1
        self.dut.aw_id_i.value     = axid & self.MASK_ID
        self.dut.aw_user_i.value   = m.user & self.MASK_USER
        self.dut.aw_cache_i.value  = m.cache & 0xF
        self.dut.aw_prot_i.value   = m.prot & 0x7
        self.dut.aw_qos_i.value    = m.qos & 0xF
        self.dut.aw_region_i.value = m.region & 0xF
        self.dut.aw_size_i.value   = m.size & 0x7
        self.dut.aw_burst_i.value  = m.burst & 0x3
        await RisingEdge(self.dut.aclk)
        self.dut.aw_we_i.value = 0
        await Timer(_NBA_SETTLE_PS, units="ps")

    async def write_ar(self, axid: int, m: Meta) -> None:
        self.dut.ar_we_i.value     = 1
        self.dut.ar_id_i.value     = axid & self.MASK_ID
        self.dut.ar_user_i.value   = m.user & self.MASK_USER
        self.dut.ar_cache_i.value  = m.cache & 0xF
        self.dut.ar_prot_i.value   = m.prot & 0x7
        self.dut.ar_qos_i.value    = m.qos & 0xF
        self.dut.ar_region_i.value = m.region & 0xF
        self.dut.ar_size_i.value   = m.size & 0x7
        self.dut.ar_burst_i.value  = m.burst & 0x3
        await RisingEdge(self.dut.aclk)
        self.dut.ar_we_i.value = 0
        await Timer(_NBA_SETTLE_PS, units="ps")

    # ---- read (combinational) ----

    async def lookup_aw_push_qos(self, axid: int) -> int:
        self.dut.aw_push_id_i.value = axid & self.MASK_ID
        await Timer(_NBA_SETTLE_PS, units="ps")
        return int(self.dut.aw_push_qos_o.value)

    async def lookup_aw_compl_user(self, axid: int) -> int:
        self.dut.aw_compl_id_i.value = axid & self.MASK_ID
        await Timer(_NBA_SETTLE_PS, units="ps")
        return int(self.dut.aw_compl_user_o.value)

    async def lookup_ar_push_qos(self, axid: int) -> int:
        self.dut.ar_push_id_i.value = axid & self.MASK_ID
        await Timer(_NBA_SETTLE_PS, units="ps")
        return int(self.dut.ar_push_qos_o.value)

    async def lookup_ar_compl_user(self, axid: int) -> int:
        self.dut.ar_compl_id_i.value = axid & self.MASK_ID
        await Timer(_NBA_SETTLE_PS, units="ps")
        return int(self.dut.ar_compl_user_o.value)

    async def settle(self) -> None:
        await RisingEdge(self.dut.aclk)
        await Timer(_NBA_SETTLE_PS, units="ps")
