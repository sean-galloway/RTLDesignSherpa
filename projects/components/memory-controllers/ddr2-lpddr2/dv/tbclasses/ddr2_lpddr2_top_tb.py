# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Test-bench harness for ddr2_lpddr2_top.

Three live BFMs glued to one DUT:

  * APBMaster + RegisterMap                          → CSR programming
  * AXI4MasterWrite + AXI4MasterRead + AXI4Sequence  → host traffic
  * DFISlavePHY + MemoryModel + AddressMapping       → DFI loopback +
                                                       preloadable DRAM

The DFI side is the framework's full DFISlavePHY BFM, bound through
the dv/tb/ddr2_lpddr2_top_tb_top.sv alias module (`phy_dfi_*` ports
shadow the DUT's `dfi_*` ports so the BFM auto-binds without per-DUT
plumbing). The BFM uses MemoryModel for storage — preload via
`tb.preload_memory(byte_addr, data)` and inspect via
`tb.peek_memory(byte_addr, length)`.
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
from CocoTBFramework.components.dfi.dfi_base import DFIBase
from CocoTBFramework.components.dfi.dfi_signals import DFIVersion, MemoryType
from CocoTBFramework.components.dfi.dfi_slave_phy import DFISlavePHY
from CocoTBFramework.components.dfi.dram_state import (
    AddressMapping, DramStateModel, ViolationPolicy,
)
from CocoTBFramework.components.dfi.jedec_timings import builtin_timings
from CocoTBFramework.components.shared.memory_model import MemoryModel

from TBClasses.apb.register_map import RegisterMap


class DDR2LPDDR2TopTB:
    """End-to-end TB for ddr2_lpddr2_top."""

    REGMAP_FILE = os.path.join(
        os.path.dirname(__file__), "ddr2_lpddr2_regmap.py"
    )

    def __init__(self, dut, *, mc_period_ns: int = 7, pclk_period_ns: int = 10,
                 axi_data_width: int = 64, axi_id_width: int = 4,
                 axi_addr_width: int = 32,
                 num_ranks: int = 1, num_banks: int = 8,
                 row_width: int = 14, col_width: int = 10) -> None:
        self.dut = dut
        self.log = logging.getLogger("ddr2_lpddr2_top_tb")
        self.log.setLevel(logging.INFO)
        self.mc_period_ns = mc_period_ns
        self.pclk_period_ns = pclk_period_ns
        self.axi_data_width = axi_data_width
        self.axi_id_width = axi_id_width
        self.axi_addr_width = axi_addr_width

        # DRAM geometry
        self.num_ranks = num_ranks
        self.num_banks = num_banks
        self.row_width = row_width
        self.col_width = col_width
        self.bytes_per_beat = axi_data_width // 8

        # Address mapping mirrors the RTL's default ROW_MAJOR scheme:
        #   byte_addr = {row, bank, col, byte_off}
        # AddressMapping decodes flat-column-index → (rank, bank, row, col).
        # For preload byte_addr we use the same packing the RTL applies.
        # ROW_MAJOR with rank in the top bits when NUM_RANKS>1 — matches
        # the RTL addr_mapper default for the rank parameter.
        mapping_str = ("rank|row|bank|col" if num_ranks > 1
                       else "row|bank|col")
        self.mapping = AddressMapping(
            num_ranks=num_ranks,
            num_banks=num_banks,
            num_rows=1 << row_width,
            num_cols=1 << col_width,
            mapping=mapping_str,
        )

        # Backing memory model — preloadable + inspectable. One line == one
        # DFI beat = bytes_per_beat bytes.
        num_lines = num_ranks * num_banks * (1 << row_width) * (1 << col_width)
        self.memory = MemoryModel(
            num_lines=num_lines,
            bytes_per_line=self.bytes_per_beat,
            log=self.log,
        )

        # Single source of truth for DRAM burst length. The controller's
        # MR0 default is BL=4 for DDR2 (see init_sequencer's
        # DDR2_MR0_DEFAULT). We drive the SAME value into:
        #   * wr_beat_sequencer.bl_i — so the controller pads short AXI
        #     bursts to BL DRAM beats with masked padding
        #   * DFISlavePHY.beats_per_burst — so the slave queues the same
        #     number of pending writes per WR command
        # Both knobs MUST match; if they diverge the slave drops or
        # over-queues beats and writes get corrupted.
        self.dram_bl = 4
        self.dfi_base = DFIBase(
            dfi_version=DFIVersion.V2_1,
            memory_type=MemoryType.DDR2,
            timings=builtin_timings("ddr2-650-mt47h64m16hr"),
            mapping=self.mapping,
            beats_per_burst=self.dram_bl,
        )

        self.apb_master: Optional[APBMaster] = None
        self.axi_master_wr: Optional[AXI4MasterWrite] = None
        self.axi_master_rd: Optional[AXI4MasterRead] = None
        self.reg_map: Optional[RegisterMap] = None
        self.dfi_slave: Optional[DFISlavePHY] = None

    # ---- bring-up ---------------------------------------------------------

    async def reset(self, *, mem_type: str = "DDR2",
                    init_complete_delay: int = 20) -> None:
        """Apply mc_clk + pclk reset; tie off externals; release.

        Args:
            mem_type: ``"DDR2"`` (default) or ``"LPDDR2"`` — drives
                `memtype_i`. LPDDR2 selects a different MR walk in
                `init_sequencer` and the LPDDR2 CA-bus encoding in
                `dfi_cmd_formatter`.
            init_complete_delay: cycles to wait before asserting
                `phy_dfi_init_complete`. Long values can be used to
                exercise the init_sequencer's wait branches.
        """
        self.dut.memtype_i.value      = 1 if mem_type.upper() == "LPDDR2" else 0
        self.dut.t_phy_wrlat_i.value  = 4
        self.dut.t_rddata_en_i.value  = 4
        self.dut.rd_in_order_i.value  = 1
        self.dut.cap_lookahead_max_i.value = 0
        self.dut.cap_synth_mask_i.value    = 0b111

        # DFI PHY-side inputs that the BFM does NOT drive (init_complete,
        # ctrlupd_ack, phyupd_req/type). The BFM owns rddata + rddata_valid.
        self.dut.phy_dfi_init_complete.value = 0
        self.dut.phy_dfi_ctrlupd_ack.value   = 0
        self.dut.phy_dfi_phyupd_req.value    = 0
        self.dut.phy_dfi_phyupd_type.value   = 0

        # APB master signals (BFM will re-drive)
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

        # Assert dfi_init_complete a few cycles after reset (the DUT's
        # init_sequencer waits for this before promoting init_done).
        async def _init_complete_after(n: int) -> None:
            await ClockCycles(self.dut.mc_clk, n)
            self.dut.phy_dfi_init_complete.value = 1
        cocotb.start_soon(_init_complete_after(init_complete_delay))

    def init_dfi_slave(self, *,
                       strict_violations: bool = False) -> DFISlavePHY:
        """Instantiate the DFISlavePHY BFM bound to phy_dfi_* signals.

        Call AFTER reset() so the bus is live when the BFM samples it.
        The BFM owns dfi_rddata / dfi_rddata_valid and writes wrdata
        into self.memory keyed by (rank, bank, row, col) → flat index.

        `strict_violations=False` (default) demotes the BFM's HARD
        violations to SOFT so the test only fails on data mismatches.
        Flip it on to enforce full JEDEC timing checking — the
        controller's tRCD / tFAW / etc. must then match the
        ddr2-650 preset exactly.
        """
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

    # ---- Memory preload + peek -------------------------------------------

    def preload_memory(self, byte_addr: int, data: bytes | bytearray) -> None:
        """Write bytes directly into the DRAM model.

        After preload, an AXI read of `byte_addr` returns those bytes
        (assuming the controller is initialized and addr-mapped to the
        same flat index the model uses).
        """
        if not isinstance(data, (bytes, bytearray)):
            raise TypeError(f"data must be bytes/bytearray, got {type(data)}")
        self.memory.write(byte_addr, bytearray(data))

    def peek_memory(self, byte_addr: int, length: int) -> bytearray:
        """Read bytes directly from the DRAM model — verification hook."""
        return self.memory.read(byte_addr, length)

    # ---- High-level APIs --------------------------------------------------

    async def apb_program_register(self, register: str, field: str,
                                   value: int) -> None:
        """Use the RegisterMap to encode one field-write, send via APB.

        RegisterMap's `write()` expects `value` already shifted to its
        absolute bit position; we hide that here so callers pass the
        natural field value (`page_policy_or=2`, not `2 << 2`).
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
