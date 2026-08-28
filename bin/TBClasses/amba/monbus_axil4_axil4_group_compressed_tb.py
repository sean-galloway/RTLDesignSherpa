# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: MonbusAxilAxilGroupTB
# Purpose: Testbench for monbus_axil4_axil4_group_compressed
# Subsystem: framework
#
# Extracted from val/amba/test_monbus_axil4_axil4_group_compressed.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
from typing import List, Tuple
from cocotb.triggers import RisingEdge, ReadOnly, Combine
from TBClasses.shared.tbbase import TBBase
from TBClasses.scoreboards.monbus_group import MonbusGroupHarness


class MonbusAxilAxilGroupTB(TBBase):
    """Drive records into the monbus input, capture every AXIL write
    on the master interface, and compare against the Python golden."""

    SLOT_STRIDE = 8

    def __init__(self, dut):
        super().__init__(dut)
        self.SEED = int(os.environ.get('SEED', '0'))
        random.seed(self.SEED)
        # Shared harness drives the m_axil_* master-write sink and captures
        # every (addr, data) beat into harness.trace_beats (replaces the
        # hand-rolled _aw/_w/_b AXIL slave model).
        self.mon = MonbusGroupHarness(
            dut, dut.axi_aclk,
            drain_proto="axil", trace_proto="axil",
            drain_prefix="s_axil_", trace_prefix="m_axil_",
            group_node=dut, irq_sig=dut.irq_out, log=self.log,
        )

    @property
    def captured(self) -> List[Tuple[int, int]]:
        """(addr, data) compressed slots captured on m_axil_*, in order."""
        return self.mon.trace_beats

    # ---------- setup / reset ----------

    def _tie_off_config(self):
        """Disable all dropping and all err-FIFO routing so every monbus
        packet lands in the write FIFO, feeding the compressor."""
        # Drop masks = 0, err_select = 0, event masks = 0.
        for sig in (
            'cfg_axi_pkt_mask', 'cfg_axi_err_select', 'cfg_axi_error_mask',
            'cfg_axi_timeout_mask', 'cfg_axi_compl_mask', 'cfg_axi_thresh_mask',
            'cfg_axi_perf_mask', 'cfg_axi_addr_mask', 'cfg_axi_debug_mask',
            'cfg_axis_pkt_mask', 'cfg_axis_err_select', 'cfg_axis_error_mask',
            'cfg_axis_timeout_mask', 'cfg_axis_compl_mask', 'cfg_axis_credit_mask',
            'cfg_axis_channel_mask', 'cfg_axis_stream_mask',
            'cfg_core_pkt_mask', 'cfg_core_err_select', 'cfg_core_error_mask',
            'cfg_core_timeout_mask', 'cfg_core_compl_mask', 'cfg_core_thresh_mask',
            'cfg_core_perf_mask', 'cfg_core_debug_mask',
        ):
            getattr(self.dut, sig).value = 0

    async def reset_dut(self, base_addr: int, limit_addr: int):
        self.dut.monbus_valid.value     = 0
        self.dut.monbus_packet.value    = 0
        self.dut.monbus_timestamp.value = 0
        # s_axil slave read interface unused -- we never drain the err FIFO,
        # but with err_select=0 the err FIFO never fills anyway.
        self.dut.s_axil_arvalid.value = 0
        self.dut.s_axil_araddr.value  = 0
        self.dut.s_axil_arprot.value  = 0
        self.dut.s_axil_rready.value  = 0
        # AXIL master write slave model (we behave as the memory side).
        self.dut.m_axil_awready.value = 0
        self.dut.m_axil_wready.value  = 0
        self.dut.m_axil_bvalid.value  = 0
        self.dut.m_axil_bresp.value   = 0
        # Window.
        self.dut.cfg_base_addr.value  = base_addr
        self.dut.cfg_limit_addr.value = limit_addr
        # Eagerly flush every slot so this slot-by-slot golden compare
        # works the same way it did against the pre-family monolithic
        # writer. With a beat-granular FIFO, watermark=1 means a single
        # compressed-mode slot in the FIFO triggers a flush immediately.
        self.dut.cfg_flush_watermark.value = 1
        # Compression is now runtime-selected; this group is built with the
        # compressor hardware present (USE_COMPRESSION=1), so enable it.
        self.dut.cfg_compress_en.value = 1
        self._tie_off_config()
        # Reset pulse.
        self.dut.axi_aresetn.value = 0
        await self.wait_clocks('axi_aclk', 5)
        self.dut.axi_aresetn.value = 1
        await self.wait_clocks('axi_aclk', 2)
        self.mon.clear()

    # ---------- monbus driver (input side) ----------

    async def drive_record(self, packet: int, source_ts: int):
        """Same pre-edge ReadOnly handshake pattern as the compressor
        test, so a single record cannot be double-handshook."""
        self.dut.monbus_packet.value    = packet
        self.dut.monbus_timestamp.value = source_ts
        self.dut.monbus_valid.value     = 1
        while True:
            await ReadOnly()
            if int(self.dut.monbus_ready.value) == 1:
                break
            await RisingEdge(self.dut.axi_aclk)
        await RisingEdge(self.dut.axi_aclk)
        self.dut.monbus_valid.value = 0

    # ---------- AXIL slave model (output side, via MonbusGroupHarness) ----------

    async def run_records_through(self,
                                  records: List[Tuple[int, int]],
                                  expected_slots: List[int],
                                  drain_cycles: int = 6000):
        n_slots = len(expected_slots)
        # Harness master-write consumer drives awready/wready/bvalid and
        # captures every (addr,data) slot into harness.trace_beats.
        self.mon.start_trace_consumer()

        for pkt, ts in records:
            await self.drive_record(pkt, ts)

        # Drain: wait until all expected slots land (or a wall-clock bound).
        waited = 0
        while len(self.mon.trace_beats) < n_slots and waited < drain_cycles:
            await self.wait_clocks('axi_aclk', 10)
            waited += 10
        await self.wait_clocks('axi_aclk', 4)
        self.mon.stop_trace_consumer()

        assert len(self.captured) == n_slots, (
            f"captured slot count mismatch: got={len(self.captured)}, "
            f"expected={n_slots}"
        )

        rtl_slots = [d for (_, d) in self.captured]
        for i, (rtl, golden) in enumerate(zip(rtl_slots, expected_slots)):
            assert rtl == golden, (
                f"slot {i} mismatch: rtl=0x{rtl:016x}, golden=0x{golden:016x}"
            )

    # ---------- wrap-window assertion ----------

    def assert_wrap_addresses(self, base_addr: int, limit_addr: int):
        """Walk the captured (addr, data) pairs and confirm every addr
        is inside [base_addr, limit_addr - 7] and that consecutive addrs
        either step by +8 or wrap back to base_addr."""
        for i, (addr, _) in enumerate(self.captured):
            assert base_addr <= addr <= (limit_addr - (self.SLOT_STRIDE - 1)), (
                f"slot {i}: addr 0x{addr:08x} outside window "
                f"[0x{base_addr:08x}, 0x{limit_addr:08x}]"
            )
            if i == 0:
                continue
            prev_addr = self.captured[i - 1][0]
            step = addr - prev_addr
            wrapped = (prev_addr + self.SLOT_STRIDE) > limit_addr and addr == base_addr
            assert step == self.SLOT_STRIDE or wrapped, (
                f"slot {i}: bad addr step from 0x{prev_addr:08x} to 0x{addr:08x}"
            )
