# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: mc_ocelus_tb
# Purpose: Shared bench for the memory controllers' Ocelus plane
#          (mc_ocelus_plane, HAS_MON = 1) at a geared top: granite_top_geared
#          and pumice_top_geared expose the same pins, so one bench drives both.
#
# Author: sean galloway
# Created: 2026-11-01
"""
The flow, per cell:

  on   program the MON_* CSRs by name (both windows, Debug routed to the
       error window beside Error / Timeout, every internal event on, port
       completions on), run N write+read round trips through the AXI BFM,
       let the writers flush, then check:
         - every m_axil_mon write landed in one of the two windows;
         - the trace window holds exactly N read and N write completion
           packets (PROTOCOL_AXI, the configured unit / agents);
         - no Error or Timeout packet anywhere (the traffic is clean);
         - the error window holds whole records, each a PROTOCOL_CORE Debug
           packet from mc_monlite, a direction flip among them;
         - mon_irq pulses == records parsed == MON_ERR_STATUS.REC_COUNT;
         - MON_RD_STATS / MON_WR_STATS completions == N, errors == 0,
           MON_CORE_STATS errors == 0.
  off  the plane built, every source left at its reset (off): the same
       traffic writes nothing on m_axil_mon and every count reads 0.

Writes go to the shared MonbusGroupHarness (AXI-Lite slave, randomized
wready) and decode through the shared parser; registers resolve by name from
the product's generated regmap.
"""

import importlib.util
import random
from collections import deque
from typing import Dict, List

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles, with_timeout

from TBClasses.scoreboards.monbus_group import MonbusGroupHarness, BeatLayout, BeatOrder
from TBClasses.monbus.monbus_types import PktType, ProtocolType

from tbclasses.pumice_axi_bfm import PumiceAxiBfm

ERR_BASE, ERR_LIMIT = 0x0000_1000, 0x0000_1FFF
TRACE_BASE, TRACE_LIMIT = 0x0000_4000, 0x0000_7FFF
UNIT_ID, AGENT_RD, AGENT_WR, AGENT_CORE = 0x20, 0x0010, 0x0011, 0x0012
EV_DIR_FLIP = 0x0A
CTRL_SOFT_RESET = 1 << 31
STATUS_INIT_DONE = 1 << 0


class McOcelusTB:
    """Bench for mc_ocelus_plane at granite_top_geared / pumice_top_geared."""

    def __init__(self, dut, *, regmap_path: str, aclk_ns: float = 10.0,
                 dfi_ns: float = 10.0, dw: int = 64, dfi_rate: int = 2,
                 bl_words: int = 8, burst_words: int = 1):
        # The clock / geometry arguments serve run() (the self-contained flow
        # with the loose DFI model). A bench that owns setup and traffic itself
        # (pumice's PumiceTopCsrTB) uses only start_harness(),
        # program_monitors() and finish().
        self.dut = dut
        self.log = dut._log
        self.aclk_ns, self.dfi_ns = aclk_ns, dfi_ns
        self.dw, self.dfi_rate = dw, dfi_rate
        self.bl_words, self.burst_words = bl_words, burst_words
        spec = importlib.util.spec_from_file_location("ocelus_regmap", regmap_path)
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        self.regs: Dict = mod.top_block
        self.captured: List[int] = []
        self.mon = None

    # ------------------------------------------------------------------
    # clocks and reset
    # ------------------------------------------------------------------
    async def setup_clocks_and_reset(self):
        d = self.dut
        cocotb.start_soon(Clock(d.aclk, self.aclk_ns, unit="ns").start())
        cocotb.start_soon(Clock(d.dfi_clk, self.dfi_ns, unit="ns").start())
        for s in ("s_cpuif_req", "s_cpuif_req_is_wr", "s_cpuif_addr", "s_cpuif_wr_data",
                  "s_cpuif_wr_biten", "dfi_rddata_i", "dfi_rddata_valid_i",
                  "dfi_init_complete_i", "m_axil_mon_awready", "m_axil_mon_wready",
                  "m_axil_mon_bvalid", "m_axil_mon_bresp"):
            getattr(d, s).value = 0
        await self.assert_reset()
        await ClockCycles(d.aclk, 10)
        await self.deassert_reset()
        await ClockCycles(d.aclk, 6)

    async def assert_reset(self):
        self.dut.aresetn.value = 0
        self.dut.dfi_rstn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1
        self.dut.dfi_rstn.value = 1

    # ------------------------------------------------------------------
    # CSRs by name (PeakRDL passthrough cpuif)
    # ------------------------------------------------------------------
    def addr(self, reg: str) -> int:
        return int(self.regs[reg]["address"], 16)

    def _span(self, reg: str, field: str):
        off = self.regs[reg][field]["offset"]
        hi, lo = (off.split(":") + [off])[:2]
        return int(hi), int(lo)

    def pack(self, reg: str, **fields) -> int:
        val = int(self.regs[reg]["default"], 16)
        for name, v in fields.items():
            hi, lo = self._span(reg, name)
            mask = ((1 << (hi - lo + 1)) - 1) << lo
            val = (val & ~mask) | ((v << lo) & mask)
        return val

    def field(self, reg: str, name: str, regval: int) -> int:
        hi, lo = self._span(reg, name)
        return (regval >> lo) & ((1 << (hi - lo + 1)) - 1)

    async def _cpuif(self, addr: int, data: int = 0, wr: bool = False) -> int:
        d = self.dut
        d.s_cpuif_addr.value = addr
        d.s_cpuif_wr_data.value = data
        d.s_cpuif_wr_biten.value = 0xFFFFFFFF
        d.s_cpuif_req_is_wr.value = int(wr)
        d.s_cpuif_req.value = 1
        val = 0
        for _ in range(100):
            await RisingEdge(d.aclk)
            if wr and (int(d.s_cpuif_wr_ack.value) or int(d.s_cpuif_wr_err.value)):
                break
            if not wr and (int(d.s_cpuif_rd_ack.value) or int(d.s_cpuif_rd_err.value)):
                val = int(d.s_cpuif_rd_data.value)
                break
        else:
            raise AssertionError(f"CSR {'write' if wr else 'read'} {addr:#x} never acked")
        d.s_cpuif_req.value = 0
        d.s_cpuif_req_is_wr.value = 0
        await RisingEdge(d.aclk)
        return val

    async def write(self, reg: str, **fields):
        await self._cpuif(self.addr(reg), self.pack(reg, **fields), wr=True)

    async def read(self, reg: str) -> int:
        return await self._cpuif(self.addr(reg))

    # ------------------------------------------------------------------
    # DFI model: finish init, capture writes, replay them on reads
    # (the granite / pumice top tests' loose model)
    # ------------------------------------------------------------------
    async def dfi_model(self):
        d = self.dut
        chunks, in_window, rd_q = 0, False, deque()
        state, gap_left, beat_left = "idle", 0, 0
        while True:
            await RisingEdge(d.dfi_clk)
            if int(d.dfi_init_start_o.value):
                d.dfi_init_complete_i.value = 1
            if int(d.dfi_wrdata_en_o.value) != 0:
                self.captured.append(int(d.dfi_wrdata_o.value))
            if int(d.dfi_rddata_en_o.value) != 0:
                if not in_window:
                    chunks += 1
                    in_window = True
            else:
                in_window = False
            if state == "idle":
                if chunks > 0 and not rd_q and self.captured:
                    rd_q = deque(self.captured)
                if chunks > 0 and rd_q:
                    chunks -= 1
                    state, gap_left = "gap", 2
                d.dfi_rddata_valid_i.value = 0
            elif state == "gap":
                gap_left -= 1
                if gap_left == 0:
                    state, beat_left = "data", min(self.burst_words, len(rd_q))
                d.dfi_rddata_valid_i.value = 0
            else:
                d.dfi_rddata_i.value = rd_q.popleft()
                d.dfi_rddata_valid_i.value = (1 << self.dfi_rate) - 1
                beat_left -= 1
                if beat_left == 0:
                    state = "idle"

    # ------------------------------------------------------------------
    # the run
    # ------------------------------------------------------------------
    async def init_controller(self):
        await self._cpuif(self.addr("CTRL"), CTRL_SOFT_RESET, wr=True)
        for _ in range(2000):
            await RisingEdge(self.dut.aclk)
            if await self.read("STATUS") & STATUS_INIT_DONE:
                return
        raise AssertionError("init never completed")

    async def program_monitors(self):
        await self.write("MON_BASE_ADDR", VAL=TRACE_BASE)
        await self.write("MON_LIMIT_ADDR", VAL=TRACE_LIMIT)
        await self.write("MON_ERR_BASE_ADDR", VAL=ERR_BASE)
        await self.write("MON_ERR_LIMIT_ADDR", VAL=ERR_LIMIT)
        err_sel = ((1 << PktType.PktTypeError) | (1 << PktType.PktTypeTimeout)
                   | (1 << PktType.PktTypeDebug))
        await self.write("MON_ROUTE", PKT_MASK=0, ERR_SELECT=err_sel)
        await self.write("MON_CORE_EV", EV_EN=0xFFFF)
        await self.write("MON_CTRL", RD_EN=1, WR_EN=1, CORE_EN=1, ERROR_EN=1,
                         COMPL_EN=1, TIMEOUT_EN=1)

    async def traffic(self, rounds: int, seed: int):
        bfm = PumiceAxiBfm(self.dut, data_width=self.dw, bl_words=self.bl_words)
        rng = random.Random(seed)
        for rnd in range(rounds):
            data = [rng.randrange(1 << self.dw) for _ in range(self.bl_words)]
            addr = 0x2000 + rnd * 0x1000
            self.captured.clear()
            await with_timeout(bfm.write(addr, data, wid=1), 200, "us")

            async def _wait_wr():
                while len(self.captured) < self.bl_words:
                    await RisingEdge(self.dut.dfi_clk)
            try:
                await with_timeout(_wait_wr(), 200, "us")
            except cocotb.triggers.SimTimeoutError:
                raise AssertionError(
                    f"round {rnd}: {len(self.captured)} of {self.bl_words} write "
                    f"words reached the DFI") from None
            rd = await with_timeout(bfm.read(addr, rid=1), 200, "us")
            assert rd[:self.bl_words] == data, f"round {rnd}: read-back mismatch"

    def start_harness(self):
        self.mon = MonbusGroupHarness(
            self.dut, self.dut.aclk,
            drain_proto=None, drain_prefix="unused_",
            trace_proto="axil", trace_prefix="m_axil_mon_",
            group_node=self.dut, irq_sig=self.dut.mon_irq_o, log=self.log,
            layout_trace=BeatLayout(order=BeatOrder.TS_HI_LO),
            err_window=(ERR_BASE, ERR_LIMIT))
        self.mon.start_trace_consumer(ready_prob=0.7)
        self.mon.start_irq_watch()

    async def run(self, *, cell: str, rounds: int, seed: int):
        """The self-contained flow: reset, loose DFI model, host-style init."""
        await self.setup_clocks_and_reset()
        self.start_harness()
        cocotb.start_soon(self.dfi_model())
        await self.init_controller()
        if cell == "on":
            await self.program_monitors()
        await self.traffic(rounds, seed)
        await self.finish(cell=cell, rounds=rounds)

    async def finish(self, *, cell: str, rounds: int):
        """Let the writers flush, stop capture, check the cell. rounds = the
        AXI write bursts issued, which is also the read bursts issued."""
        # the trace writer's flush timeout is 1024 cycles
        await ClockCycles(self.dut.aclk, 3000)
        self.mon.stop_trace_consumer()
        self.mon.stop_irq_watch()
        await ClockCycles(self.dut.aclk, 4)
        if cell == "on":
            await self.check_on(rounds)
        else:
            await self.check_off(rounds)

    async def _stats(self) -> Dict[str, int]:
        return {r: await self.read(r) for r in
                ("MON_ERR_STATUS", "MON_RD_STATS", "MON_WR_STATS", "MON_CORE_STATS")}

    async def check_off(self, rounds: int):
        st = await self._stats()
        assert not self.mon.trace_beats, \
            f"{len(self.mon.trace_beats)} writes with every source off"
        assert self.mon.stats.irq_rising_edges == 0
        for name, v in st.items():
            assert v == 0, f"{name} = {v:#x} with every source off"
        self.log.info("PASS off: %d round trips, nothing written", rounds)

    async def check_on(self, rounds: int):
        trace = self.mon.parse_trace_records()
        errs = self.mon.parse_err_records()
        st = await self._stats()
        for a, _ in self.mon.trace_beats:
            assert (ERR_BASE <= a <= ERR_LIMIT) or (TRACE_BASE <= a <= TRACE_LIMIT), \
                f"write outside both windows: {a:#x}"

        def is_compl(p, agent):
            return (p.packet_type == PktType.PktTypeCompletion
                    and p.protocol == ProtocolType.PROTOCOL_AXI
                    and p.unit_id == UNIT_ID and p.agent_id == agent)

        n_rd = sum(1 for p in trace if is_compl(p, AGENT_RD))
        n_wr = sum(1 for p in trace if is_compl(p, AGENT_WR))
        assert n_rd == rounds and n_wr == rounds, \
            f"completions rd={n_rd} wr={n_wr}, expected {rounds} each"
        bad = [p for p in trace + errs
               if p.packet_type in (PktType.PktTypeError, PktType.PktTypeTimeout)]
        assert not bad, f"error/timeout packets on clean traffic: {bad[:4]}"
        assert errs, "no records in the error window (Debug is routed there)"
        for p in errs:
            assert (p.protocol == ProtocolType.PROTOCOL_CORE and p.unit_id == UNIT_ID
                    and p.agent_id == AGENT_CORE
                    and p.packet_type == PktType.PktTypeDebug), \
                f"unexpected error-window record {p}"
        assert any(p.event_code == EV_DIR_FLIP for p in errs), \
            f"no direction flip among {[hex(p.event_code) for p in errs]}"
        n_rec = self.field("MON_ERR_STATUS", "REC_COUNT", st["MON_ERR_STATUS"])
        assert self.mon.stats.irq_rising_edges == len(errs) == n_rec, \
            f"irq {self.mon.stats.irq_rising_edges} records {len(errs)} REC_COUNT {n_rec}"
        assert self.field("MON_RD_STATS", "COMPLETIONS", st["MON_RD_STATS"]) == rounds
        assert self.field("MON_WR_STATS", "COMPLETIONS", st["MON_WR_STATS"]) == rounds
        assert self.field("MON_RD_STATS", "ERRORS", st["MON_RD_STATS"]) == 0
        assert self.field("MON_WR_STATS", "ERRORS", st["MON_WR_STATS"]) == 0
        assert self.field("MON_CORE_STATS", "ERRORS", st["MON_CORE_STATS"]) == 0
        self.log.info("PASS on: %d round trips; %d trace records (%d+%d completions), "
                      "%d error-window records %s, dropped=%d",
                      rounds, len(trace), n_rd, n_wr, len(errs),
                      sorted({hex(p.event_code) for p in errs}),
                      self.field("MON_ERR_STATUS", "DROPPED", st["MON_ERR_STATUS"]))
