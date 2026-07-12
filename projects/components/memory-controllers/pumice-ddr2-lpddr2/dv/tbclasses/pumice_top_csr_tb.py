# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Test-bench harness for the rearchitected pumice_top (pumice_core + PeakRDL CSR).

Ported from the old APB/FSM-era DDR2LPDDR2TopTB to the new interface:

  * cpuif (PeakRDL passthrough) + pumice_regmap (by-name)  -> CSR programming
  * AXI4MasterWrite + AXI4MasterRead + AXI4Sequence         -> host traffic (aclk)
  * DFISlavePHY + MemoryModel + AddressMapping              -> strict DFI + golden DRAM (dfi_clk)

Interface deltas vs the old top:
  * clocks/resets:  mc_clk/pclk/mc_rst_n/presetn -> aclk/dfi_clk/aresetn/dfi_rstn
  * CSR:            APB slave -> cpuif passthrough (config written BY NAME through
                    pumice_regmap, never hardcoded offsets)
  * config:         extern ports (memtype_i/t_phy_wrlat_i/rd_in_order_i/cap_*) are
                    GONE -> all config is CSR fields, programmed before init
  * geometry:       AXI data width = DRAM_BEAT_WIDTH * DFI_RATE (128 by default);
                    one AXI burst = BL/DFI_RATE beats = one DRAM burst (BL beats)

Correctness bar is the strict DFISlavePHY + golden MemoryModel (write data is
captured cycle-exactly and reads are checked against the model), which is a
stronger end-to-end check than the old FSM-internal divergence trackers (those
hooked u_command_scheduler / u_data_path hierarchy that no longer exists).
"""

from __future__ import annotations

import logging
import os
from typing import Optional, Sequence

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, RisingEdge, Timer

from CocoTBFramework.components.axi4.axi4_interfaces import (
    AXI4MasterRead, AXI4MasterWrite,
)
from CocoTBFramework.components.axi4.axi4_sequence import (
    AXI4Sequence, run_axi4_sequence,
)
from CocoTBFramework.components.dfi.dfi_base import DFIBase
from CocoTBFramework.components.dfi.dfi_monitor import DFIMonitor
from CocoTBFramework.components.dfi.dfi_packet import DRAMCommand
from CocoTBFramework.components.dfi.dfi_signals import DFIVersion, MemoryType
from CocoTBFramework.components.dfi.dfi_slave_phy import DFISlavePHY
from CocoTBFramework.components.dfi.dram_state import (
    AddressMapping, DramStateModel, ViolationPolicy,
)
from CocoTBFramework.components.dfi.jedec_timings import builtin_timings
from CocoTBFramework.components.shared.memory_model import MemoryModel


class PumiceTopCsrTB:
    """End-to-end TB for the rearchitected pumice_top (cpuif + DFI)."""

    # by-name register map (generated from pumice_csr.rdl)
    _REGMAP = None

    def __init__(self, dut, *, aclk_period_ns: int = 10, dfi_period_ns: int = 4,
                 dram_beat_width: int = 64, dfi_rate: int = 2, dram_bl: int = 8,
                 axi_id_width: int = 8, axi_addr_width: int = 32,
                 num_ranks: int = 1, num_banks: int = 8,
                 row_width: int = 14, col_width: int = 10,
                 mem_type: str = "DDR2") -> None:
        self.dut = dut
        self.log = logging.getLogger("pumice_top_csr_tb")
        self.log.setLevel(logging.INFO)
        self.aclk_period_ns = aclk_period_ns
        self.dfi_period_ns = dfi_period_ns

        # geometry: AXI data width == one DFI word == DRAM_BEAT_WIDTH * DFI_RATE
        self.dfi_rate = dfi_rate
        self.dram_beat_width = dram_beat_width
        self.dram_beat_bytes = dram_beat_width // 8
        self.axi_data_width = dram_beat_width * dfi_rate
        self.bytes_per_beat = self.axi_data_width // 8
        self.axi_id_width = axi_id_width
        self.axi_addr_width = axi_addr_width

        # DRAM geometry
        self.num_ranks = num_ranks
        self.num_banks = num_banks
        self.row_width = row_width
        self.col_width = col_width

        # DRAM burst length (DRAM beats per command). Each AXI burst is exactly
        # one DRAM burst => BL/DFI_RATE AXI beats.
        self.dram_bl = dram_bl
        self.beats_per_burst = dram_bl // dfi_rate   # AXI beats per burst

        mapping_str = ("rank|row|bank|col" if num_ranks > 1 else "row|bank|col")
        self.mapping = AddressMapping(
            num_ranks=num_ranks, num_banks=num_banks,
            num_rows=1 << row_width, num_cols=1 << col_width,
            mapping=mapping_str,
        )
        num_lines = num_ranks * num_banks * (1 << row_width) * (1 << col_width)
        self.memory = MemoryModel(
            num_lines=num_lines, bytes_per_line=self.dram_beat_bytes, log=self.log,
        )
        self.mem_type = mem_type.upper()
        _mt = MemoryType.LPDDR2 if self.mem_type == "LPDDR2" else MemoryType.DDR2
        self.dfi_base = DFIBase(
            dfi_version=DFIVersion.V2_1, memory_type=_mt,
            timings=builtin_timings("ddr2-650-mt47h64m16hr"),
            mapping=self.mapping, beats_per_burst=self.dram_bl,
        )

        self.axi_master_wr: Optional[AXI4MasterWrite] = None
        self.axi_master_rd: Optional[AXI4MasterRead] = None
        self.dfi_slave: Optional[DFISlavePHY] = None
        self.dfi_monitor: Optional[DFIMonitor] = None
        self.axi_wr_snoop: dict = {}
        self._axi_wr_snoop_task = None
        self.axi_rd_snoop: list = []
        self._axi_rd_snoop_task = None
        self._load_regmap()

    # ---- register map (by-name) ------------------------------------------

    @classmethod
    def _load_regmap(cls):
        if cls._REGMAP is None:
            import importlib.util
            path = os.path.join(os.path.dirname(__file__), "pumice_regmap.py")
            spec = importlib.util.spec_from_file_location("pumice_regmap", path)
            mod = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(mod)
            cls._REGMAP = mod.top_block
        return cls._REGMAP

    def _field_loc(self, register: str, field: str) -> tuple[int, int, int]:
        """Return (addr, lsb, mask) for REGISTER.field from the by-name map."""
        reg = self._REGMAP[register]
        addr = int(reg["address"], 16)
        off = reg[field]["offset"]
        if ":" in off:
            hi, lo = (int(x) for x in off.split(":"))
        else:
            hi = lo = int(off)
        mask = ((1 << (hi - lo + 1)) - 1) << lo
        return addr, lo, mask

    # ---- bring-up ---------------------------------------------------------

    async def reset(self, *, init_complete_delay: int = 8) -> None:
        """Start aclk + dfi_clk, idle the cpuif/AXI, reset, and arm the DFI
        init-complete responder (asserts phy_dfi_init_complete once the DUT
        raises dfi_init_start_o)."""
        cocotb.start_soon(Clock(self.dut.aclk, self.aclk_period_ns, units="ns").start())
        cocotb.start_soon(Clock(self.dut.dfi_clk, self.dfi_period_ns, units="ns").start())

        # idle cpuif
        self.dut.s_cpuif_req.value = 0
        self.dut.s_cpuif_req_is_wr.value = 0
        self.dut.s_cpuif_addr.value = 0
        self.dut.s_cpuif_wr_data.value = 0
        self.dut.s_cpuif_wr_biten.value = 0
        # idle AXI (BFMs re-drive once instantiated)
        for s in ("awvalid", "wvalid", "bready", "arvalid", "rready"):
            try:
                getattr(self.dut, f"s_axi_{s}").value = 0
            except Exception:
                pass
        self.dut.phy_dfi_init_complete.value = 0

        self.dut.aresetn.value = 0
        self.dut.dfi_rstn.value = 0
        await ClockCycles(self.dut.aclk, 10)
        self.dut.aresetn.value = 1
        self.dut.dfi_rstn.value = 1
        await ClockCycles(self.dut.aclk, 6)

        async def _init_responder(n: int) -> None:
            for _ in range(4000):
                await RisingEdge(self.dut.dfi_clk)
                if int(self.dut.phy_dfi_init_start.value):
                    await ClockCycles(self.dut.dfi_clk, n)
                    self.dut.phy_dfi_init_complete.value = 1
                    return
        cocotb.start_soon(_init_responder(init_complete_delay))

    # ---- CSR (cpuif, by-name) --------------------------------------------

    async def _cpuif_write(self, addr: int, data: int, biten: int) -> None:
        self.dut.s_cpuif_req.value = 1
        self.dut.s_cpuif_req_is_wr.value = 1
        self.dut.s_cpuif_addr.value = addr
        self.dut.s_cpuif_wr_data.value = data
        self.dut.s_cpuif_wr_biten.value = biten
        await RisingEdge(self.dut.aclk)
        for _ in range(40):
            if int(self.dut.s_cpuif_wr_ack.value):
                break
            await RisingEdge(self.dut.aclk)
        self.dut.s_cpuif_req.value = 0
        await RisingEdge(self.dut.aclk)

    async def _cpuif_read(self, addr: int) -> int:
        self.dut.s_cpuif_req.value = 1
        self.dut.s_cpuif_req_is_wr.value = 0
        self.dut.s_cpuif_addr.value = addr
        await RisingEdge(self.dut.aclk)
        val = 0
        for _ in range(40):
            if int(self.dut.s_cpuif_rd_ack.value):
                val = int(self.dut.s_cpuif_rd_data.value)
                break
            await RisingEdge(self.dut.aclk)
        self.dut.s_cpuif_req.value = 0
        await RisingEdge(self.dut.aclk)
        return val

    async def csr_write_field(self, register: str, field: str, value: int) -> None:
        """Write one CSR field BY NAME (cpuif, biten-masked so only the field
        bits change). Callers pass the natural field value."""
        addr, lsb, mask = self._field_loc(register, field)
        await self._cpuif_write(addr, (value << lsb) & mask, mask)

    async def csr_read_register(self, register: str) -> int:
        addr = int(self._REGMAP[register]["address"], 16)
        return await self._cpuif_read(addr)

    async def csr_read_field(self, register: str, field: str) -> int:
        addr, lsb, mask = self._field_loc(register, field)
        return (await self._cpuif_read(addr) & mask) >> lsb

    async def program_defaults(self, *, page_policy: int = 1,
                               t_phy_wrlat: int = 1, t_rddata_en: int = 2,
                               mem_type: str = "DDR2", scheme: int = 0,
                               t_refi: int = 0x0400) -> None:
        """Program the timing / PHY / policy CSRs (by name) to a fast-sim-safe
        DDR2 config, then release init. page_policy is REFRESH_TUNING.page_policy_or,
        used DIRECTLY as pumice_pkg::page_policy_e: 0=OPEN, 1=CLOSE, 2=HAPPY_HYBRID."""
        w = self.csr_write_field
        # JEDEC timings (small, sim-fast; DFISlavePHY runs relaxed violation)
        await w("TIMINGS_RC_RCD_RP_RAS", "tRC", 6)
        await w("TIMINGS_RC_RCD_RP_RAS", "tRCD", 3)
        await w("TIMINGS_RC_RCD_RP_RAS", "tRP", 3)
        await w("TIMINGS_RC_RCD_RP_RAS", "tRAS", 4)
        await w("TIMINGS_RFC_REFI", "tRFC", 8)
        await w("TIMINGS_RFC_REFI", "tREFI", t_refi)
        await w("TIMINGS_RRD_FAW_WTR_CCD", "tRRD", 2)
        await w("TIMINGS_RRD_FAW_WTR_CCD", "tFAW", 6)
        await w("TIMINGS_RRD_FAW_WTR_CCD", "tWTR", 2)
        await w("TIMINGS_RRD_FAW_WTR_CCD", "tCCD", 2)
        await w("TIMINGS_CL_CWL_WR", "CL", 3)
        await w("TIMINGS_CL_CWL_WR", "CWL", 2)
        await w("TIMINGS_CL_CWL_WR", "tWR", 3)
        await w("TIMINGS_RTP_RTW", "tRTP", 2)
        await w("TIMINGS_RTP_RTW", "tRTW", 2)
        await w("DFI_PHASE", "rd_phase", 0)
        await w("DFI_PHASE", "wr_phase", 0)
        await w("PHY_TIMING", "t_phy_wrlat", t_phy_wrlat)
        await w("PHY_TIMING", "t_rddata_en", t_rddata_en)
        await w("PHY_TIMING", "memtype", 1 if mem_type.upper() == "LPDDR2" else 0)
        await w("PHY_TIMING", "refresh_burst", 1)
        await w("REFRESH_TUNING", "page_policy_or", page_policy)
        await w("ADDR_MAP_TUNING", "scheme_or", scheme)
        # fast init (zero the init waits)
        await w("INIT_TIMING0", "t_init_wait", 0)
        await w("INIT_TIMING0", "t_dll_wait", 0)
        await w("INIT_TIMING1", "t_mrd_wait", 0)
        await w("INIT_TIMING1", "t_rp_wait", 0)
        await w("INIT_TIMING1", "t_rfc_wait", 0)
        # kick init
        await w("CTRL", "init_start", 1)

    async def wait_for_init_done(self, timeout_cycles: int = 4000) -> None:
        for _ in range(timeout_cycles):
            await RisingEdge(self.dut.aclk)
            if int(self.dut.init_done_o.value):
                self.log.info("init_done observed")
                return
        raise AssertionError("init_done never asserted within timeout")

    # ---- BFM bring-up -----------------------------------------------------

    def init_dfi_slave(self, *, strict_violations: bool = False,
                       strict_timing: bool = False,
                       read_latency: int = 2, write_latency: int = 1) -> DFISlavePHY:
        """DFISlavePHY on dfi_clk (golden DRAM). Lenient by default (self-timed,
        matching the proven core/csr suites); flip DFI_STRICT_TIMING=1 to model
        the exact PHY data cadence (write captured at cmd+write_latency)."""
        import os as _os
        if _os.environ.get("DFI_STRICT_TIMING", "") in ("1", "true", "True"):
            strict_timing = True
        read_latency = int(_os.environ.get("DFI_READ_LATENCY", read_latency))
        write_latency = int(_os.environ.get("DFI_WRITE_LATENCY", write_latency))
        self.dfi_slave = DFISlavePHY(
            self.dut, self.dut.dfi_clk, base=self.dfi_base, memory=self.memory,
            strict_read_timing=strict_timing, strict_write_timing=strict_timing,
            read_latency=read_latency, write_latency=write_latency,
            dfi_phase_bytes=self.dram_beat_bytes,
        )
        if not strict_violations:
            self.dfi_slave.dram = DramStateModel(
                timings=self.dfi_base.timings,
                num_banks=self.dfi_base.mapping.num_banks,
                policy=ViolationPolicy(hard=frozenset()),
            )
        return self.dfi_slave

    def init_dfi_monitor(self) -> DFIMonitor:
        self.dfi_monitor = DFIMonitor(
            self.dut, self.dut.dfi_clk, side="phy", title="dfi_phy_monitor",
        )
        return self.dfi_monitor

    def init_axi_masters(self) -> tuple[AXI4MasterWrite, AXI4MasterRead]:
        self.axi_master_wr = AXI4MasterWrite(
            self.dut, self.dut.aclk, prefix="s_axi",
            data_width=self.axi_data_width, id_width=self.axi_id_width,
            addr_width=self.axi_addr_width, log=self.log,
        )
        self.axi_master_rd = AXI4MasterRead(
            self.dut, self.dut.aclk, prefix="s_axi",
            data_width=self.axi_data_width, id_width=self.axi_id_width,
            addr_width=self.axi_addr_width, log=self.log,
        )
        return self.axi_master_wr, self.axi_master_rd

    def set_axi_timing_profile(self, profile_name: str = "backtoback") -> None:
        from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
        from TBClasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS
        if self.axi_master_wr is None or self.axi_master_rd is None:
            raise RuntimeError("init_axi_masters() first")
        if profile_name not in AXI_RANDOMIZER_CONFIGS:
            raise ValueError(f"unknown profile '{profile_name}'")
        cfg = AXI_RANDOMIZER_CONFIGS[profile_name]
        self.axi_master_wr.aw_channel.randomizer = FlexRandomizer(cfg["master"])
        self.axi_master_wr.w_channel.randomizer = FlexRandomizer(cfg["master"])
        self.axi_master_rd.ar_channel.randomizer = FlexRandomizer(cfg["master"])
        self.axi_master_wr.b_channel.randomizer = FlexRandomizer(cfg["slave"])
        self.axi_master_rd.r_channel.randomizer = FlexRandomizer(cfg["slave"])
        self.log.info(f"AXI timing profile = '{profile_name}'")

    def set_axi_timing_per_channel(self, aw="fast", w="fast", b="fast",
                                   ar="fast", r="fast") -> None:
        from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
        from TBClasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS
        if self.axi_master_wr is None or self.axi_master_rd is None:
            raise RuntimeError("init_axi_masters() first")
        for name in (aw, w, b, ar, r):
            if name not in AXI_RANDOMIZER_CONFIGS:
                raise ValueError(f"unknown profile '{name}'")
        m, s = "master", "slave"
        self.axi_master_wr.aw_channel.randomizer = FlexRandomizer(AXI_RANDOMIZER_CONFIGS[aw][m])
        self.axi_master_wr.w_channel.randomizer = FlexRandomizer(AXI_RANDOMIZER_CONFIGS[w][m])
        self.axi_master_wr.b_channel.randomizer = FlexRandomizer(AXI_RANDOMIZER_CONFIGS[b][s])
        self.axi_master_rd.ar_channel.randomizer = FlexRandomizer(AXI_RANDOMIZER_CONFIGS[ar][m])
        self.axi_master_rd.r_channel.randomizer = FlexRandomizer(AXI_RANDOMIZER_CONFIGS[r][s])
        self.log.info("AXI per-channel: aw=%s w=%s b=%s ar=%s r=%s", aw, w, b, ar, r)

    # ---- memory preload + peek -------------------------------------------

    def preload_memory(self, byte_addr: int, data: bytes | bytearray) -> None:
        if not isinstance(data, (bytes, bytearray)):
            raise TypeError(f"data must be bytes/bytearray, got {type(data)}")
        self.memory.write(byte_addr, bytearray(data))

    def peek_memory(self, byte_addr: int, length: int) -> bytearray:
        return self.memory.read(byte_addr, length)

    # ---- AXI snoops (aclk) + golden verify -------------------------------

    def start_axi_wr_snoop(self) -> None:
        if self._axi_wr_snoop_task is not None:
            return
        self._axi_wr_snoop_task = cocotb.start_soon(self._axi_wr_snoop_loop())

    def stop_axi_wr_snoop(self) -> None:
        if self._axi_wr_snoop_task is not None:
            self._axi_wr_snoop_task.kill()
            self._axi_wr_snoop_task = None

    async def _axi_wr_snoop_loop(self) -> None:
        from collections import deque as _dq
        aw_q: _dq = _dq()
        cur_aw_addr = None
        cur_beat_idx = 0
        bpb = self.bytes_per_beat
        mask = (1 << (bpb * 8)) - 1
        while True:
            await RisingEdge(self.dut.aclk)
            try:
                if int(self.dut.s_axi_awvalid.value) and int(self.dut.s_axi_awready.value):
                    aw_q.append(int(self.dut.s_axi_awaddr.value))
                if int(self.dut.s_axi_wvalid.value) and int(self.dut.s_axi_wready.value):
                    if cur_aw_addr is None:
                        if not aw_q:
                            continue
                        cur_aw_addr = aw_q.popleft()
                        cur_beat_idx = 0
                    wd = int(self.dut.s_axi_wdata.value) & mask
                    self.axi_wr_snoop[cur_aw_addr + cur_beat_idx * bpb] = wd
                    cur_beat_idx += 1
                    if int(self.dut.s_axi_wlast.value):
                        cur_aw_addr = None
                        cur_beat_idx = 0
            except Exception:
                continue

    def start_axi_rd_snoop(self) -> None:
        if self._axi_rd_snoop_task is not None:
            return
        self._axi_rd_snoop_task = cocotb.start_soon(self._axi_rd_snoop_loop())

    def stop_axi_rd_snoop(self) -> None:
        if self._axi_rd_snoop_task is not None:
            self._axi_rd_snoop_task.kill()
            self._axi_rd_snoop_task = None

    async def _axi_rd_snoop_loop(self) -> None:
        from collections import deque as _dq
        pending: dict = {}
        bpb = self.bytes_per_beat
        mask = (1 << (bpb * 8)) - 1
        while True:
            await RisingEdge(self.dut.aclk)
            try:
                if int(self.dut.s_axi_arvalid.value) and int(self.dut.s_axi_arready.value):
                    arid = int(self.dut.s_axi_arid.value)
                    pending.setdefault(arid, _dq()).append(
                        [int(self.dut.s_axi_araddr.value),
                         int(self.dut.s_axi_arlen.value), 0])
                if int(self.dut.s_axi_rvalid.value) and int(self.dut.s_axi_rready.value):
                    rid = int(self.dut.s_axi_rid.value)
                    rdata = int(self.dut.s_axi_rdata.value) & mask
                    q = pending.get(rid)
                    if q:
                        head = q[0]
                        base, _alen, beat_idx = head
                        self.axi_rd_snoop.append((base + beat_idx * bpb, rdata, rid))
                        head[2] = beat_idx + 1
                        if int(self.dut.s_axi_rlast.value):
                            q.popleft()
            except Exception:
                continue

    def verify_axi_rd_matches_memory(self) -> Optional[tuple]:
        """Every snooped AXI R beat vs the golden MemoryModel at its byte addr.
        Snarf / OOO are transparent (looked up by the requested byte addr)."""
        bpb = self.bytes_per_beat
        for byte_addr, actual_int, rid in self.axi_rd_snoop:
            mem_int = int.from_bytes(bytes(self.memory.read(byte_addr, bpb)), "little")
            if actual_int != mem_int:
                return (byte_addr, mem_int, actual_int, rid)
        return None

    def verify_memory_matches_axi_wr(self) -> Optional[tuple]:
        bpb = self.bytes_per_beat
        for byte_addr, expected_int in self.axi_wr_snoop.items():
            actual_int = int.from_bytes(bytes(self.memory.read(byte_addr, bpb)), "little")
            if actual_int != expected_int:
                return (byte_addr, expected_int, actual_int)
        return None

    # ---- sequences --------------------------------------------------------

    async def run_sequence(self, seq: AXI4Sequence) -> Sequence[dict]:
        if self.axi_master_wr is None or self.axi_master_rd is None:
            raise RuntimeError("call init_axi_masters() first")
        return await run_axi4_sequence(
            seq, master_wr=self.axi_master_wr, master_rd=self.axi_master_rd, log=self.log,
        )

    async def run_writes(self, wr_seq: AXI4Sequence, *, drain_cycles: int = 300):
        """Run a write-only AXI4Sequence through the write master BFM and let
        the writes commit/drain to the golden DRAM."""
        await self.run_sequence(wr_seq)
        await ClockCycles(self.dut.aclk, drain_cycles)

    async def run_reads(self, rd_seq: AXI4Sequence) -> list:
        """Run a read-only AXI4Sequence through the read master BFM; return the
        per-burst beat-value lists (the sequence result 'data' field)."""
        rd_dicts = await self.run_sequence(rd_seq)
        return [d["data"] for d in rd_dicts]
