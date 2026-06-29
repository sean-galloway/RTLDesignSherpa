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
from CocoTBFramework.components.dfi.dfi_monitor import DFIMonitor
from CocoTBFramework.components.dfi.dfi_packet import DRAMCommand
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
        self.dfi_monitor: Optional[DFIMonitor] = None
        # AXI WR snoop — per-beat (byte_addr, data_int) records built
        # by a coroutine that watches s_axi_aw + s_axi_w. Indexed by
        # byte_addr; the test compares against peek_memory after writes
        # drain to localize AXI-WR → DFI-WR → memory corruption.
        self.axi_wr_snoop: dict = {}
        self._axi_wr_snoop_task = None
        # AXI RD snoop — list of (byte_addr, data_int) for every AXI R
        # beat the controller returns. Built by snooping s_axi_ar +
        # s_axi_r and pairing by id (AXI4 same-id in-order semantics).
        # verify_axi_rd_matches_memory() compares against the DFI
        # MemoryModel at each byte addr — snarfing/OOO are transparent
        # because we lookup by the actual byte addr the engine asked for.
        self.axi_rd_snoop: list = []
        self._axi_rd_snoop_task = None

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

    def start_axi_wr_snoop(self, axi_path=None) -> None:
        """Spawn a coroutine that watches s_axi_aw + s_axi_w + s_axi_wlast
        and records every AXI WR beat into ``self.axi_wr_snoop`` keyed
        by byte address.

        Args:
            axi_path: The scope where ``s_axi_*`` signals live. Defaults
                to ``self.dut`` (for envs where the controller's slave
                port is exposed at the top). For envs that wrap the
                controller (e.g. NexysA7's ``u_dut.u_ctrl``), pass that
                handle so the snoop reaches the real signals.

        Stop with ``stop_axi_wr_snoop()`` or just let it run until sim end.
        """
        import cocotb as _cocotb
        if self._axi_wr_snoop_task is not None:
            return
        self._axi_wr_path = axi_path if axi_path is not None else self.dut
        self._axi_wr_snoop_task = _cocotb.start_soon(self._axi_wr_snoop_loop())

    def stop_axi_wr_snoop(self) -> None:
        if self._axi_wr_snoop_task is not None:
            self._axi_wr_snoop_task.kill()
            self._axi_wr_snoop_task = None

    async def _axi_wr_snoop_loop(self) -> None:
        """Per-cycle snoop: track AW handshakes into a FIFO, walk each
        AW's burst on every W handshake, store data at the beat's byte
        addr. Pure observer, no drive."""
        from collections import deque as _dq
        from cocotb.triggers import RisingEdge as _RisingEdge
        aw_q: _dq = _dq()
        cur_aw_addr = None
        cur_beat_idx = 0
        bytes_per_beat = self.bytes_per_beat
        mask = (1 << (bytes_per_beat * 8)) - 1
        while True:
            await _RisingEdge(self.dut.mc_clk)
            # AW handshake
            try:
                awv = int(self.dut.s_axi_awvalid.value)
                awr = int(self.dut.s_axi_awready.value)
            except Exception:
                continue
            if awv and awr:
                addr = int(self.dut.s_axi_awaddr.value)
                aw_q.append(addr)
            # W handshake
            try:
                wv = int(self.dut.s_axi_wvalid.value)
                wr = int(self.dut.s_axi_wready.value)
            except Exception:
                continue
            if wv and wr:
                if cur_aw_addr is None:
                    if not aw_q:
                        continue  # W before AW — skip (early sim edge)
                    cur_aw_addr = aw_q.popleft()
                    cur_beat_idx = 0
                wd = int(self.dut.s_axi_wdata.value) & mask
                byte_addr = cur_aw_addr + cur_beat_idx * bytes_per_beat
                self.axi_wr_snoop[byte_addr] = wd
                cur_beat_idx += 1
                if int(self.dut.s_axi_wlast.value):
                    cur_aw_addr = None
                    cur_beat_idx = 0

    def start_axi_rd_snoop(self) -> None:
        """Spawn a coroutine that watches s_axi_ar + s_axi_r and
        records every AXI R beat (byte_addr, returned_data_int) into
        ``self.axi_rd_snoop``. Pair ARs to R bursts by id (AXI4 same-id
        in-order semantics).
        """
        import cocotb as _cocotb
        if self._axi_rd_snoop_task is not None:
            return
        self._axi_rd_snoop_task = _cocotb.start_soon(self._axi_rd_snoop_loop())

    def stop_axi_rd_snoop(self) -> None:
        if self._axi_rd_snoop_task is not None:
            self._axi_rd_snoop_task.kill()
            self._axi_rd_snoop_task = None

    async def _axi_rd_snoop_loop(self) -> None:
        """Per-cycle: track AR handshakes into per-id FIFOs; on each
        R handshake, peek the head pending AR for that id and compute
        this beat's byte address."""
        from collections import deque as _dq
        from cocotb.triggers import RisingEdge as _RisingEdge
        # per-id deque of pending (base_addr, len_minus_1, beats_returned)
        pending: dict = {}
        bytes_per_beat = self.bytes_per_beat
        rdata_mask = (1 << (bytes_per_beat * 8)) - 1
        while True:
            await _RisingEdge(self.dut.mc_clk)
            try:
                arv = int(self.dut.s_axi_arvalid.value)
                arr = int(self.dut.s_axi_arready.value)
            except Exception:
                continue
            if arv and arr:
                arid  = int(self.dut.s_axi_arid.value)
                addr  = int(self.dut.s_axi_araddr.value)
                alen  = int(self.dut.s_axi_arlen.value)
                pending.setdefault(arid, _dq()).append([addr, alen, 0])
            try:
                rv = int(self.dut.s_axi_rvalid.value)
                rr = int(self.dut.s_axi_rready.value)
            except Exception:
                continue
            if rv and rr:
                rid = int(self.dut.s_axi_rid.value)
                rdata = int(self.dut.s_axi_rdata.value) & rdata_mask
                q = pending.get(rid)
                if q:
                    head = q[0]
                    base, alen, beat_idx = head
                    byte_addr = base + beat_idx * bytes_per_beat
                    self.axi_rd_snoop.append((byte_addr, rdata, rid))
                    head[2] = beat_idx + 1
                    if int(self.dut.s_axi_rlast.value):
                        q.popleft()

    def verify_axi_rd_matches_memory(
        self,
    ) -> Optional[tuple]:
        """Compare every AXI R beat the controller returned (snooped on
        s_axi_r* + AR-pairing) against the DFI MemoryModel state at the
        same byte address. A mismatch means the controller delivered
        wrong data on the R channel for that byte addr — pure RD-path
        corruption (rd_cl_aligner / axi_intake R-emit / scheduler RD
        pick / wr2rd_forward).

        Note: this verifies that R data matches MEMORY, not that the
        engine got what it expected. Snarfing + OOO are transparent —
        we look up by the actual byte address the engine requested.

        Returns:
            None if every snooped AXI R beat matches memory.
            (byte_addr, expected_int, actual_int, rid) of the first
            mismatch.
        """
        bpb = self.bytes_per_beat
        for byte_addr, actual_int, rid in self.axi_rd_snoop:
            mem_bytes = bytes(self.memory.read(byte_addr, bpb))
            mem_int = int.from_bytes(mem_bytes, "little")
            if actual_int != mem_int:
                return (byte_addr, mem_int, actual_int, rid)
        return None

    def verify_memory_matches_axi_wr(
        self,
    ) -> Optional[tuple]:
        """Compare every (byte_addr, data) the AXI WR snoop captured
        against the DFISlavePHY's MemoryModel state. A mismatch means
        the controller corrupted on the way from AXI WR → DFI WR →
        memory (since the BFM is known-good, that points at the
        controller).

        Call after wr_done + a small drain delay so all DFI WR data has
        landed in memory.

        Returns:
            None if every snooped AXI WR beat matches memory.
            (byte_addr, expected_int, actual_int) of the first mismatch.
        """
        bpb = self.bytes_per_beat
        for byte_addr, expected_int in self.axi_wr_snoop.items():
            actual_bytes = bytes(self.memory.read(byte_addr, bpb))
            actual_int = int.from_bytes(actual_bytes, "little")
            if actual_int != expected_int:
                return (byte_addr, expected_int, actual_int)
        return None

    def init_dfi_monitor(self) -> DFIMonitor:
        """Passive DFIMonitor that captures every ACT / RD / WR / PRE /
        REF command and every wrdata / rddata beat into per-sub-interface
        queues (command_q, write_data_q, read_data_q). Use the verify_*
        helpers below to walk those queues post-test.

        Wires to the same `phy_dfi_*` signal cluster as the DFISlavePHY;
        purely observational, doesn't drive anything.
        """
        self.dfi_monitor = DFIMonitor(
            self.dut, self.dut.mc_clk, side="phy",
            title="dfi_phy_monitor",
        )
        return self.dfi_monitor

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

    def set_axi_timing_profile(self, profile_name: str = "backtoback") -> None:
        """Apply an AXI_RANDOMIZER_CONFIGS profile to every AXI channel.

        BFM default timing inserts bubbles on valid/ready, which DOESN'T
        match what real engine traffic looks like (the engine's
        axi4_master_wr_pattern_gen drives every cycle). Use 'backtoback'
        to mimic the engine. Mixing profiles per channel is a future
        extension that'll catch a much broader bug class than the
        single-profile sweep we have today — most controller-side
        scheduler / wbuf / cam tests are run with default-only timing.
        """
        from CocoTBFramework.components.shared.flex_randomizer import (
            FlexRandomizer,
        )
        from TBClasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS

        if self.axi_master_wr is None or self.axi_master_rd is None:
            raise RuntimeError(
                "init_axi_masters() must be called before "
                "set_axi_timing_profile()"
            )
        if profile_name not in AXI_RANDOMIZER_CONFIGS:
            raise ValueError(f"unknown profile '{profile_name}'")
        cfg = AXI_RANDOMIZER_CONFIGS[profile_name]
        # AW / W / AR — master drives valid
        self.axi_master_wr.aw_channel.randomizer = FlexRandomizer(cfg["master"])
        self.axi_master_wr.w_channel.randomizer  = FlexRandomizer(cfg["master"])
        self.axi_master_rd.ar_channel.randomizer = FlexRandomizer(cfg["master"])
        # B / R — slave drives ready
        self.axi_master_wr.b_channel.randomizer  = FlexRandomizer(cfg["slave"])
        self.axi_master_rd.r_channel.randomizer  = FlexRandomizer(cfg["slave"])
        self.log.info(f"AXI timing profile = '{profile_name}'")

    def set_axi_timing_per_channel(
        self,
        aw: str = "fast",
        w:  str = "fast",
        b:  str = "fast",
        ar: str = "fast",
        r:  str = "fast",
    ) -> None:
        """Apply a different AXI_RANDOMIZER_CONFIGS profile to each channel.

        Per-channel sweeps catch cross-channel interaction bugs that
        uniform sweeps miss — e.g. fast AW + slow_producer W can wedge
        wbuf/cam pressure differently than uniform 'slow'.
        """
        from CocoTBFramework.components.shared.flex_randomizer import (
            FlexRandomizer,
        )
        from TBClasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS

        if self.axi_master_wr is None or self.axi_master_rd is None:
            raise RuntimeError(
                "init_axi_masters() must be called before "
                "set_axi_timing_per_channel()"
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

    # ---- DFI-side verification helpers -----------------------------------

    def verify_dfi_writes(
        self,
        expected: dict,
    ) -> Optional[tuple]:
        """Walk the DFI monitor's command_q for WR commands and pair
        each with the next `beats_per_burst` entries from write_data_q,
        decode each beat's byte address via the same mapping the
        DFISlavePHY uses, and compare against `expected[byte_addr]`.

        Args:
            expected: ``{byte_addr → expected_byte_value_lower_64bits}``
                — one entry per DRAM beat. Caller builds this from the
                AXI-side write data (LFSR pattern, etc.).

        Returns:
            None if every observed WR beat matches expected.
            (byte_addr, expected_int, actual_int) at the first mismatch.

        Requires ``init_dfi_monitor()`` to have been called.
        """
        if self.dfi_monitor is None:
            raise RuntimeError("verify_dfi_writes requires init_dfi_monitor()")
        from collections import deque
        wrdata_q = deque(self.dfi_monitor.write_data_q)
        open_row = {}  # bank → last-ACT row
        bpb = self.dfi_base.beats_per_burst   # DRAM beats per DFI burst
        bytes_per_beat = self.bytes_per_beat
        dfi_data_bits = self.dfi_base.field_config_for(  # 64 / 128 etc.
            __import__("CocoTBFramework.components.dfi.dfi_signals",
                       fromlist=["SubInterface"]).SubInterface.WRITE_DATA,
        ).get_field("wrdata").bit_width
        bits_per_dfi_cycle = dfi_data_bits   # 128 typical
        bits_per_beat = bytes_per_beat * 8   # 64
        dfi_rate = bits_per_dfi_cycle // bits_per_beat
        for cmd_pkt in self.dfi_monitor.command_q:
            if cmd_pkt.cmd == DRAMCommand.ACT:
                open_row[cmd_pkt.bank] = cmd_pkt.address
                continue
            if cmd_pkt.cmd != DRAMCommand.WR:
                continue
            bank = cmd_pkt.bank
            row = open_row.get(bank, 0)
            base_col = cmd_pkt.address & ((1 << self.col_width) - 1)
            for k in range(bpb):
                col_k = base_col + k
                if col_k >= self.mapping.num_cols:
                    break
                flat = self.mapping.tuple_to_flat(0, bank, row, col_k)
                byte_addr = flat * bytes_per_beat
                # Pop the next DRAM beat from write_data_q. Each DFI
                # cycle carries dfi_rate beats packed in wrdata.
                dfi_phase_in_cycle = k % dfi_rate
                if dfi_phase_in_cycle == 0:
                    if not wrdata_q:
                        return (byte_addr, expected.get(byte_addr, -1), -1)
                    cur_dfi_pkt = wrdata_q.popleft()
                # Extract this beat from the DFI cycle's packed wrdata
                shift = dfi_phase_in_cycle * bits_per_beat
                mask = (1 << bits_per_beat) - 1
                actual = (cur_dfi_pkt.wrdata >> shift) & mask
                exp = expected.get(byte_addr)
                if exp is None:
                    continue   # not in expected — skip silently
                if actual != (exp & mask):
                    return (byte_addr, exp & mask, actual)
        return None

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
