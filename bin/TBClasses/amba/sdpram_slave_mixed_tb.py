# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: SdpramSlaveMixedTB
# Purpose: Shared testbench for the three mixed-protocol sdpram_slave_*
#          wrappers (sdpram_slave_axi4_axil, sdpram_slave_axil_axi4,
#          sdpram_slave_axil_axil) plus the pure AXI4 wrapper if a caller
#          wants it. Drives whichever side is AXI4-shaped with the AXI4
#          master factory and whichever side is AXIL-shaped with the AXIL4
#          master factory -- never hand-pokes s_axi_*/s_axil_*.
#
# Subsystem: framework
# Author: sean galloway

"""
SdpramSlaveMixedTB

The three sdpram_slave_* wrappers under test share one backend
(sdpram_core) and differ only in which side (write/read) is AXI4-shaped
(s_axi_* with id/len/size/burst) vs AXIL4-shaped (s_axil_* single-beat).
This TB class parameterizes over WR_PROTOCOL/RD_PROTOCOL so one class
serves all three (and the fourth, axi4_axi4, for completeness) without
duplicating driver code per wrapper.

BFM axis: AXI4MasterWrite/Read (via create_axi4_master_wr/rd) and
AXIL4MasterWrite/Read (via create_axil4_master_wr/rd) -- RDS-DV factories,
never hand-rolled signal pokes. i_cfg_start_clear / o_cfg_done_clear /
o_dbg_vr are plain control/debug signals outside any AXI channel, so they
are driven/sampled directly on `dut`, same as the model FUB test does.
"""

import os
import random
from typing import Dict, List, Optional

import cocotb
from cocotb.triggers import RisingEdge

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.axi4.axi4_factories import (
    create_axi4_master_rd,
    create_axi4_master_wr,
)
from CocoTBFramework.components.axil4.axil4_factories import (
    create_axil4_master_rd,
    create_axil4_master_wr,
)

# AXI4 burst-type encoding (also accepted, ignored, by the AXIL4 API).
BURST_FIXED = 0
BURST_INCR = 1
BURST_WRAP = 2


class SdpramSlaveMixedTB(TBBase):
    """Drives a sdpram_slave_{axi4,axil}_{axi4,axil} wrapper via the RDS-DV
    AXI4/AXIL4 master factories, picking the factory per side from
    wr_protocol/rd_protocol.
    """

    def __init__(self, dut, wr_protocol: str, rd_protocol: str,
                 aclk=None, aresetn=None):
        super().__init__(dut)

        assert wr_protocol in ("AXI4", "AXIL")
        assert rd_protocol in ("AXI4", "AXIL")
        self.wr_protocol = wr_protocol
        self.rd_protocol = rd_protocol

        self.data_width = self.convert_to_int(os.environ.get('DUT_DATA_WIDTH', '64'))
        self.addr_width = self.convert_to_int(os.environ.get('DUT_ADDR_WIDTH', '32'))
        self.mem_depth = self.convert_to_int(os.environ.get('DUT_MEM_DEPTH', '64'))
        self.id_width = self.convert_to_int(os.environ.get('DUT_ID_WIDTH', '4'))
        self.seed = self.convert_to_int(os.environ.get('SEED', '0'))
        random.seed(self.seed)

        self.word_bytes = self.data_width // 8
        self.size_log2 = (self.word_bytes - 1).bit_length()
        self.mask = (1 << self.data_width) - 1

        self.aclk = aclk
        self.aclk_name = aclk._name if aclk else 'aclk'
        self.aresetn = aresetn

        self.log.info(
            f"SdpramSlaveMixedTB: WR={wr_protocol} RD={rd_protocol} "
            f"DATA_WIDTH={self.data_width} MEM_DEPTH={self.mem_depth} "
            f"seed={self.seed}"
        )

        # -----------------------------------------------------------
        # Write-side master
        # -----------------------------------------------------------
        if wr_protocol == "AXI4":
            self.wr_components = create_axi4_master_wr(
                dut=dut, clock=aclk, prefix="s_axi", log=self.log,
                data_width=self.data_width, id_width=self.id_width,
                addr_width=self.addr_width, user_width=1, multi_sig=True,
            )
        else:
            self.wr_components = create_axil4_master_wr(
                dut=dut, clock=aclk, prefix="s_axil_", log=self.log,
                data_width=self.data_width, addr_width=self.addr_width,
                multi_sig=True,
            )
        self.wr_master = self.wr_components['interface']

        # -----------------------------------------------------------
        # Read-side master
        # -----------------------------------------------------------
        if rd_protocol == "AXI4":
            self.rd_components = create_axi4_master_rd(
                dut=dut, clock=aclk, prefix="s_axi", log=self.log,
                data_width=self.data_width, id_width=self.id_width,
                addr_width=self.addr_width, user_width=1, multi_sig=True,
            )
        else:
            self.rd_components = create_axil4_master_rd(
                dut=dut, clock=aclk, prefix="s_axil_", log=self.log,
                data_width=self.data_width, addr_width=self.addr_width,
                multi_sig=True,
            )
        self.rd_master = self.rd_components['interface']

    # -----------------------------------------------------------------
    # TBBase-mandated lifecycle methods
    # -----------------------------------------------------------------
    async def assert_reset(self):
        self.aresetn.value = 0
        self.dut.i_cfg_start_clear.value = 0
        for chan_key in ("AW", "W", "B"):
            comp = self.wr_components.get(chan_key)
            if comp is not None and hasattr(comp, "reset_bus"):
                await comp.reset_bus()
        for chan_key in ("AR", "R"):
            comp = self.rd_components.get(chan_key)
            if comp is not None and hasattr(comp, "reset_bus"):
                await comp.reset_bus()
        await self.wait_clocks(self.aclk_name, 5)

    async def deassert_reset(self):
        self.aresetn.value = 1
        await self.wait_clocks(self.aclk_name, 5)

    async def setup_clocks_and_reset(self):
        await self.start_clock(self.aclk_name, 10, 'ns')
        await self.assert_reset()
        await self.wait_clocks(self.aclk_name, 10)
        await self.deassert_reset()

    # -----------------------------------------------------------------
    # Write / read helpers -- route through the correct protocol's master
    # -----------------------------------------------------------------
    async def write_single(self, addr: int, data: int, strb: Optional[int] = None) -> None:
        """Single-beat write. Raises on any non-OKAY response."""
        data &= self.mask
        if self.wr_protocol == "AXI4":
            kwargs = {"burst_len": 1, "size": self.size_log2, "burst_type": BURST_INCR}
            if strb is not None:
                kwargs["strb"] = strb
            result = await self.wr_master.write_transaction(addr, data, **kwargs)
            if not result.get("success", False):
                raise RuntimeError(f"AXI4 single write failed at 0x{addr:x}: {result}")
        else:
            await self.wr_master.write_transaction(addr, data, strb=strb)

    async def write_burst(self, addr: int, data_list: List[int],
                           burst_type: int = BURST_INCR) -> None:
        """AXI4-only burst write. Raises if called on an AXIL write side."""
        if self.wr_protocol != "AXI4":
            raise RuntimeError("write_burst is only valid on an AXI4 write side")
        data_list = [d & self.mask for d in data_list]
        result = await self.wr_master.write_transaction(
            addr, data_list, burst_len=len(data_list),
            size=self.size_log2, burst_type=burst_type,
        )
        if not result.get("success", False):
            raise RuntimeError(f"AXI4 burst write failed at 0x{addr:x}: {result}")

    async def read_single(self, addr: int) -> int:
        """Single-beat read. Raises on any non-OKAY response."""
        if self.rd_protocol == "AXI4":
            data_list = await self.rd_master.read_transaction(
                addr, burst_len=1, size=self.size_log2, burst_type=BURST_INCR,
            )
            return data_list[0] & self.mask
        return (await self.rd_master.read_transaction(addr)) & self.mask

    async def read_burst(self, addr: int, n_beats: int,
                          burst_type: int = BURST_INCR) -> List[int]:
        """AXI4-only burst read. Raises if called on an AXIL read side."""
        if self.rd_protocol != "AXI4":
            raise RuntimeError("read_burst is only valid on an AXI4 read side")
        data_list = await self.rd_master.read_transaction(
            addr, burst_len=n_beats, size=self.size_log2, burst_type=burst_type,
        )
        return [d & self.mask for d in data_list]

    # -----------------------------------------------------------------
    # Bulk-clear + debug-tap helpers.  Neither i_cfg_start_clear /
    # o_cfg_done_clear nor o_dbg_vr sit on an AXI channel -- they are the
    # wrapper's own control/debug surface, so a direct dut poke here (as
    # the model sdpram_slave FUB test does) is not a hand-rolled protocol
    # driver.
    # -----------------------------------------------------------------
    async def bulk_clear(self, timeout_cycles: int = 20000) -> None:
        """Pulse i_cfg_start_clear and wait for o_cfg_done_clear to rise.

        o_cfg_done_clear is a STICKY LEVEL, not a pulse: once the clear
        completes it stays high until the *next* clear request is
        accepted. Callers must not assume it self-clears.

        The clear FSM only accepts i_cfg_start_clear while write/read/
        inflight tracking is idle, and those tracking flags drop one
        cycle *after* the handshake that quiesces them (registered, not
        combinational) -- so a settle window is needed after the last
        AXI/AXIL transaction before the strobe is guaranteed accepted.
        """
        await self.wait_clocks(self.aclk_name, 3)
        self.dut.i_cfg_start_clear.value = 1
        await RisingEdge(self.aclk)
        self.dut.i_cfg_start_clear.value = 0

        cycles = 0
        while int(self.dut.o_cfg_done_clear.value) == 0:
            await RisingEdge(self.aclk)
            cycles += 1
            if cycles > timeout_cycles:
                raise TimeoutError(
                    f"bulk_clear: o_cfg_done_clear did not rise within "
                    f"{timeout_cycles} cycles"
                )

    def dbg_vr_fields(self) -> Dict[str, int]:
        """Decode o_dbg_vr[9:0] into its five (ready,valid) pairs.

        Bit layout (from the RTL): R=[9:8], AR=[7:6], B=[5:4], W=[3:2],
        AW=[1:0]; within each pair bit0=valid, bit1=ready.
        """
        v = int(self.dut.o_dbg_vr.value)
        return {
            "aw_valid": v & 0x1, "aw_ready": (v >> 1) & 0x1,
            "w_valid": (v >> 2) & 0x1, "w_ready": (v >> 3) & 0x1,
            "b_valid": (v >> 4) & 0x1, "b_ready": (v >> 5) & 0x1,
            "ar_valid": (v >> 6) & 0x1, "ar_ready": (v >> 7) & 0x1,
            "r_valid": (v >> 8) & 0x1, "r_ready": (v >> 9) & 0x1,
        }

    def _read_direct_vr(self) -> Dict[str, int]:
        """Sample the raw AW/W/B/AR/R valid+ready ports directly (protocol
        picked per side), independent of the o_dbg_vr mux under test."""
        d = self.dut
        if self.wr_protocol == "AXI4":
            aw_v, aw_r = int(d.s_axi_awvalid.value), int(d.s_axi_awready.value)
            w_v, w_r = int(d.s_axi_wvalid.value), int(d.s_axi_wready.value)
            b_v, b_r = int(d.s_axi_bvalid.value), int(d.s_axi_bready.value)
        else:
            aw_v, aw_r = int(d.s_axil_awvalid.value), int(d.s_axil_awready.value)
            w_v, w_r = int(d.s_axil_wvalid.value), int(d.s_axil_wready.value)
            b_v, b_r = int(d.s_axil_bvalid.value), int(d.s_axil_bready.value)

        if self.rd_protocol == "AXI4":
            ar_v, ar_r = int(d.s_axi_arvalid.value), int(d.s_axi_arready.value)
            r_v, r_r = int(d.s_axi_rvalid.value), int(d.s_axi_rready.value)
        else:
            ar_v, ar_r = int(d.s_axil_arvalid.value), int(d.s_axil_arready.value)
            r_v, r_r = int(d.s_axil_rvalid.value), int(d.s_axil_rready.value)

        return {
            "aw_valid": aw_v, "aw_ready": aw_r,
            "w_valid": w_v, "w_ready": w_r,
            "b_valid": b_v, "b_ready": b_r,
            "ar_valid": ar_v, "ar_ready": ar_r,
            "r_valid": r_v, "r_ready": r_r,
        }

    def start_dbg_vr_monitor(self) -> None:
        """Spawn a background task that cross-checks o_dbg_vr's decoded
        bit-order against the raw AW/W/B/AR/R ports on every cycle for the
        rest of the test. Call check_dbg_vr_clean() at the end."""
        self._dbg_vr_mismatches: List[tuple] = []
        self._dbg_vr_monitor_task = cocotb.start_soon(self._dbg_vr_monitor_loop())

    async def _dbg_vr_monitor_loop(self) -> None:
        while True:
            await RisingEdge(self.aclk)
            decoded = self.dbg_vr_fields()
            direct = self._read_direct_vr()
            for key, direct_val in direct.items():
                if decoded[key] != direct_val:
                    self._dbg_vr_mismatches.append((key, decoded[key], direct_val))

    def check_dbg_vr_clean(self) -> None:
        assert not self._dbg_vr_mismatches, (
            f"o_dbg_vr bit-order mismatch(es) (field, decoded, direct): "
            f"{self._dbg_vr_mismatches[:5]} (+{max(0, len(self._dbg_vr_mismatches) - 5)} more)"
        )

    # -----------------------------------------------------------------
    # Test phases -- shared across all sdpram_slave_* wrapper tests.
    # -----------------------------------------------------------------
    async def phase_single_beat(self) -> None:
        """1-beat write + read round trip on whatever ports this wrapper
        exposes (AXI4 single-beat or AXIL, on either side)."""
        addr = 0x0
        data = 0xCAFEBABEDEADBEEF & self.mask
        await self.write_single(addr, data)
        got = await self.read_single(addr)
        assert got == data, f"single-beat readback 0x{got:x} != expected 0x{data:x}"

    async def phase_axi4_write_burst(self) -> None:
        """INCR + FIXED write bursts. No-op unless the write side is AXI4
        (AXIL is single-beat by construction)."""
        if self.wr_protocol != "AXI4":
            return

        base = 4 * self.word_bytes
        burst_data = [(0x1111111100000000 | i) & self.mask for i in range(4)]
        await self.write_burst(base, burst_data, burst_type=BURST_INCR)
        for i, expected in enumerate(burst_data):
            got = await self.read_single(base + i * self.word_bytes)
            assert got == expected, (
                f"INCR write-burst beat {i} at 0x{base + i * self.word_bytes:x}: "
                f"read 0x{got:x} != expected 0x{expected:x}"
            )

        fixed_addr = 32 * self.word_bytes
        fixed_beats = [(0xAAAA000000000000 | (i * 0x10)) & self.mask for i in range(4)]
        await self.write_burst(fixed_addr, fixed_beats, burst_type=BURST_FIXED)
        got = await self.read_single(fixed_addr)
        assert got == fixed_beats[-1], (
            f"FIXED write-burst last-beat-wins: read 0x{got:x} != "
            f"expected 0x{fixed_beats[-1]:x}"
        )

    async def phase_axi4_read_burst(self) -> None:
        """INCR + FIXED read bursts. No-op unless the read side is AXI4."""
        if self.rd_protocol != "AXI4":
            return

        base = 8 * self.word_bytes
        burst_data = [(0x2222222200000000 | i) & self.mask for i in range(4)]
        for i, d in enumerate(burst_data):
            await self.write_single(base + i * self.word_bytes, d)
        got = await self.read_burst(base, 4, burst_type=BURST_INCR)
        assert got == burst_data, f"INCR read-burst mismatch: {got} != {burst_data}"

        fixed_addr = 40 * self.word_bytes
        fixed_data = 0x3333333300000000 & self.mask
        await self.write_single(fixed_addr, fixed_data)
        got = await self.read_burst(fixed_addr, 4, burst_type=BURST_FIXED)
        assert all(b == fixed_data for b in got), (
            f"FIXED read-burst: expected every beat == 0x{fixed_data:x}, got {got}"
        )

    async def phase_random_fill(self, count: int) -> Dict[int, int]:
        """Random single-beat fill across `count` unique addresses, then
        read back and compare against a software mirror (the golden
        model). Returns the mirror dict for callers that want to inspect
        or mutate it (mutation-check hook)."""
        count = min(count, self.mem_depth)
        expected: Dict[int, int] = {}
        for i in range(count):
            addr = i * self.word_bytes
            expected[addr] = random.randint(0, self.mask)

        for addr, data in expected.items():
            await self.write_single(addr, data)

        mismatches = 0
        for addr, exp_data in expected.items():
            got = await self.read_single(addr)
            if got != exp_data:
                mismatches += 1
                self.log.error(
                    f"random_fill mismatch @0x{addr:x}: got 0x{got:x} != "
                    f"expected 0x{exp_data:x}"
                )
        assert mismatches == 0, f"{mismatches}/{count} random-fill readbacks mismatched"
        return expected

    async def phase_bulk_clear(self) -> None:
        """Fill the whole memory with a known non-zero pattern, clear it,
        verify every address reads back zero, and verify o_cfg_done_clear
        behaves as a STICKY LEVEL: it does not self-clear while idle, and
        a second clear request drops it low again before it rises on that
        clear's completion."""
        for i in range(self.mem_depth):
            data = (0xA5A5A5A5A5A5A5A5 + i) & self.mask
            await self.write_single(i * self.word_bytes, data)

        await self.bulk_clear()
        assert int(self.dut.o_cfg_done_clear.value) == 1, (
            "o_cfg_done_clear did not assert after the clear completed"
        )

        # Sticky-level contract: must NOT self-clear while idle.
        for _ in range(50):
            await RisingEdge(self.aclk)
            assert int(self.dut.o_cfg_done_clear.value) == 1, (
                "o_cfg_done_clear dropped with no new clear request pending -- "
                "it is documented as a sticky level, not a pulse"
            )

        mismatches = 0
        for i in range(self.mem_depth):
            got = await self.read_single(i * self.word_bytes)
            if got != 0:
                mismatches += 1
                self.log.error(f"post-clear readback @word {i}: got 0x{got:x}, expected 0")
        assert mismatches == 0, f"{mismatches}/{self.mem_depth} post-clear readbacks were non-zero"

        # A second clear request must drop the level low again before it
        # rises on completion -- confirms it tracks "clear in flight"
        # rather than latching once at the first completion forever.
        await self._assert_second_clear_drops_and_completes()

    async def _assert_second_clear_drops_and_completes(
        self, accept_window_cycles: int = 20, timeout_cycles: int = 20000
    ) -> None:
        """o_cfg_done_clear is already 1 here (from a prior clear). Confirm
        a new i_cfg_start_clear request drives it low again (acceptance
        is registered, so the drop can lag the strobe by a cycle or two --
        poll a small window rather than assuming the very next edge) and
        that it rises again once that clear completes."""
        await self.wait_clocks(self.aclk_name, 3)
        assert int(self.dut.o_cfg_done_clear.value) == 1, (
            "expected o_cfg_done_clear already high before requesting a second clear"
        )

        self.dut.i_cfg_start_clear.value = 1
        dropped = False
        for _ in range(accept_window_cycles):
            await RisingEdge(self.aclk)
            if int(self.dut.o_cfg_done_clear.value) == 0:
                dropped = True
                break
        self.dut.i_cfg_start_clear.value = 0
        assert dropped, (
            f"second clear request did not drop the sticky o_cfg_done_clear "
            f"level within {accept_window_cycles} cycles of being asserted"
        )

        cycles = 0
        while int(self.dut.o_cfg_done_clear.value) == 0:
            await RisingEdge(self.aclk)
            cycles += 1
            if cycles > timeout_cycles:
                raise TimeoutError("second clear request never completed")

    async def run_standard_suite(self, test_level: str = "gate") -> None:
        """Orchestrates the phases above, scaled by TEST_LEVEL. Shared by
        all three thin per-wrapper test files."""
        counts = {"gate": 8, "func": 32, "full": 64}
        count = counts.get(test_level, 8)

        self.start_dbg_vr_monitor()

        await self.phase_single_beat()
        await self.phase_axi4_write_burst()
        await self.phase_axi4_read_burst()
        await self.phase_random_fill(count)
        await self.phase_bulk_clear()

        self.check_dbg_vr_clean()
