# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Author: sean galloway
# Created: 2026-06-18

"""
TB class for axi_frontend_macro using CocoTBFramework AXI4 BFMs and
FlexRandomizer for directed-random timing-profile testing.

DUT is an AXI4 slave (host signals are s_axi_*). The TB uses:
  - AXI4MasterWrite : drives s_axi_aw* / w*, receives s_axi_b*
  - AXI4MasterRead  : drives s_axi_ar*, receives s_axi_r*
  - FlexRandomizer  : per-channel valid/ready timing per AXI_RANDOMIZER_CONFIGS

It also drives the non-AXI stub interfaces manually:
  - Scheduler stub (q_rank/bank/row, mark_issued, beat_pull, b_complete)
  - Read-data injection (rd_inject_*) for non-forwarded reads
  - Read-beat acknowledgement (rd_beat_we/slot)

Memory model tracks the writes that have been issued so any non-forwarded
read can be auto-serviced with the expected data.
"""

import os
import sys
import logging
import random
import subprocess
from typing import Dict, List, Optional, Tuple

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer, ReadOnly


# Add repo root to sys.path so framework imports work
_repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).decode().strip()
if _repo_root not in sys.path:
    sys.path.insert(0, _repo_root)

from CocoTBFramework.components.axi4.axi4_interfaces import (  # noqa: E402
    AXI4MasterWrite, AXI4MasterRead,
)
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer  # noqa: E402
from TBClasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS  # noqa: E402


#----------------------------------------------------------------------------
# Memory model
#----------------------------------------------------------------------------

class MemModel:
    """Simple address-keyed beat-store for self-checking.

    The TB writes (addr, beats) on every AXI write; reads pull the same
    beats out for verification. Non-forwarded reads also use this to source
    the rd_inject_* data.
    """

    def __init__(self) -> None:
        self._store: Dict[int, List[int]] = {}
        # FIFO of (id, [beats]) for reads still in flight that the
        # rd_scheduler stub needs to inject.
        self._rd_inject_q: List[Tuple[int, List[int]]] = []

    def write(self, addr: int, beats: List[int]) -> None:
        self._store[addr] = list(beats)

    def expected_beats(self, addr: int, count: int) -> List[int]:
        return self._store.get(addr, [0] * count)[:count]

    def queue_inject(self, axi_id: int, beats: List[int]) -> None:
        self._rd_inject_q.append((axi_id, beats))

    def pop_inject(self) -> Optional[Tuple[int, List[int]]]:
        if self._rd_inject_q:
            return self._rd_inject_q.pop(0)
        return None


#----------------------------------------------------------------------------
# Main TB class
#----------------------------------------------------------------------------

class AxiFrontendMacroTB:
    SCHEME_ROW_MAJOR       = 0
    SCHEME_BANK_INTERLEAVE = 1
    SCHEME_XOR_HASH        = 2

    def __init__(self, dut,
                 axi_data_width: int = 64,
                 axi_id_width:   int = 4,
                 axi_addr_width: int = 32,
                 axi_user_width: int = 1) -> None:
        self.dut = dut
        self.log = logging.getLogger("axi_frontend_macro_tb")
        self.log.setLevel(logging.INFO)

        self.AXI_DATA_WIDTH = axi_data_width
        self.AXI_ID_WIDTH   = axi_id_width
        self.AXI_ADDR_WIDTH = axi_addr_width
        self.AXI_USER_WIDTH = axi_user_width
        self.AXI_STRB_WIDTH = axi_data_width // 8
        self.AXI_DATA_MASK  = (1 << axi_data_width) - 1
        self.AXI_STRB_FULL  = (1 << self.AXI_STRB_WIDTH) - 1

        # Deterministic randomness from SEED
        self.SEED = int(os.environ.get('SEED', '12345'))
        random.seed(self.SEED)

        # Self-checking memory model
        self.mem = MemModel()

        # Statistics
        self.fwd_hits_seen   = 0
        self.fwd_misses_seen = 0

        # Handshake-stall counters — (valid && !ready) cycles per channel.
        # Used by the `perfect_streaming` scenario to prove the host AXI
        # boundary never throttles under ideal drain. reset_stall_counters()
        # clears them before the workload-of-interest begins.
        self.aw_stall_cycles = 0
        self.w_stall_cycles  = 0
        self.ar_stall_cycles = 0
        self.b_stall_cycles  = 0
        self.r_stall_cycles  = 0
        # Per-channel longest contiguous (valid && !ready) run — catches a
        # multi-cycle hang even when the total budget is met.
        self.aw_stall_run_max = 0
        self.w_stall_run_max  = 0
        self.ar_stall_run_max = 0
        # Internal running-count state for the monitor.
        self._aw_stall_run = 0
        self._w_stall_run  = 0
        self._ar_stall_run = 0

        # Stub control flags. Tests can pause the auto-services to hold a
        # write in the CAM beyond its natural lifetime (needed for the
        # snarf-timing schmoo so we can place the read inside / outside
        # the snarf window deterministically).
        self.wr_stub_paused: bool = False
        self.rd_stub_paused: bool = False

        # Build AXI4 BFMs as masters (we drive the host side of the slave DUT)
        self.axi_master_wr = AXI4MasterWrite(
            dut=dut,
            clock=dut.mc_clk,
            prefix='s_axi',
            data_width=axi_data_width,
            id_width=axi_id_width,
            addr_width=axi_addr_width,
            user_width=axi_user_width,
            log=self.log,
        )

        self.axi_master_rd = AXI4MasterRead(
            dut=dut,
            clock=dut.mc_clk,
            prefix='s_axi',
            data_width=axi_data_width,
            id_width=axi_id_width,
            addr_width=axi_addr_width,
            user_width=axi_user_width,
            log=self.log,
        )

    # --------------------------------------------------------------------
    # Setup / reset
    # --------------------------------------------------------------------

    async def setup(self, period_ns: int = 5,
                    scheme: int = SCHEME_ROW_MAJOR,
                    timing_profile: str = 'backtoback') -> None:
        cocotb.start_soon(Clock(self.dut.mc_clk, period_ns, units='ns').start())

        # CSR
        self.dut.scheme_active_i.value = scheme
        self.dut.xor_seed_i.value      = 0

        # Scheduler stub signals
        self.dut.q_rank_i.value         = 0
        self.dut.q_bank_i.value         = 0
        self.dut.q_row_i.value          = 0
        self.dut.wr_issued_we_i.value   = 0
        self.dut.wr_issued_slot_i.value = 0
        self.dut.rd_issued_we_i.value   = 0
        self.dut.rd_issued_slot_i.value = 0
        self.dut.beat_pull_strb_i.value = 0
        self.dut.beat_pull_slot_i.value = 0
        self.dut.b_complete_strb_i.value = 0
        self.dut.b_complete_slot_i.value = 0
        self.dut.rd_beat_we_i.value     = 0
        self.dut.rd_beat_slot_i.value   = 0

        # Rd inject (idle by default)
        self.dut.rd_inject_valid_i.value = 0
        self.dut.rd_inject_id_i.value    = 0
        self.dut.rd_inject_data_i.value  = 0
        self.dut.rd_inject_last_i.value  = 0

        # Reset
        self.dut.mc_rst_n.value = 0
        for _ in range(10):
            await RisingEdge(self.dut.mc_clk)
        self.dut.mc_rst_n.value = 1
        for _ in range(5):
            await RisingEdge(self.dut.mc_clk)

        # AXI channel timing profile
        self.set_axi_timing_profile(timing_profile)

        # Start scheduler-stub background tasks
        cocotb.start_soon(self._wr_scheduler_stub())
        cocotb.start_soon(self._rd_scheduler_stub())
        cocotb.start_soon(self._fwd_observer())
        cocotb.start_soon(self._handshake_stall_monitor())

    def set_axi_timing_profile(self, profile_name: str) -> None:
        """Configure per-channel FlexRandomizer timing.

        For an AXI4 master-side BFM:
          - aw/w/ar channels are GAXIMaster (drive valid)  -> config['master']
          - b/r channels are GAXISlave   (drive ready)     -> config['slave']
        """
        if profile_name not in AXI_RANDOMIZER_CONFIGS:
            self.log.warning(f"unknown timing profile '{profile_name}' — using 'backtoback'")
            profile_name = 'backtoback'
        cfg = AXI_RANDOMIZER_CONFIGS[profile_name]
        # AW channel (master drives awvalid)
        self.axi_master_wr.aw_channel.randomizer = FlexRandomizer(cfg['master'])
        # W channel  (master drives wvalid)
        self.axi_master_wr.w_channel.randomizer  = FlexRandomizer(cfg['master'])
        # B channel  (slave drives bready)
        self.axi_master_wr.b_channel.randomizer  = FlexRandomizer(cfg['slave'])
        # AR channel (master drives arvalid)
        self.axi_master_rd.ar_channel.randomizer = FlexRandomizer(cfg['master'])
        # R channel  (slave drives rready)
        self.axi_master_rd.r_channel.randomizer  = FlexRandomizer(cfg['slave'])
        self.log.info(f"AXI timing profile = '{profile_name}'")

    def set_scheme(self, scheme: int) -> None:
        """Live-switch the address-map scheme (CSR-style)."""
        self.dut.scheme_active_i.value = scheme

    def stat_snapshot(self) -> Tuple[int, int]:
        """Returns (fwd_hits, fwd_misses) — useful for delta-checking around
        a scenario step."""
        return self.fwd_hits_seen, self.fwd_misses_seen

    def reset_stall_counters(self) -> None:
        """Clear the per-channel handshake-stall accumulators. Call this
        immediately before the workload-of-interest in `perfect_streaming`
        so warmup transactions don't count against the budget."""
        self.aw_stall_cycles = 0
        self.w_stall_cycles  = 0
        self.ar_stall_cycles = 0
        self.b_stall_cycles  = 0
        self.r_stall_cycles  = 0
        self.aw_stall_run_max = 0
        self.w_stall_run_max  = 0
        self.ar_stall_run_max = 0
        self._aw_stall_run = 0
        self._w_stall_run  = 0
        self._ar_stall_run = 0

    async def _handshake_stall_monitor(self) -> None:
        """Background: every clock edge, sample (valid && !ready) on each
        host AXI channel. Tracks both total stall cycles and the longest
        contiguous run per channel.

        Runs from `setup()` through end of test. Cheap (5 single-bit
        comparisons per cycle).
        """
        while True:
            await RisingEdge(self.dut.mc_clk)
            await ReadOnly()

            aw_stall = int(self.dut.s_axi_awvalid.value) and not int(self.dut.s_axi_awready.value)
            w_stall  = int(self.dut.s_axi_wvalid.value)  and not int(self.dut.s_axi_wready.value)
            ar_stall = int(self.dut.s_axi_arvalid.value) and not int(self.dut.s_axi_arready.value)
            b_stall  = int(self.dut.s_axi_bvalid.value)  and not int(self.dut.s_axi_bready.value)
            r_stall  = int(self.dut.s_axi_rvalid.value)  and not int(self.dut.s_axi_rready.value)

            if aw_stall:
                self.aw_stall_cycles += 1
                self._aw_stall_run   += 1
                if self._aw_stall_run > self.aw_stall_run_max:
                    self.aw_stall_run_max = self._aw_stall_run
            else:
                self._aw_stall_run = 0

            if w_stall:
                self.w_stall_cycles += 1
                self._w_stall_run   += 1
                if self._w_stall_run > self.w_stall_run_max:
                    self.w_stall_run_max = self._w_stall_run
            else:
                self._w_stall_run = 0

            if ar_stall:
                self.ar_stall_cycles += 1
                self._ar_stall_run   += 1
                if self._ar_stall_run > self.ar_stall_run_max:
                    self.ar_stall_run_max = self._ar_stall_run
            else:
                self._ar_stall_run = 0

            if b_stall:
                self.b_stall_cycles += 1
            if r_stall:
                self.r_stall_cycles += 1

    async def wait_for_wr_cam_push(self, prev_occ: int = 0,
                                   timeout_cycles: int = 200) -> int:
        """Wait until dbg_wr_cam_occ_o exceeds prev_occ. Used by tests to
        deterministically know the in-flight write has reached the CAM
        before issuing the matching read (otherwise the read races the
        BFM's AW+W drive and may arrive before the snarf window opens).
        Returns the observed occupancy."""
        for _ in range(timeout_cycles):
            await RisingEdge(self.dut.mc_clk)
            await ReadOnly()
            occ = int(self.dut.dbg_wr_cam_occ_o.value)
            if occ > prev_occ:
                return occ
        raise TimeoutError(
            f"wait_for_wr_cam_push: occupancy did not exceed {prev_occ} "
            f"within {timeout_cycles} cycles"
        )

    # --------------------------------------------------------------------
    # Test API — high-level write/read using the BFMs
    # --------------------------------------------------------------------

    async def axi_write(self, address: int, beats: List[int],
                        axi_id: int = 0, strb: Optional[int] = None) -> None:
        """Issue an AXI write burst via the master BFM and wait for B.
        Records the burst into the memory model for later verification.
        """
        if strb is None:
            strb = self.AXI_STRB_FULL
        self.mem.write(address, beats)
        size = (self.AXI_DATA_WIDTH // 8).bit_length() - 1  # log2(bytes)
        await self.axi_master_wr.write_transaction(
            address=address,
            data=beats,
            burst_len=len(beats),
            id=axi_id,
            size=size,
            burst_type=1,   # INCR
            strb=strb,
        )

    async def axi_read(self, address: int, beats: int,
                       axi_id: int = 0) -> List[int]:
        """Issue an AXI read burst via the master BFM and return the beats.

        If the read does not snarf, the rd-scheduler stub will inject the
        expected data from the memory model so the transaction completes.
        """
        # Pre-queue inject data in case this becomes a miss
        expected = self.mem.expected_beats(address, beats)
        self.mem.queue_inject(axi_id, expected)
        size = (self.AXI_DATA_WIDTH // 8).bit_length() - 1
        data = await self.axi_master_rd.read_transaction(
            address=address,
            burst_len=beats,
            id=axi_id,
            size=size,
            burst_type=1,
        )
        return list(data)

    # --------------------------------------------------------------------
    # Stubs — background tasks that emulate the FUBs outside this macro
    # --------------------------------------------------------------------

    async def _wr_scheduler_stub(self) -> None:
        """Auto-services the wr_cmd_cam.

        v1 simplification: assumes single-write-in-flight (always slot 0).
        For each new occupancy: mark issued, beat-pull until last, b_complete.

        Honors tb.wr_stub_paused — when True, the stub idles without
        servicing, keeping any pushed AW in the CAM. Tests use this to
        deterministically place a read inside or outside the snarf window.
        """
        prev_occ = 0
        while True:
            await RisingEdge(self.dut.mc_clk)
            if self.wr_stub_paused:
                continue
            await ReadOnly()
            occ = int(self.dut.dbg_wr_cam_occ_o.value)
            if occ <= prev_occ:
                prev_occ = occ
                continue
            prev_occ = occ
            slot = 0
            await RisingEdge(self.dut.mc_clk)

            # Mark issued
            self.dut.wr_issued_we_i.value   = 1
            self.dut.wr_issued_slot_i.value = slot
            await RisingEdge(self.dut.mc_clk)
            self.dut.wr_issued_we_i.value   = 0

            # Pull beats until last
            self.dut.beat_pull_slot_i.value = slot
            self.dut.beat_pull_strb_i.value = 1
            while True:
                await ReadOnly()
                last = int(self.dut.beat_pull_last_o.value)
                await RisingEdge(self.dut.mc_clk)
                if last:
                    break
            self.dut.beat_pull_strb_i.value = 0
            await RisingEdge(self.dut.mc_clk)

            # b_complete
            self.dut.b_complete_strb_i.value = 1
            self.dut.b_complete_slot_i.value = slot
            await RisingEdge(self.dut.mc_clk)
            self.dut.b_complete_strb_i.value = 0
            prev_occ = 0   # reopen for the next write

    async def _rd_scheduler_stub(self) -> None:
        """Auto-services rd_cmd_cam entries that didn't snarf.

        When dbg_rd_cam_occ_o rises (a miss-path read pushed) it dequeues
        the next queued inject from the memory model and drives the R data.

        v1 simplification: serial — one rd burst at a time.
        """
        prev_occ = 0
        while True:
            await RisingEdge(self.dut.mc_clk)
            await ReadOnly()
            occ = int(self.dut.dbg_rd_cam_occ_o.value)
            if occ <= prev_occ:
                prev_occ = occ
                continue
            prev_occ = occ

            # A new rd-CAM entry exists. Get its inject data.
            inject = self.mem.pop_inject()
            if inject is None:
                self.log.warning("rd_scheduler_stub: rd CAM occupied but no inject queued")
                continue
            axi_id, beats = inject
            slot = 0
            await RisingEdge(self.dut.mc_clk)

            # Mark issued
            self.dut.rd_issued_we_i.value   = 1
            self.dut.rd_issued_slot_i.value = slot
            await RisingEdge(self.dut.mc_clk)
            self.dut.rd_issued_we_i.value   = 0

            # Stream rd_inject_* beats
            for i, beat in enumerate(beats):
                self.dut.rd_inject_valid_i.value = 1
                self.dut.rd_inject_id_i.value    = axi_id
                self.dut.rd_inject_data_i.value  = beat
                self.dut.rd_inject_last_i.value  = 1 if i == len(beats) - 1 else 0
                await ReadOnly()
                while int(self.dut.rd_inject_ready_o.value) == 0:
                    await RisingEdge(self.dut.mc_clk)
                    await ReadOnly()
                await RisingEdge(self.dut.mc_clk)
            self.dut.rd_inject_valid_i.value = 0
            self.dut.rd_inject_last_i.value  = 0

            # Tell rd_cmd_cam each beat was emitted to AXI R
            for _ in range(len(beats)):
                self.dut.rd_beat_we_i.value   = 1
                self.dut.rd_beat_slot_i.value = slot
                await RisingEdge(self.dut.mc_clk)
            self.dut.rd_beat_we_i.value = 0
            prev_occ = 0

    async def _fwd_observer(self) -> None:
        """Counts dbg_forward_hit / dbg_forward_miss pulses, and reclaims
        the queued inject when a hit fires (the snarf'd read won't need
        the rd-stub to drive its data, so leaving stale inject in the
        queue would corrupt the NEXT miss-path read)."""
        while True:
            await RisingEdge(self.dut.mc_clk)
            await ReadOnly()
            if int(self.dut.dbg_forward_hit_o.value) == 1:
                self.fwd_hits_seen += 1
                # Pop the inject that axi_read() pre-queued — it won't be needed
                self.mem.pop_inject()
            if int(self.dut.dbg_forward_miss_o.value) == 1:
                self.fwd_misses_seen += 1
                # On miss the rd-stub will pop the inject when it
                # services the rd_cam entry.
