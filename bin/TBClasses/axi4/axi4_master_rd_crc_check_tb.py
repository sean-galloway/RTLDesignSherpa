# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: axi4_master_rd_crc_check_tb
# Purpose: Direct FUB TB for axi4_master_rd_crc_check. Drives the cfg
#          interface and acts as a minimal AXI4 read slave on the M side.

"""TB for `axi4_master_rd_crc_check`.

Terminates the M-side AXI with the framework's ``AXI4SlaveRead`` BFM
backed by a shared ``MemoryModel``:
  * BFM drives ``arready`` per ``slave_profile`` (default ``backtoback``
    = 0 ready_delay).
  * On each AR, the BFM walks consecutive beats out of ``MemoryModel``
    starting at the AR's base addr, packing them into R beats with the
    AR's id, plus ``rresp_override`` for non-OKAY-resp scenarios.
  * The TB preloads MemoryModel with the LFSR pattern (or constant
    garbage) the reader expects to see; ``return_lfsr_data=True``
    preload-fills, ``return_lfsr_data=False`` writes the same
    ``garbage_word`` everywhere — preserves the legacy scenario knobs.

ar_log is populated from the BFM's AR channel callback so existing
scenario assertions keep working unchanged.

The Python LFSR mirror delegates to the canonical
``TBClasses.common.lfsr_mirror.simulate_xor_lfsr`` to stay in sync with
the writer engine TB and the LFSR unit-test TB — no per-TB drift.
"""

from __future__ import annotations

import logging
import os
from dataclasses import dataclass
from typing import Deque, List, Optional
from collections import deque

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer

from TBClasses.shared.tbbase import TBBase
from TBClasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS
from TBClasses.common.lfsr_mirror import simulate_xor_lfsr as _shared_lfsr
from TBClasses.axi4.axi4_master_wr_pattern_gen_tb import (
    WrPatternGenTB as _LfsrMirror,
)

from CocoTBFramework.components.axi4.axi4_interfaces import AXI4SlaveRead
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.shared.memory_model import MemoryModel


_NBA_SETTLE_PS = 100


@dataclass
class CapturedAr:
    addr: int
    axid: int
    arlen: int  # len-1 per AXI4


class _Axi4SlaveReadWithRrespOverride(AXI4SlaveRead):
    """AXI4SlaveRead that lets the test inject a non-OKAY rresp.

    Mirrors the WR-side wrapper: ``self.rresp_override`` is spliced
    into every R packet by intercepting ``r_channel.create_packet``."""

    def __init__(self, *args, **kwargs) -> None:
        super().__init__(*args, **kwargs)
        self.rresp_override: int = 0
        _orig_create = self.r_channel.create_packet
        outer = self

        def _wrapped(**kw):
            pkt = _orig_create(**kw)
            pkt.resp = outer.rresp_override
            return pkt
        self.r_channel.create_packet = _wrapped


class RdCrcCheckTB(TBBase):
    CLK = 10
    LFSR_DEFAULT_SEED = _LfsrMirror.LFSR_DEFAULT_SEED
    LFSR_TAPS         = _LfsrMirror.LFSR_TAPS
    DEFAULT_MEM_BYTES = 64 * 1024   # 64 KiB — covers kb32 (32 KiB) headroom

    def __init__(self, dut, *, mem_bytes: int = DEFAULT_MEM_BYTES) -> None:
        super().__init__(dut)
        self.dut = dut
        self.log = logging.getLogger("rd_crc_check_tb")
        self.log.setLevel(logging.INFO)

        self.AXI_DATA_WIDTH = self.convert_to_int(
            os.environ.get("AXI_DATA_WIDTH", "64"))
        self.AXI_ID_WIDTH = self.convert_to_int(
            os.environ.get("AXI_ID_WIDTH", "8"))
        self.LFSR_WIDTH = 32
        self.MASK_LFSR = (1 << self.LFSR_WIDTH) - 1
        self.MASK_DATA = (1 << self.AXI_DATA_WIDTH) - 1
        self.BYTES_PER_BEAT = self.AXI_DATA_WIDTH // 8

        # Slave-side responder behavior knobs (test overrides per scenario)
        self.return_lfsr_data: bool = True   # True: preload LFSR; False: preload garbage
        self.garbage_word: int = 0xBADCAFE_DEADBEEF
        self.lfsr_seed: int = self.LFSR_DEFAULT_SEED

        # Hash-mode mirror state (set by program()). When data_mode=1 the
        # preload uses hash_beat_data instead of LFSR_advance.
        self.data_mode: int = 0
        self.hash_seeds: tuple = (0, 0, 0)
        # Preload geometry — saved on program() so we know what range to
        # fill once pulse_start() is called.
        self._preload_start_addr: int = 0
        self._preload_stride: int = 0
        self._preload_burst_len: int = 1
        self._preload_txn_count: int = 0

        self.ar_log: List[CapturedAr] = []

        self._mem_bytes = mem_bytes
        self.memory = MemoryModel(
            num_lines=mem_bytes // self.BYTES_PER_BEAT,
            bytes_per_line=self.BYTES_PER_BEAT,
            log=self.log,
        )
        self.slave: Optional[_Axi4SlaveReadWithRrespOverride] = None

    # ---- rresp override convenience ----

    @property
    def rresp_override(self) -> int:
        return self.slave.rresp_override if self.slave else 0

    @rresp_override.setter
    def rresp_override(self, v: int) -> None:
        if self.slave is None:
            raise RuntimeError("rresp_override set before setup_clocks_and_reset()")
        self.slave.rresp_override = int(v) & 0x3

    # ---- setup ----

    async def setup_clocks_and_reset(self):
        cocotb.start_soon(Clock(self.dut.aclk, self.CLK, units="ns").start())
        self._drive_idle_cfg()
        self.dut.aresetn.value = 0
        for _ in range(10):
            await RisingEdge(self.dut.aclk)
        self.dut.aresetn.value = 1
        for _ in range(5):
            await RisingEdge(self.dut.aclk)
        self.slave = _Axi4SlaveReadWithRrespOverride(
            dut=self.dut, clock=self.dut.aclk,
            prefix="m_axi_",
            data_width=self.AXI_DATA_WIDTH,
            id_width=self.AXI_ID_WIDTH,
            addr_width=32,
            user_width=1,
            multi_sig=True,
            memory_model=self.memory,
            log=self.log,
        )
        self.set_slave_delay_profile("backtoback")

        def _ar_cb(pkt) -> None:
            self.ar_log.append(CapturedAr(
                addr  = int(getattr(pkt, "addr", 0)),
                axid  = int(getattr(pkt, "id", 0)),
                arlen = int(getattr(pkt, "len", 0)),
            ))

        self.slave.ar_channel.add_callback(_ar_cb)

    def _drive_idle_cfg(self) -> None:
        self.dut.cfg_start_addr.value       = 0
        self.dut.cfg_addr_stride_0.value    = 0
        self.dut.cfg_addr_stride_1.value    = 0
        self.dut.cfg_addr_wrap_mask_0.value = 0
        self.dut.cfg_addr_wrap_mask_1.value = 0
        self.dut.cfg_burst_len.value        = 1
        self.dut.cfg_txn_count.value        = 0
        self.dut.cfg_axi_id.value           = 0
        self.dut.cfg_id_mode.value          = 0
        self.dut.cfg_axi_size.value         = 3
        self.dut.cfg_axi_burst.value        = 1
        self.dut.cfg_lfsr_seed.value        = 0
        self.dut.cfg_data_mode.value        = 0
        self.dut.cfg_hash_seed0.value       = 0
        self.dut.cfg_hash_seed1.value       = 0
        self.dut.cfg_hash_seed2.value       = 0
        self.dut.cfg_rd_gap.value           = 0
        self.dut.cfg_start.value            = 0
        # Debug FIFO drain idle (DBG_FIFO_DEPTH default=0 → ports tied
        # off internally; the per-engine FUB tests don't enable it).
        self.dut.dbg_ready.value            = 0

    def set_slave_delay_profile(self, profile: str) -> None:
        """Apply ``profile`` (from ``AXI_RANDOMIZER_CONFIGS``) to the
        slave's AR/R channel randomizers. Use ``backtoback`` for 0-delay."""
        if profile not in AXI_RANDOMIZER_CONFIGS:
            raise ValueError(
                f"unknown profile {profile!r}; valid: "
                f"{sorted(AXI_RANDOMIZER_CONFIGS.keys())}"
            )
        cfg = AXI_RANDOMIZER_CONFIGS[profile]
        slave_constraints = cfg["slave"]
        master_constraints = cfg["master"]
        self.slave.ar_channel.set_randomizer(FlexRandomizer(slave_constraints))
        self.slave.r_channel.set_randomizer(FlexRandomizer(master_constraints))

    # ---- preload helpers ----

    def _replicate(self, lfsr_word: int) -> int:
        rep = (self.AXI_DATA_WIDTH + 31) // 32
        out = 0
        w = lfsr_word & 0xFFFFFFFF
        for k in range(rep):
            out |= w << (k * 32)
        return out & self.MASK_DATA

    def _preload_memory(self) -> None:
        """Fill MemoryModel with the data the reader will compare
        against. Called from pulse_start() after the seed is locked.
        Lays out one beat per (start_addr + k*BPP) for the entire
        workload range — this is what an idealized writer would have
        deposited before the read phase.
        """
        if self._preload_txn_count == 0:
            return
        total_beats = self._preload_txn_count * self._preload_burst_len
        bpp = self.BYTES_PER_BEAT

        if self.data_mode == 1:
            # Hash mode: data per byte addr (engine reader hashes
            # araddr+k*bpp; mirror at the same bpp granularity).
            base = self._preload_start_addr
            for bi in range(self._preload_txn_count):
                for k in range(self._preload_burst_len):
                    byte_addr = base + bi * self._preload_stride + k * bpp
                    data = _LfsrMirror.expected_hash_beat_data(
                        self, byte_addr & 0xFFFFFFFF, self.hash_seeds)
                    self.memory.write(byte_addr,
                                      self.memory.integer_to_bytearray(
                                          data, bpp))
        else:
            # LFSR mode: phases 0..total_beats-1 starting from seed.
            lfsr_seq = _shared_lfsr(
                seed=self.lfsr_seed,
                taps=self.LFSR_TAPS,
                cycles=total_beats - 1,
                width=self.LFSR_WIDTH,
                include_seed=True,
            )
            payload = [self._replicate(w) if self.return_lfsr_data
                       else (self.garbage_word & self.MASK_DATA)
                       for w in lfsr_seq]
            base = self._preload_start_addr
            idx = 0
            for bi in range(self._preload_txn_count):
                for k in range(self._preload_burst_len):
                    byte_addr = base + bi * self._preload_stride + k * bpp
                    self.memory.write(byte_addr,
                                      self.memory.integer_to_bytearray(
                                          payload[idx], bpp))
                    idx += 1

    # ---- cfg drive helpers ----

    async def program(self, *, start_addr: int, stride_0: int = 0,
                      stride_1: int = 0, wrap_mask_0: int = 0,
                      wrap_mask_1: int = 0, burst_len: int = 1,
                      txn_count: int = 1, axi_id: int = 0,
                      axi_size: int = 3, axi_burst: int = 1,
                      lfsr_seed: int = 0, rd_gap: int = 0,
                      data_mode: int = 0,
                      hash_seed0: int = 0,
                      hash_seed1: int = 0,
                      hash_seed2: int = 0,
                      id_mode: int = 0) -> None:
        self.dut.cfg_start_addr.value       = start_addr
        self.dut.cfg_addr_stride_0.value    = stride_0
        self.dut.cfg_addr_stride_1.value    = stride_1
        self.dut.cfg_addr_wrap_mask_0.value = wrap_mask_0
        self.dut.cfg_addr_wrap_mask_1.value = wrap_mask_1
        self.dut.cfg_burst_len.value        = burst_len
        self.dut.cfg_txn_count.value        = txn_count
        self.dut.cfg_axi_id.value           = axi_id
        self.dut.cfg_id_mode.value          = id_mode & 0x3
        self.dut.cfg_axi_size.value         = axi_size
        self.dut.cfg_axi_burst.value        = axi_burst
        self.dut.cfg_lfsr_seed.value        = lfsr_seed
        self.dut.cfg_data_mode.value        = data_mode & 0x1
        self.dut.cfg_hash_seed0.value       = hash_seed0 & 0xFFFFFFFF
        self.dut.cfg_hash_seed1.value       = hash_seed1 & 0xFFFFFFFF
        self.dut.cfg_hash_seed2.value       = hash_seed2 & 0xFFFFFFFF
        self.dut.cfg_rd_gap.value           = rd_gap & 0xF
        # Mirror the DUT's seed selection so the preloaded MemoryModel
        # contents phase-lock with what the reader engine expects.
        self.lfsr_seed = (lfsr_seed if lfsr_seed != 0
                          else self.LFSR_DEFAULT_SEED)
        self.data_mode   = data_mode & 0x1
        self.hash_seeds  = (hash_seed0 & 0xFFFFFFFF,
                            hash_seed1 & 0xFFFFFFFF,
                            hash_seed2 & 0xFFFFFFFF)
        # Save the geometry so pulse_start() can preload memory.
        # stride_0 is the per-burst byte stride (engine semantics).
        self._preload_start_addr = start_addr
        self._preload_stride     = stride_0 if stride_0 else burst_len * self.BYTES_PER_BEAT
        self._preload_burst_len  = burst_len
        self._preload_txn_count  = txn_count
        await RisingEdge(self.dut.aclk)
        await Timer(_NBA_SETTLE_PS, units="ps")

    async def pulse_start(self) -> None:
        # Preload MemoryModel with the data the reader expects BEFORE
        # firing the engine. Old hand-rolled stub generated R-data on
        # the fly via an LFSR mirror; the BFM pulls from MemoryModel,
        # so the same data has to live there ahead of time.
        self._preload_memory()
        self.dut.cfg_start.value = 1
        await RisingEdge(self.dut.aclk)
        await Timer(_NBA_SETTLE_PS, units="ps")
        self.dut.cfg_start.value = 0
        await RisingEdge(self.dut.aclk)

    async def wait_done(self, timeout_cycles: int = 200_000) -> None:
        for _ in range(timeout_cycles):
            await RisingEdge(self.dut.aclk)
            await Timer(_NBA_SETTLE_PS, units="ps")
            if int(self.dut.cfg_done.value):
                return
        raise TimeoutError(
            f"cfg_done did not assert within {timeout_cycles} cycles"
        )
