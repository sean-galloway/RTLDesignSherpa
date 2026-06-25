# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: axi_intake_tb
# Purpose: Direct FUB TB for axi_intake — uses the AXI4Master BFMs to
#          drive the host side and minimal stubs to ack/respond on the
#          downstream side (the CAM-push and B/R completion ports).

"""TB for `axi_intake`.

The FUB is the AXI4 slave protocol engine for the controller. It has
83 ports across host AXI4, downstream CAM push, write/read completion,
forwarded R, injected R, external W-buf read, and obs. Macro tests
exercise it but don't pin its boundaries — these scenarios drive the
host side with the real `AXI4MasterWrite` / `AXI4MasterRead` BFMs and
verify the four contracts most likely to silently break the consumer:

  1. **W buffer correctness** — W beats land in `r_w_buf` at the
     `aw_push_w_buf_ptr_o` start pointer; `wbuf_ext_rd_data_o` returns
     each beat verbatim. Any byte-lane shuffle would corrupt every
     forwarded read.
  2. **B-channel BUSER + BID echo** — on `wr_entry_complete_strb_i`,
     the B-channel response carries the AWUSER captured at AW time
     and the matching BID. Pinned with two distinct (id, user) pairs.
  3. **R-channel routing precedence** — `fwd_valid_i` and
     `rd_inject_valid_i` cannot both drive `s_axi_rvalid` in the same
     beat; the forward path takes priority while `r_r_fwd_active`.
  4. **rd_inject end-to-end** — for a non-forwarded AR, the
     injected beats reach the master with correct id + last + data.
"""

from __future__ import annotations

import logging
import os
from dataclasses import dataclass
from typing import Deque, List, Optional, Tuple
from collections import deque

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.axi4.axi4_interfaces import (
    AXI4MasterWrite, AXI4MasterRead,
)


@dataclass
class PushedAw:
    push_id:    int
    w_buf_ptr:  int
    strb_ptr:   int
    length:     int
    full_strb:  bool
    qos:        int


@dataclass
class PushedAr:
    push_id:   int
    addr:      int
    length:    int
    qos:       int


class AxiIntakeTB(TBBase):
    CLK = 10

    def __init__(self, dut) -> None:
        super().__init__(dut)
        self.dut = dut
        self.log = logging.getLogger("axi_intake_tb")
        self.log.setLevel(logging.INFO)
        self.AXI_ID_WIDTH    = self.convert_to_int(
            os.environ.get("AXI_ID_WIDTH",   "4"))
        self.AXI_USER_WIDTH  = self.convert_to_int(
            os.environ.get("AXI_USER_WIDTH", "8"))
        self.AXI_DATA_WIDTH  = self.convert_to_int(
            os.environ.get("AXI_DATA_WIDTH", "64"))
        self.AXI_ADDR_WIDTH  = self.convert_to_int(
            os.environ.get("AXI_ADDR_WIDTH", "32"))
        self.SEED = self.convert_to_int(os.environ.get("SEED", "1"))

        # AXI4 BFMs
        self.axi_master_wr = AXI4MasterWrite(
            dut=dut, clock=dut.aclk, prefix='s_axi',
            data_width=self.AXI_DATA_WIDTH,
            id_width=self.AXI_ID_WIDTH,
            addr_width=self.AXI_ADDR_WIDTH,
            user_width=self.AXI_USER_WIDTH,
            log=self.log,
        )
        self.axi_master_rd = AXI4MasterRead(
            dut=dut, clock=dut.aclk, prefix='s_axi',
            data_width=self.AXI_DATA_WIDTH,
            id_width=self.AXI_ID_WIDTH,
            addr_width=self.AXI_ADDR_WIDTH,
            user_width=self.AXI_USER_WIDTH,
            log=self.log,
        )

        # Downstream stubs — captured aw/ar push entries, FIFO order
        self.aw_pushes: Deque[PushedAw] = deque()
        self.ar_pushes: Deque[PushedAr] = deque()
        # Per-AR injection queue: (id, [beats])
        self._inject_q: Deque[Tuple[int, List[int]]] = deque()

    def queue_inject(self, axi_id: int, beats: List[int]) -> None:
        self._inject_q.append((axi_id, beats))

    # ---- setup ----

    def _drive_idle(self) -> None:
        # CAM-push ack ports — always ready in this TB
        self.dut.aw_push_ready_i.value = 1
        self.dut.ar_push_ready_i.value = 1
        # Completion strobes idle
        self.dut.wr_entry_complete_strb_i.value = 0
        self.dut.wr_entry_complete_id_i.value   = 0
        self.dut.rd_entry_complete_strb_i.value = 0
        self.dut.rd_entry_complete_id_i.value   = 0
        # Forward + inject inactive
        self.dut.fwd_valid_i.value     = 0
        self.dut.fwd_id_i.value        = 0
        self.dut.fwd_w_buf_ptr_i.value = 0
        self.dut.fwd_len_i.value       = 0
        self.dut.rd_inject_valid_i.value = 0
        self.dut.rd_inject_id_i.value    = 0
        self.dut.rd_inject_data_i.value  = 0
        self.dut.rd_inject_last_i.value  = 0
        # Wbuf external read idle
        self.dut.wbuf_ext_rd_ptr_i.value = 0

    async def setup_clocks_and_reset(self):
        cocotb.start_soon(Clock(self.dut.aclk, self.CLK, units="ns").start())
        self._drive_idle()
        self.dut.aresetn.value = 0
        for _ in range(10):
            await RisingEdge(self.dut.aclk)
        self.dut.aresetn.value = 1
        for _ in range(5):
            await RisingEdge(self.dut.aclk)
        # Background stubs
        cocotb.start_soon(self._aw_push_capture())
        cocotb.start_soon(self._ar_push_capture())
        cocotb.start_soon(self._rd_inject_pump())

    # ---- background stubs ----

    async def _aw_push_capture(self) -> None:
        """Capture every aw_push handshake into self.aw_pushes."""
        while True:
            await RisingEdge(self.dut.aclk)
            try:
                v = int(self.dut.aw_push_valid_o.value)
                r = int(self.dut.aw_push_ready_i.value)
            except Exception:
                return
            if v and r:
                self.aw_pushes.append(PushedAw(
                    push_id   = int(self.dut.aw_push_id_o.value),
                    w_buf_ptr = int(self.dut.aw_push_w_buf_ptr_o.value),
                    strb_ptr  = int(self.dut.aw_push_strb_ptr_o.value),
                    length    = int(self.dut.aw_push_len_o.value),
                    full_strb = bool(int(self.dut.aw_push_full_strb_o.value)),
                    qos       = int(self.dut.aw_push_qos_o.value),
                ))

    async def _ar_push_capture(self) -> None:
        while True:
            await RisingEdge(self.dut.aclk)
            try:
                v = int(self.dut.ar_push_valid_o.value)
                r = int(self.dut.ar_push_ready_i.value)
            except Exception:
                return
            if v and r:
                self.ar_pushes.append(PushedAr(
                    push_id = int(self.dut.ar_push_id_o.value),
                    addr    = int(self.dut.ar_push_addr_o.value),
                    length  = int(self.dut.ar_push_len_o.value),
                    qos     = int(self.dut.ar_push_qos_o.value),
                ))

    async def _rd_inject_pump(self) -> None:
        """When an AR has been pushed AND no fwd is active, dequeue an
        inject and stream beats with the same id."""
        while True:
            await RisingEdge(self.dut.aclk)
            if not self._inject_q:
                continue
            # Wait until AR push captured (so id is known) and no fwd
            if not self.ar_pushes:
                continue
            if int(self.dut.fwd_valid_i.value) == 1:
                continue
            axi_id, beats = self._inject_q.popleft()
            for i, beat in enumerate(beats):
                self.dut.rd_inject_valid_i.value = 1
                self.dut.rd_inject_id_i.value    = axi_id
                self.dut.rd_inject_data_i.value  = beat
                self.dut.rd_inject_last_i.value  = 1 if i == len(beats) - 1 else 0
                # Wait for handshake
                while True:
                    await RisingEdge(self.dut.aclk)
                    if int(self.dut.rd_inject_ready_o.value) == 1:
                        break
            self.dut.rd_inject_valid_i.value = 0
            self.dut.rd_inject_last_i.value  = 0

    # ---- explicit drives the tests use ----

    async def fire_wr_entry_complete(self, axi_id: int) -> None:
        """Drive the wr_entry_complete strobe for `axi_id` so axi_intake
        emits the B-channel response."""
        await RisingEdge(self.dut.aclk)
        self.dut.wr_entry_complete_strb_i.value = 1
        self.dut.wr_entry_complete_id_i.value   = axi_id
        await RisingEdge(self.dut.aclk)
        self.dut.wr_entry_complete_strb_i.value = 0

    async def read_wbuf(self, w_buf_ptr: int) -> int:
        self.dut.wbuf_ext_rd_ptr_i.value = w_buf_ptr
        await Timer(100, units="ps")
        return int(self.dut.wbuf_ext_rd_data_o.value)
