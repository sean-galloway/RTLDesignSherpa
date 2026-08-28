# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: PumiceAxiBfm
# Purpose: The one place pumice DV drives its AXI4 slave port. Wraps the
#          framework master BFMs so no test ever hand-pokes s_axi_*.

"""Shared AXI4 master driving for every pumice DUT that exposes `s_axi_*`.

Exists because of a HARD RULE (PUMICE-014): no environment may hand-poke a
standard or valid/ready interface. Hand-rolled `dut.s_axi_awvalid = 1`
helpers skip the BFM's protocol timing -- valid/ready randomization,
per-channel profiles, outstanding and interleaved bursts -- so they miss
protocol and timing bugs, and they poison every performance measurement:
a hand-rolled driver starves the DUT, so the numbers grade the testbench.

It is a shared module rather than a copied block because four test files
need it (core_dfi, core, top_csr, top/top_geared) and a copied driver
drifts. When it drifted, the failure was silent -- see the engine-runner
note below, which took three wrong fixes to find.

## Timing profiles

Profiles come from the repo-wide `TBClasses.amba.amba_random_configs`
(`AXI_RANDOMIZER_CONFIGS`) -- the common valid/ready timing source for all
protocols, with `master` (valid_delay) and `slave` (ready_delay) sub-keys.
Never write manual gaps. For any perf measurement use `backtoback`.

## Which runner: this is the part that bites

`run_axi4_sequence` walks bursts SERIALLY -- it takes a per-instance AW+W
lock and awaits each B response before the next burst, ~34.5 cycles/burst
measured on pumice's core. Building one big `AXI4Sequence` does NOT change
that; the sequence is a work list, not a pipeline.

`run_axi4_sequence_engine` is the queue-and-go runner: all AWs queued
back-to-back, B responses collected at the end (~5.5 cycles/burst here).

The difference is not only throughput. pumice's scheduler derives
`demand_i` from command-CAM occupancy, so the serial runner left the CAM
EMPTY between bursts, the gaps outran the refresh idle-confirm hysteresis,
and refreshes fired inside a window a test asserted was refresh-free.
So: `write_many`/`read_many` use the engine runner; the single-burst
`write`/`read` use the plain one (they must block through B/R anyway).
"""

from __future__ import annotations

import os
from typing import Callable, Dict, Iterable, List, Optional, Sequence, Tuple

from CocoTBFramework.components.axi4.axi4_interfaces import (AXI4MasterRead,
                                                             AXI4MasterWrite)
from CocoTBFramework.components.axi4.axi4_sequence import (
    AXI4Sequence, run_axi4_sequence, run_axi4_sequence_engine)
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from TBClasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS

DEFAULT_PROFILE = "backtoback"


class PumiceAxiBfm:
    """AXI4 write+read masters on one `s_axi_*` port.

        bfm = PumiceAxiBfm(dut, data_width=128, bl_words=4)
        await bfm.write(addr, beats)
        beats = await bfm.read(addr)
        await bfm.write_many([(addr, beats), ...])      # engine runner

    The default profile is `backtoback` (zero inter-beat delay) and can be
    overridden per run with the AXI_PROFILE env var, or per channel with
    `set_profile`.
    """

    def __init__(self, dut, *, data_width: int, bl_words: int,
                 id_width: int = 8, addr_width: int = 32,
                 prefix: str = "s_axi", clock=None,
                 profile: Optional[str] = None, log=None,
                 write: bool = True, read: bool = True):
        """`write`/`read` select which masters to build. A DUT with only a
        write intake has no AR/R ports, and constructing a read master
        against absent signals fails at bind time -- so build only what the
        port actually has."""
        self.dut = dut
        self.dw = data_width
        self.bl_words = bl_words
        self.log = log if log is not None else dut._log
        clk = clock if clock is not None else dut.aclk
        self.wr = (AXI4MasterWrite(dut, clk, prefix=prefix, data_width=data_width,
                                   id_width=id_width, addr_width=addr_width,
                                   log=self.log) if write else None)
        self.rd = (AXI4MasterRead(dut, clk, prefix=prefix, data_width=data_width,
                                  id_width=id_width, addr_width=addr_width,
                                  log=self.log) if read else None)
        self.set_profile(profile or os.environ.get("AXI_PROFILE",
                                                   DEFAULT_PROFILE))

    # ---------------- timing ----------------

    def set_profile(self, profile: str, *,
                    channels: Optional[Iterable[str]] = None) -> None:
        """Apply an AXI_RANDOMIZER_CONFIGS profile.

        `channels` limits which of aw/w/ar/b/r are retimed -- use it to give
        one channel different pacing, e.g. consumer-side backpressure on R
        while the request channels stay back-to-back.
        """
        cfg = AXI_RANDOMIZER_CONFIGS[profile]
        # master = valid_delay (we drive), slave = ready_delay (we consume)
        targets = {}
        if self.wr is not None:
            targets.update({'aw': (self.wr.aw_channel, "master"),
                            'w':  (self.wr.w_channel,  "master"),
                            'b':  (self.wr.b_channel,  "slave")})
        if self.rd is not None:
            targets.update({'ar': (self.rd.ar_channel, "master"),
                            'r':  (self.rd.r_channel,  "slave")})
        for name in (channels if channels is not None else targets):
            if name not in targets:      # channel not built on this port
                continue
            chan, side = targets[name]
            chan.randomizer = FlexRandomizer(cfg[side])

    # ---------------- running ----------------

    async def run(self, seq: AXI4Sequence, *, engine: bool = False) -> List[Dict]:
        runner = run_axi4_sequence_engine if engine else run_axi4_sequence
        return await runner(seq, master_wr=self.wr, master_rd=self.rd,
                            log=self.log)

    async def write(self, addr: int, data: Sequence[int], wid: int = 0) -> None:
        """One write burst; blocks through its B response."""
        seq = AXI4Sequence("w1", data_width=self.dw)
        seq.add_write(addr, list(data), axid=wid & 0xF)
        await self.run(seq)

    async def read(self, addr: int, rid: int = 0,
                   length: Optional[int] = None) -> List[int]:
        """One read burst; returns its beat list."""
        seq = AXI4Sequence("r1", data_width=self.dw)
        seq.add_read(addr, length=length or self.bl_words, axid=rid & 0xF)
        res = await self.run(seq)
        return list(res[0]["data"]) if res else []

    async def write_many(self, reqs: Sequence[Tuple[int, Sequence[int]]],
                         axid_fn: Callable[[int], int] = lambda k: k & 0xF
                         ) -> None:
        """Multi-burst write via the ENGINE runner, so AWs queue
        back-to-back and the DUT's command CAM stays occupied."""
        seq = AXI4Sequence("wN", data_width=self.dw)
        for k, (addr, data) in enumerate(reqs):
            seq.add_write(addr, list(data), axid=axid_fn(k))
        await self.run(seq, engine=True)

    async def read_many(self, addrs: Sequence[int],
                        axid_fn: Callable[[int], int] = lambda k: k & 0xF,
                        length: Optional[int] = None
                        ) -> List[Tuple[int, List[int]]]:
        """Multi-burst read via the ENGINE runner; [(addr, beats), ...]."""
        seq = AXI4Sequence("rN", data_width=self.dw)
        for k, a in enumerate(addrs):
            seq.add_read(a, length=length or self.bl_words, axid=axid_fn(k))
        res = await self.run(seq, engine=True)
        return [(d["addr"], list(d["data"])) for d in res]
