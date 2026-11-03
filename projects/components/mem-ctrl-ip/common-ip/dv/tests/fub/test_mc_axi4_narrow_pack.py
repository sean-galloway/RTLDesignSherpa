# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""
FUB test: mc_axi4_narrow_pack (common-ip) -- narrow-transfer support at the
memory controller's host edge (granite TASK-007).

The controller below this block is full-width only. The block rewrites a
narrow INCR burst (AxSIZE below the bus) into the full-width INCR burst over
the same words, packs narrow W beats into their word by strobe, and replays
each returned word once per narrow beat that falls in it. Full-width bursts,
and narrow FIXED / WRAP, pass through unchanged.

Bench: an AXI4 master BFM on the host side (fub_*) issues bursts of every
legal AxSIZE, random AxLEN and random (including size-unaligned) start
addresses; an AXI4 slave BFM with a byte memory on the controller side (m_*)
answers them. A Python byte image mirrors every write by the AXI A3.4.1 lane
rules, and every read beat is checked against it on the beat's strobed lanes.

Checks:
  * data: every read byte equals the image (end-to-end through the block);
  * command rewrite: every downstream AW / AR is the expected rewrite of its
    upstream command, computed here independently -- a narrow INCR leaves at
    full size, the word-aligned address and AxLEN = words spanned - 1;
    anything else leaves unchanged;
  * no narrow INCR reaches the controller side (the monitor fails on one);
  * coverage: under randomized timing W beats are accepted while their AW
    still waits in the block's AW queue for the controller.

Production changes that fail it: stepping a narrow burst by full beats (the
TASK-007 defect -- every narrow beat after the first reads the wrong word),
dropping the W accumulator (the first half of a word is lost), replaying R
by the wrong count (RLAST early / late, the BFM times out or mis-frames), a
word count that ignores the first beat's offset (unaligned starts lose their
last word).

Cells: AXI_DATA_WIDTH 32 and 128, timing profile backtoback and
gaxi_realistic on both BFMs. Levels: TEST_LEVEL gate = 60 bursts, func =
400, full = 2000, plus a concurrent phase of multi-ID reads (R order is AR
order, the contract the controller's return ring gives this block).
"""
import os
import random

import pytest
import cocotb
from cocotb.triggers import FallingEdge, ReadOnly

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.amba.amba_random_configs import GAXI_RANDOMIZER_CONFIGS

from CocoTBFramework.components.axi4.axi4_factories import (
    create_axi4_master_rd, create_axi4_master_wr,
    create_axi4_slave_rd, create_axi4_slave_wr)
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.axi_burst import beat_addr, beat_lanes
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

_FILELIST = ("projects/components/mem-ctrl-ip/common-ip/dv/filelists/"
             "mc_axi4_narrow_pack_fub.f")

IW = 4
AW = 32
MEM_BYTES = 1 << 14
FIXED, INCR, WRAP = 0, 1, 2
LEVEL_BURSTS = {"gate": 60, "func": 400, "full": 2000}


def expected_rewrite(addr, length, size, burst, bus_bytes):
    """The controller-side (addr, len, size) for an upstream command."""
    full = bus_bytes.bit_length() - 1
    if burst != INCR or size >= full:
        return addr, length, size
    nb = 1 << size
    off = (addr % bus_bytes) & ~(nb - 1)
    words = (off + (length + 1) * nb + bus_bytes - 1) // bus_bytes
    return addr & ~(bus_bytes - 1), words - 1, full


class NarrowPackTB(TBBase):
    """Host-side master BFMs, controller-side slave BFMs over one memory."""

    def __init__(self, dut):
        super().__init__(dut)
        self.DW = int(os.environ.get("NP_DW", "128"))
        self.SW = self.DW // 8
        self.FULL = self.SW.bit_length() - 1
        self.profile = os.environ.get("NP_PROFILE", "backtoback")
        self.image = bytearray(MEM_BYTES)
        self.cmd_errors = []
        self.cmds_checked = 0
        self.narrow_rewrites = 0
        self.w_ahead_bursts = 0          # W bursts finished on a presented, unaccepted AW
        self.w_beats_awq = 0             # W beats accepted while an AW waits for the controller

    async def setup_clocks_and_reset(self):
        await self.start_clock("aclk", 10, "ns")
        await self.assert_reset()
        self._create_bfms()
        await self.wait_clocks("aclk", 5)
        await self.deassert_reset()
        await self.wait_clocks("aclk", 2)
        cocotb.start_soon(self._cmd_monitor("aw"))
        cocotb.start_soon(self._cmd_monitor("ar"))
        cocotb.start_soon(self._ahead_monitor())

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    def _create_bfms(self):
        kw = dict(data_width=self.DW, id_width=IW, addr_width=AW, user_width=1, multi_sig=True)
        self.mem = MemoryModel(num_lines=MEM_BYTES // self.SW, bytes_per_line=self.SW, log=self.log)
        # pipelined: AW and W queue independently, so W can reach the block
        # before its AW is accepted (the engine-runner pattern the pumice suite
        # drives); the default mode sends W only after the AW handshake.
        self.mwr = create_axi4_master_wr(self.dut, self.dut.aclk, prefix="fub_", log=self.log,
                                         ifc_name="host_wr", pipelined=self.profile != "backtoback",
                                         **kw)
        self.mrd = create_axi4_master_rd(self.dut, self.dut.aclk, prefix="fub_", log=self.log,
                                         ifc_name="host_rd", **kw)
        self.swr = create_axi4_slave_wr(self.dut, self.dut.aclk, prefix="m_", log=self.log,
                                        ifc_name="ctrl_wr", memory_model=self.mem, **kw)
        self.srd = create_axi4_slave_rd(self.dut, self.dut.aclk, prefix="m_", log=self.log,
                                        ifc_name="ctrl_rd", memory_model=self.mem, **kw)
        cfg = GAXI_RANDOMIZER_CONFIGS[self.profile]
        for bfm, chans, role in ((self.mwr, ("AW", "W"), "master"), (self.mrd, ("AR",), "master"),
                                 (self.swr, ("AW", "W"), "slave"), (self.srd, ("AR",), "slave"),
                                 (self.swr, ("B",), "master"), (self.srd, ("R",), "master"),
                                 (self.mwr, ("B",), "slave"), (self.mrd, ("R",), "slave")):
            for ch in chans:
                comp = bfm.get(ch)
                if comp is not None and hasattr(comp, "randomizer"):
                    comp.randomizer = FlexRandomizer(cfg[role])

    # ---- command-rewrite monitor (both sides fire in one cycle: combinational) ----
    # Sampled mid-cycle: the BFMs drive after the rising edge, so a read just
    # after it sees a mix of this cycle's and last cycle's handshake signals.
    async def _cmd_monitor(self, ch):
        d = self.dut
        up_q = []
        while True:
            await FallingEdge(d.aclk)
            await ReadOnly()
            if int(d.aresetn.value) == 0:
                continue
            if int(getattr(d, f"fub_{ch}valid").value) and int(getattr(d, f"fub_{ch}ready").value):
                up_q.append(tuple(int(getattr(d, f"fub_{ch}{f}").value)
                                  for f in ("addr", "len", "size", "burst")))
            if int(getattr(d, f"m_{ch}valid").value) and int(getattr(d, f"m_{ch}ready").value):
                got = tuple(int(getattr(d, f"m_{ch}{f}").value) for f in ("addr", "len", "size"))
                burst = int(getattr(d, f"m_{ch}burst").value)
                if not up_q:
                    self.cmd_errors.append(f"{ch}: downstream command {got} with no upstream one")
                    continue
                a, ln, sz, bu = up_q.pop(0)
                exp = expected_rewrite(a, ln, sz, bu, self.SW)
                self.cmds_checked += 1
                if exp != got or burst != bu:
                    self.cmd_errors.append(f"{ch}: up (0x{a:x}, len {ln}, size {sz}, burst {bu}) -> "
                                           f"got (0x{got[0]:x}, {got[1]}, {got[2]}, {burst}), "
                                           f"expected (0x{exp[0]:x}, {exp[1]}, {exp[2]})")
                if bu == INCR and got[2] != self.FULL:
                    self.cmd_errors.append(f"{ch}: narrow INCR reached the controller: {got}")
                if bu == INCR and sz < self.FULL:
                    self.narrow_rewrites += 1

    async def _ahead_monitor(self):
        """Coverage: W running ahead of an AW the controller has not accepted --
        through the AW queue, and through the presented-AW record."""
        d = self.dut
        prev = 0
        while True:
            await FallingEdge(d.aclk)
            await ReadOnly()
            cur = int(d.r_w_ahead.value)
            if cur and not prev:
                self.w_ahead_bursts += 1
            prev = cur
            if int(d.w_awq_valid.value) and int(d.fub_wvalid.value) and int(d.fub_wready.value):
                self.w_beats_awq += 1

    # ---- stimulus ----
    def rand_burst(self, rng):
        """(addr, len, size, burst) inside memory, legal AXI, not crossing 4 KB."""
        size = rng.choice(range(self.FULL + 1))
        nb = 1 << size
        r = rng.random()
        if r < 0.08:
            burst, length = FIXED, rng.randint(0, 7)
        elif r < 0.16:
            burst, length = WRAP, rng.choice([1, 3, 7, 15])
        else:
            burst = INCR
            length = rng.choice([0, 1, 2, 3, 7, rng.randint(0, 31), rng.randint(0, 63)])
        span = (length + 1) * nb
        while True:
            addr = rng.randrange(0, MEM_BYTES - span - self.SW)
            if burst == WRAP or rng.random() < 0.6:
                addr &= ~(nb - 1)                                  # size-aligned start
            aligned = addr & ~(nb - 1)
            end = (aligned + span - 1) if burst == INCR else (aligned + nb - 1)
            if (aligned >> 12) == (end >> 12):
                return addr, length, size, burst

    def _beats(self, addr, length, size, burst):
        for i in range(length + 1):
            strb, lane = beat_lanes(addr, i, size, burst, length, self.SW)
            a = beat_addr(addr, i, size, burst, length)
            yield i, strb, lane, a - (a % self.SW)

    async def write(self, rng, addr, length, size, burst, txn_id):
        nb = 1 << size
        data = [rng.getrandbits(8 * min(nb, self.SW)) for _ in range(length + 1)]
        await self.mwr["interface"].write_transaction(
            addr, data, burst_len=length + 1, id=txn_id, size=size, burst_type=burst)
        for i, strb, lane, word in self._beats(addr, length, size, burst):
            value = data[i] << (8 * lane) if nb < self.SW else data[i]
            for b in range(self.SW):
                if (strb >> b) & 1:
                    self.image[word + b] = (value >> (8 * b)) & 0xFF

    async def read_check(self, addr, length, size, burst, txn_id):
        got = await self.mrd["interface"].read_transaction(
            addr, burst_len=length + 1, id=txn_id, size=size, burst_type=burst)
        bad = 0
        for i, strb, _lane, word in self._beats(addr, length, size, burst):
            for b in range(self.SW):
                if (strb >> b) & 1 and ((got[i] >> (8 * b)) & 0xFF) != self.image[word + b]:
                    bad += 1
                    if bad <= 4:
                        self.log.error(f"read 0x{addr:x} len {length} size {size} burst {burst}: "
                                       f"beat {i} byte {b} got 0x{(got[i] >> (8 * b)) & 0xFF:02x} "
                                       f"expected 0x{self.image[word + b]:02x}")
        return bad


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_narrow_pack(dut):
    tb = NarrowPackTB(dut)
    seed = int(os.environ.get("SEED", "7"))
    rng = random.Random(seed)
    level = os.environ.get("TEST_LEVEL", "gate").lower()
    n = LEVEL_BURSTS.get(level, LEVEL_BURSTS["gate"])
    await tb.setup_clocks_and_reset()

    # 1. serial: write a burst, read it back, then re-read an older one
    history, bad, sizes = [], 0, set()
    for k in range(n):
        cmd = tb.rand_burst(rng)
        sizes.add(cmd[2])
        await tb.write(rng, *cmd, txn_id=k % (1 << IW))
        bad += await tb.read_check(*cmd, txn_id=(k + 3) % (1 << IW))
        history.append(cmd)
        if len(history) > 4 and rng.random() < 0.3:
            bad += await tb.read_check(*rng.choice(history), txn_id=rng.randrange(1 << IW))

    # 2. concurrent multi-ID reads of written regions: R comes back in AR order
    for _ in range(max(4, n // 20)):
        picks = [rng.choice(history) for _ in range(rng.randint(2, 6))]
        tasks = [cocotb.start_soon(tb.read_check(*c, txn_id=j)) for j, c in enumerate(picks)]
        for t in tasks:
            bad += await t

    await tb.wait_clocks("aclk", 20)
    for e in tb.cmd_errors[:8]:
        tb.log.error(e)
    tb.log.info(f"DW {tb.DW} profile {tb.profile}: {n} bursts, sizes {sorted(sizes)}, "
                f"{tb.cmds_checked} commands checked, {tb.narrow_rewrites} narrow INCR rewritten, "
                f"W ahead of the controller's AW: {tb.w_beats_awq} beats (AW queue), "
                f"{tb.w_ahead_bursts} bursts (presented AW); {bad} bad bytes")
    assert not tb.cmd_errors, f"{len(tb.cmd_errors)} command-rewrite errors"
    assert bad == 0, f"{bad} read bytes differ from the written image"
    assert tb.narrow_rewrites > n // 4, "too few narrow INCR bursts: the rewrite was barely exercised"
    assert sizes == set(range(tb.FULL + 1)), f"not every AxSIZE was driven: {sorted(sizes)}"
    if tb.profile != "backtoback":
        assert tb.w_beats_awq > 0, "no W beat ran ahead of a queued AW: that path was not exercised"


@pytest.mark.parametrize("profile", ["backtoback", "gaxi_realistic"])
@pytest.mark.parametrize("dw", [32, 128])
def test_mc_axi4_narrow_pack(request, dw, profile):
    from cocotb_test.simulator import run
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "mc_axi4_narrow_pack"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST)
    tag = request.node.name.replace("[", "_").replace("]", "").replace("-", "_")
    sim_build = sim_build_path(tests_dir, tag)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    params = {"AXI_ID_WIDTH": str(IW), "AXI_ADDR_WIDTH": str(AW), "AXI_DATA_WIDTH": str(dw),
              "AXI_USER_WIDTH": "1", "REC_DEPTH": "8"}
    extra_env = {"DUT": dut_name,
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{tag}.xml"),
                 "TEST_LEVEL": os.environ.get("TEST_LEVEL", "gate"),
                 "SEED": os.environ.get("SEED", "7"),
                 "NP_DW": str(dw),
                 "NP_PROFILE": profile}
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_narrow_pack",
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET", "--assert",
                      "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC"],
        waves=bool(int(os.environ.get("WAVES", "0"))),
        plus_args=(["--trace"] if int(os.environ.get("WAVES", "0")) else []),
        keep_files=True, timescale="1ns/1ps")
