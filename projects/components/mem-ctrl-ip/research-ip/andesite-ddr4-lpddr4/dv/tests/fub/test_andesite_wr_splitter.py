# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit test for `andesite_wr_splitter` -- AW chopping plus W re-framing.

The header calls the WLAST re-frame "the key correctness point", and names the
bug it replaced: the old shared `axi_master_wr_splitter` tied WLAST to a beat
budget set by its AW FSM, so when a host burst split into many single-beat DRAM
bursts most sub-bursts never got a WLAST and the write-data CAM never delimited
them. The second half is the zero-strobe padding: a host burst that does not
fill a whole DRAM burst is COMPLETED with filler beats (strb=0 becomes DM=1 in
the serializer) rather than rejected, which is what makes AxLEN=0 writeable at
all -- before it, a compliant single-beat write was answered with SLVERR and
dropped.

Both of those are claims about the W stream as a whole, so this test checks the
stream, not cycles:

  * every chunk is exactly AXI_BEATS_PER_BURST beats long and carries exactly
    one WLAST, at its end;
  * the beats with a non-zero strobe, in order, are exactly the host's beats,
    in order -- no beat duplicated by the padding path, none dropped;
  * the filler beats carry strb == 0 (anything else writes over real data,
    which is worse than the SLVERR this replaced);
  * `fub_wready` is low for every filler beat, so the host cannot push a beat
    into the middle of a pad;
  * the number of W chunks equals the number of AW sub-commands. The two paths
    are deliberately independent -- the counter is driven off the W handshake,
    NOT off the AW side -- so nothing in the RTL forces them to agree, and the
    intake pairs them positionally.

Ports are driven directly rather than through the AXI4 BFMs for the same
reason as the chopper's test: this is a request-side transform with non-AXI
sideband (`m_aw_agg` / `m_aw_last`) and no B channel at all, so there is no
complete AXI4 interface here for a BFM to model.
"""

import os
import random

import cocotb
import pytest
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, sim_build_path

DW = 64
SW = DW // 8
STRB_ALL = (1 << SW) - 1


class SplitTB(TBBase):
    def __init__(self, dut, chunk):
        super().__init__(dut)
        self.chunk = chunk

    async def setup(self):
        await self.start_clock('aclk', 10, 'ns')
        d = self.dut
        for s in ('fub_awvalid', 'fub_wvalid', 'fub_wlast', 'm_awready',
                  'm_wready'):
            getattr(d, s).value = 0
        d.fub_awid.value = 0
        d.fub_awaddr.value = 0
        d.fub_awlen.value = 0
        d.fub_awsize.value = 3
        d.fub_awburst.value = 1
        d.fub_awlock.value = 0
        d.fub_awcache.value = 0
        d.fub_awprot.value = 0
        d.fub_awqos.value = 0
        d.fub_awregion.value = 0
        d.fub_awuser.value = 0
        d.fub_wdata.value = 0
        d.fub_wstrb.value = 0
        d.fub_wuser.value = 0
        await self.assert_reset()
        await self.wait_clocks('aclk', 5)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 2)
        await Timer(1, 'ns')

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    async def setup_clocks_and_reset(self):
        await self.setup()

    async def tick(self):
        await RisingEdge(self.dut.aclk)
        await Timer(1, 'ns')

    async def run_write(self, addr, axlen, *, wid=0, ready=lambda i: True,
                        limit=6000):
        """Drive one host write (AW + its W beats); collect the m-side streams.

        One loop owns the clock so the AW and W collectors cannot race. Host
        W beats carry data = beat index + 1 and a full strobe, which makes a
        filler beat (strb == 0, data 0) unmistakable in the trace.
        """
        d = self.dut
        total = axlen + 1
        subs, wbeats = [], []
        d.fub_awvalid.value = 1
        d.fub_awid.value = wid
        d.fub_awaddr.value = addr
        d.fub_awlen.value = axlen
        d.fub_wvalid.value = 1
        wi = 0
        d.fub_wdata.value = wi + 1
        d.fub_wstrb.value = STRB_ALL
        d.fub_wlast.value = 1 if total == 1 else 0
        aw_done = False
        cyc = 0
        while cyc < limit:
            r = ready(cyc)
            d.m_awready.value = 1 if r else 0
            d.m_wready.value = 1 if r else 0
            await Timer(1, 'ns')
            took_aw = bool(int(d.m_awvalid.value) and int(d.m_awready.value))
            if took_aw:
                subs.append({'addr': int(d.m_awaddr.value),
                             'len': int(d.m_awlen.value),
                             'id': int(d.m_awid.value),
                             'agg': int(d.m_aw_agg.value),
                             'last': int(d.m_aw_last.value)})
            took_w = bool(int(d.m_wvalid.value) and int(d.m_wready.value))
            if took_w:
                wbeats.append({'data': int(d.m_wdata.value),
                               'strb': int(d.m_wstrb.value),
                               'last': int(d.m_wlast.value),
                               'fub_ready': int(d.fub_wready.value)})
            took_host_w = bool(int(d.fub_wvalid.value)
                               and int(d.fub_wready.value))
            took_host_aw = bool(int(d.fub_awvalid.value)
                                and int(d.fub_awready.value))
            await self.tick()
            if took_host_aw:
                d.fub_awvalid.value = 0
                aw_done = True
            if took_host_w:
                wi += 1
                if wi >= total:
                    d.fub_wvalid.value = 0
                    d.fub_wlast.value = 0
                else:
                    d.fub_wdata.value = wi + 1
                    d.fub_wlast.value = 1 if wi == total - 1 else 0
            if aw_done and wi >= total and wbeats and wbeats[-1]['last']:
                break
            cyc += 1
        d.m_awready.value = 0
        d.m_wready.value = 0
        return subs, wbeats


@cocotb.test(timeout_time=120, timeout_unit="ms")
async def cocotb_test_andesite_wr_splitter(dut):
    tt = os.environ.get("TEST_TYPE", "single_beat_write_is_padded")
    chunk = int(os.environ.get("CHUNK", "4"))
    tb = SplitTB(dut, chunk)
    fails = []

    def chk(c, m):
        if not c:
            fails.append(m); tb.log.error(m)

    def check_write(subs, wbeats, axlen, tag):
        total = axlen + 1
        n_chunks = (total + chunk - 1) // chunk
        # ---- AW side ----
        chk(len(subs) == n_chunks,
            f"{tag}: {len(subs)} AW sub-commands for {total} host beats at "
            f"CHUNK={chunk}, expected {n_chunks}")
        chk(all(s['len'] == chunk - 1 for s in subs),
            f"{tag}: sub lens {[s['len'] for s in subs]}; the write path sets "
            f"PAD_TO_CHUNK, so EVERY sub declares a full DRAM burst")
        chk(sum(s['last'] for s in subs) == 1,
            f"{tag}: {sum(s['last'] for s in subs)} subs carry aw_last")
        # ---- W side ----
        chk(len(wbeats) == n_chunks * chunk,
            f"{tag}: {len(wbeats)} W beats reached the intake, expected "
            f"{n_chunks * chunk} ({n_chunks} chunks of {chunk}) -- a DRAM "
            f"burst is indivisible and every chunk must be filled")
        for c in range(n_chunks):
            seg = wbeats[c * chunk:(c + 1) * chunk]
            if len(seg) != chunk:
                continue
            lasts = [i for i, b in enumerate(seg) if b['last']]
            chk(lasts == [chunk - 1],
                f"{tag} chunk {c}: wlast at beats {lasts}, expected only at "
                f"beat {chunk - 1}. A chunk with no WLAST is never delimited "
                f"in the write-data CAM -- that is the bug this re-frame "
                f"replaced.")
        # Real beats, in order, are exactly the host's.
        real = [b['data'] for b in wbeats if b['strb'] != 0]
        chk(real == list(range(1, total + 1)),
            f"{tag}: the strobed beats carry {real}, the host sent "
            f"{list(range(1, total + 1))} -- the padding path must not "
            f"duplicate or drop a real beat")
        fillers = [b for b in wbeats if b['strb'] == 0]
        chk(len(fillers) == n_chunks * chunk - total,
            f"{tag}: {len(fillers)} filler beats, expected "
            f"{n_chunks * chunk - total}")
        chk(all(b['fub_ready'] == 0 for b in fillers),
            f"{tag}: fub_wready was high during a filler beat -- a host beat "
            f"pushed into the middle of a pad lands in the wrong chunk")

    if tt == "single_beat_write_is_padded":
        # The case that used to be answered with SLVERR and dropped. AxLEN=0 is
        # legal AXI4 and a compliant master issues it.
        await tb.setup()
        subs, wbeats = await tb.run_write(0x1000, 0)
        check_write(subs, wbeats, 0, "axlen=0")
        chk(len(subs) == 1 and subs[0]['agg'] == 0 and subs[0]['last'] == 1,
            f"axlen=0 produced {len(subs)} subs with agg="
            f"{subs[0]['agg'] if subs else '?'} -- one beat is one sub")

    elif tt == "aligned_multi_chunk":
        await tb.setup()
        for k in (2, 3, 5):
            axlen = k * chunk - 1
            if axlen > 255:
                continue
            subs, wbeats = await tb.run_write(0x2000 + k * 0x100, axlen)
            check_write(subs, wbeats, axlen, f"k={k}")
            chk(all(b['strb'] == STRB_ALL for b in wbeats),
                f"k={k}: an exact multiple of the chunk needs NO filler, but "
                f"{sum(1 for b in wbeats if b['strb'] == 0)} beats came "
                f"through with a zero strobe")

    elif tt == "ragged_burst_is_padded_to_the_chunk":
        await tb.setup()
        for axlen in (1, chunk, chunk + 1, 2 * chunk + 2):
            if axlen > 255:
                continue
            subs, wbeats = await tb.run_write(0x3000, axlen)
            check_write(subs, wbeats, axlen, f"axlen={axlen}")

    elif tt == "axlen_sweep":
        await tb.setup()
        for axlen in list(range(0, 18)) + [31, 63, 255]:
            subs, wbeats = await tb.run_write(0x4000 + (axlen << 8), axlen)
            check_write(subs, wbeats, axlen, f"axlen={axlen}")

    elif tt == "host_wlast_does_not_end_the_chunk":
        # The specific rule the header states: "The host's own wlast no longer
        # terminates a short chunk -- it starts the padding." If the host's
        # WLAST passed straight through, the intake would see a burst shorter
        # than BL and the DRAM would be left mid-burst.
        await tb.setup()
        axlen = 0 if chunk > 1 else 1
        subs, wbeats = await tb.run_write(0x5000, axlen)
        if chunk > 1:
            chk(len(wbeats) >= 1 and wbeats[0]['last'] == 0,
                f"the host's single beat came through with WLAST set "
                f"({wbeats[0] if wbeats else None}) -- at CHUNK={chunk} it is "
                f"beat 1 of {chunk} and the chunk is not over")
            chk(wbeats[-1]['last'] == 1 and wbeats[-1]['strb'] == 0,
                f"the chunk's WLAST should land on the last FILLER beat, got "
                f"{wbeats[-1]}")
        check_write(subs, wbeats, axlen, f"axlen={axlen}")

    elif tt == "back_to_back_writes":
        # Consecutive host writes must not bleed into each other: the pad of
        # one must complete before the next host beat is taken.
        await tb.setup()
        for i, axlen in enumerate((0, chunk, 1, 2 * chunk - 1)):
            subs, wbeats = await tb.run_write(0x6000 + i * 0x100, axlen, wid=i)
            check_write(subs, wbeats, axlen, f"write{i} axlen={axlen}")
            chk(all(s['id'] == i for s in subs),
                f"write{i}: sub IDs {[s['id'] for s in subs]} -- a sub picked "
                f"up another command's ID")

    elif tt == "random_backpressure_is_transparent":
        # The W counter is driven off the handshake, so the stream must not
        # depend on WHEN the intake accepts.
        await tb.setup()
        base = []
        for axlen in (0, 1, chunk + 1, 3 * chunk - 1):
            base.append(await tb.run_write(0x7000, axlen))
        for seed in (5, 6):
            rng = random.Random(seed)
            await tb.setup()
            for j, axlen in enumerate((0, 1, chunk + 1, 3 * chunk - 1)):
                got = await tb.run_write(0x7000, axlen,
                                         ready=lambda i, r=rng: r.random() < 0.6)
                chk(got == base[j],
                    f"seed={seed} axlen={axlen}: the m-side stream changed "
                    f"under random backpressure. {len(got[1])} W beats vs "
                    f"{len(base[j][1])}; the re-frame must follow the "
                    f"handshake, not the cycle count.")

    elif tt == "random_soak":
        rng = random.Random(int(os.environ.get('SEED', '37')))
        lvl = os.environ.get("TEST_LEVEL", "FUNC").upper()
        n = {"GATE": 6, "FUNC": 25, "FULL": 90}.get(lvl, 25)
        await tb.setup()
        for _ in range(n):
            axlen = rng.choice([rng.randrange(0, 8), rng.randrange(0, 64),
                                rng.randrange(0, 256)])
            subs, wbeats = await tb.run_write(rng.randrange(1 << 20) * SW,
                                              axlen,
                                              wid=rng.randrange(256),
                                              ready=lambda i, r=rng:
                                              r.random() < 0.75)
            check_write(subs, wbeats, axlen, f"axlen={axlen}")
    else:
        raise ValueError(f"Unknown TEST_TYPE: {tt}")

    await tb.wait_clocks('aclk', 3)
    assert not fails, f"{len(fails)} check(s) failed:\n  " + "\n  ".join(fails)


# CHUNK=1 is the x16 single-beat-DRAM-burst build whose missing WLASTs are the
# bug this module was written to fix; 4 is the Genesys 2 write path.
_GATE = [("single_beat_write_is_padded", 4), ("axlen_sweep", 4),
         ("host_wlast_does_not_end_the_chunk", 4)]
_FUNC = _GATE + [
    ("single_beat_write_is_padded", 1),
    ("aligned_multi_chunk", 4),
    ("aligned_multi_chunk", 2),
    ("ragged_burst_is_padded_to_the_chunk", 4),
    ("ragged_burst_is_padded_to_the_chunk", 8),
    ("axlen_sweep", 1),
    ("back_to_back_writes", 4),
    ("random_backpressure_is_transparent", 4),
    ("random_soak", 4),
]
_TEST_LEVEL = (os.environ.get("REG_LEVEL") or os.environ.get("TEST_LEVEL")
               or "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FUNC}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type, chunk", _PARAMS)
def test_andesite_wr_splitter(request, test_type, chunk):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "mc_wr_splitter"
    test_name = f"test_andesite_wr_splitter_{test_type}_c{chunk}"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/common-ip/"
                       "rtl/filelists/fub/mc_wr_splitter.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True); os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_andesite_wr_splitter",
        sim_build=sim_build, simulator="verilator",
        parameters={"AXI_ID_WIDTH": "8", "AXI_ADDR_WIDTH": "32",
                    "AXI_DATA_WIDTH": str(DW),
                    "AXI_BEATS_PER_BURST": str(chunk)},
        extra_env={"DUT": dut_name, "TEST_TYPE": test_type,
                   "CHUNK": str(chunk), "TEST_LEVEL": _TEST_LEVEL,
                   "COCOTB_LOG_LEVEL": "INFO",
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET"],
        keep_files=True, timescale="1ns/1ps")
