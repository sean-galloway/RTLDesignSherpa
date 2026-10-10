# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit test for `andesite_axi_burst_chopper` -- host AxLEN to DRAM-burst subs.

Neither andesite nor pumice has ever had a test for this block, and it is the one
that GUARANTEES the contract both intakes are built on: one AXI sub-burst ==
one DFI burst. If a sub ever spans more beats than a DRAM burst, or the
sub-command addresses do not land on burst boundaries, the intake framing is
wrong for every transaction that follows it -- and the write path's zero-strobe
padding (PAD_TO_CHUNK) means a miscount there writes filler beats over real
data rather than dropping them.

Why this drives the ports directly instead of using the AXI4 BFMs: the fub side
is an address channel on its own (no W, no B, no R) and the m side is that
channel plus two non-AXI sideband bits, `m_ax_agg` and `m_ax_last`, which is
the whole point of the block. There is no AXI4 interface here for a BFM to
model. The house rule about always using the BFMs is about full interfaces --
where hand-poking valid/ready reinvents a protocol that is already implemented
and debugged.

The checks come in two layers. The model in `expected_subs` is the HEADER'S
contract restated -- at most CHUNK beats per sub, addresses stepping by
AXI_BURST_BYTES, agg/last as documented -- and on top of it sit invariants that
need no model at all: the real beats across the subs must add up to the host's
AxLEN+1, the addresses must be strictly increasing by exactly one burst, and
exactly one sub may carry `last`. The invariants are what survive a
disagreement about what the contract should be.
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

STRB_BYTES = 8                      # bytes per AXI beat in these builds
AX_FIELDS = ('axid', 'axsize', 'axburst', 'axlock', 'axcache', 'axprot',
             'axqos', 'axregion', 'axuser')


def expected_subs(base, axlen, chunk, pad, strb=STRB_BYTES):
    """The header's contract, restated: sub addresses, declared lens, sideband."""
    total = axlen + 1
    out, rem, i = [], total, 0
    while rem > 0:
        this = min(rem, chunk)
        out.append({
            'addr': base + i * chunk * strb,
            'len': (chunk - 1) if pad else (this - 1),
            'beats': this,                       # REAL beats, not declared
            'agg': 1 if total > chunk else 0,
            'last': 1 if rem <= chunk else 0,
        })
        rem -= this
        i += 1
    return out


class ChopTB(TBBase):
    def __init__(self, dut, chunk, pad):
        super().__init__(dut)
        self.chunk = chunk
        self.pad = pad

    async def setup(self):
        await self.start_clock('aclk', 10, 'ns')
        d = self.dut
        d.fub_axvalid.value = 0
        d.fub_axaddr.value = 0
        d.fub_axlen.value = 0
        for f in AX_FIELDS:
            getattr(d, f"fub_{f}").value = 0
        d.fub_axburst.value = 1                  # INCR
        d.m_axready.value = 0
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

    def _present(self, cmd):
        d = self.dut
        d.fub_axvalid.value = 1
        d.fub_axaddr.value = cmd['addr']
        d.fub_axlen.value = cmd['axlen']
        for f in AX_FIELDS:
            getattr(d, f"fub_{f}").value = cmd.get(f, 0)

    def _sample_sub(self):
        d = self.dut
        s = {'addr': int(d.m_axaddr.value), 'len': int(d.m_axlen.value),
             'agg': int(d.m_ax_agg.value), 'last': int(d.m_ax_last.value)}
        for f in AX_FIELDS:
            s[f] = int(getattr(d, f"m_{f}").value)
        return s

    async def run_commands(self, cmds, *, ready=lambda i: True, limit=4000):
        """Drive `cmds` back to back; return the accepted sub-commands.

        One loop drives the clock, so there is no race between the collector
        and the command driver: `m_axready` is set, the cycle settles, both
        handshakes are read from the same mid-cycle sample, and only then does
        the clock advance. `fub_axready` is registered nowhere -- it is
        `w_first && m_axready` -- so reading it in the same sample as the sub
        it accepts is exactly what the arbiter above would see.
        """
        d = self.dut
        subs, hold = [], []
        q = list(cmds)
        if q:
            self._present(q[0])
        cyc = 0
        while cyc < limit:
            d.m_axready.value = 1 if ready(cyc) else 0
            await Timer(1, 'ns')
            took_sub = bool(int(d.m_axvalid.value) and int(d.m_axready.value))
            if took_sub:
                subs.append(self._sample_sub())
            took_cmd = bool(int(d.fub_axvalid.value) and int(d.fub_axready.value))
            await self.tick()
            if took_cmd:
                hold.append(q.pop(0))
                if q:
                    self._present(q[0])
                else:
                    d.fub_axvalid.value = 0
            if not q and not int(d.fub_axvalid.value):
                # Everything accepted; let the last command finish draining.
                if subs and subs[-1]['last']:
                    break
            cyc += 1
        d.m_axready.value = 0
        return subs


def split_by_last(subs):
    """Group a sub stream into per-host-command lists using m_ax_last."""
    groups, cur = [], []
    for s in subs:
        cur.append(s)
        if s['last']:
            groups.append(cur); cur = []
    if cur:
        groups.append(cur)          # unterminated -- a failure for the caller
    return groups


@cocotb.test(timeout_time=120, timeout_unit="ms")
async def cocotb_test_andesite_axi_burst_chopper(dut):
    tt = os.environ.get("TEST_TYPE", "single_sub_passthrough")
    chunk = int(os.environ.get("CHUNK", "4"))
    pad = int(os.environ.get("PAD", "0"))
    tb = ChopTB(dut, chunk, pad)
    fails = []

    def chk(c, m):
        if not c:
            fails.append(m); tb.log.error(m)

    def check_cmd(subs, base, axlen, tag):
        """Model comparison plus the model-free invariants."""
        exp = expected_subs(base, axlen, chunk, pad)
        chk(len(subs) == len(exp),
            f"{tag}: {len(subs)} sub-commands for AxLEN={axlen} at CHUNK="
            f"{chunk}, expected {len(exp)}")
        for i, (g, e) in enumerate(zip(subs, exp)):
            chk(g['addr'] == e['addr'],
                f"{tag} sub{i}: addr 0x{g['addr']:08X}, expected "
                f"0x{e['addr']:08X} -- subs must land on DRAM-burst "
                f"boundaries {chunk * STRB_BYTES} bytes apart")
            chk(g['len'] == e['len'],
                f"{tag} sub{i}: axlen {g['len']}, expected {e['len']} "
                f"(PAD_TO_CHUNK={pad})")
            chk(g['agg'] == e['agg'],
                f"{tag} sub{i}: agg {g['agg']}, expected {e['agg']} -- the "
                f"return path collapses per-sub responses using this bit")
            chk(g['last'] == e['last'],
                f"{tag} sub{i}: last {g['last']}, expected {e['last']}")
        # Model-free invariants.
        chk(sum(1 for s in subs if s['last']) == 1,
            f"{tag}: {sum(1 for s in subs if s['last'])} subs carry last; "
            f"exactly one closes a host command or the B/R aggregation never "
            f"completes")
        real = sum(min(axlen + 1 - i * chunk, chunk)
                   for i in range(len(subs)))
        chk(real == axlen + 1,
            f"{tag}: the subs cover {real} real beats, the host asked for "
            f"{axlen + 1}")
        for i in range(1, len(subs)):
            step = subs[i]['addr'] - subs[i - 1]['addr']
            chk(step == chunk * STRB_BYTES,
                f"{tag} sub{i}: address stepped {step} bytes from the previous "
                f"sub, expected exactly one burst "
                f"({chunk * STRB_BYTES})")

    if tt == "single_sub_passthrough":
        # A host burst no longer than one DRAM burst must pass through
        # untouched: same address, agg clear, last set, one sub.
        await tb.setup()
        for axlen in range(0, chunk):
            base = 0x1000_0000 + axlen * 0x100
            subs = await tb.run_commands([{'addr': base, 'axlen': axlen}])
            check_cmd(subs, base, axlen, f"axlen={axlen}")
            if subs:
                chk(subs[0]['agg'] == 0,
                    f"axlen={axlen}: a command that fits one DRAM burst was "
                    f"marked agg -- the return path would wait for a second "
                    f"response that never comes")

    elif tt == "regular_split_exact":
        # The andesite-aligned case: a whole multiple of CHUNK.
        await tb.setup()
        for k in (2, 3, 8):
            axlen = k * chunk - 1
            if axlen > 255:
                continue
            base = 0x2000_0000
            subs = await tb.run_commands([{'addr': base, 'axlen': axlen}])
            check_cmd(subs, base, axlen, f"k={k}")
            chk(len(subs) == k, f"k={k}: got {len(subs)} subs, expected {k}")

    elif tt == "ragged_tail":
        # Robustness case the header calls out: andesite never issues one, but a
        # short tail must still be framed correctly rather than over-read.
        await tb.setup()
        for axlen in (chunk, chunk + 1, 2 * chunk + 1, 3 * chunk - 2):
            if axlen > 255 or axlen < 1:
                continue
            base = 0x3000_0000
            subs = await tb.run_commands([{'addr': base, 'axlen': axlen}])
            check_cmd(subs, base, axlen, f"axlen={axlen}")

    elif tt == "axlen_sweep":
        # Every host length the AXI4 spec allows, against the contract.
        await tb.setup()
        for axlen in list(range(0, 40)) + [63, 64, 127, 255]:
            base = 0x4000_0000 + (axlen << 12)
            subs = await tb.run_commands([{'addr': base, 'axlen': axlen}])
            check_cmd(subs, base, axlen, f"axlen={axlen}")

    elif tt == "fields_survive_every_sub":
        # Every sub of a split carries the host command's sideband. A field
        # latched wrong shows up as an ID collision in the CAM, which is a
        # data-returned-to-the-wrong-master bug, not a performance one.
        await tb.setup()
        rng = random.Random(41)
        for _ in range(6):
            cmd = {'addr': 0x5000_0000, 'axlen': 4 * chunk - 1,
                   'axid': rng.randrange(1 << 8), 'axsize': rng.randrange(8),
                   'axburst': 1, 'axlock': rng.randint(0, 1),
                   'axcache': rng.randrange(16), 'axprot': rng.randrange(8),
                   'axqos': rng.randrange(16), 'axregion': rng.randrange(16),
                   'axuser': rng.randint(0, 1)}
            subs = await tb.run_commands([cmd])
            for i, s in enumerate(subs):
                for f in AX_FIELDS:
                    chk(s[f] == cmd[f],
                        f"sub{i}: {f}={s[f]} but the host command carried "
                        f"{cmd[f]} -- a sub of a split must be the same "
                        f"transaction")

    elif tt == "host_stalls_while_draining":
        # fub_axready must stay low for every continuation sub, or a second
        # host command is accepted on top of one still being emitted and the
        # two interleave.
        await tb.setup()
        d = dut
        tb._present({'addr': 0x6000_0000, 'axlen': 4 * chunk - 1})
        d.m_axready.value = 1
        await Timer(1, 'ns')
        chk(int(d.fub_axready.value) == 1,
            "fub_axready low for the first sub with m_axready high -- the "
            "command can never be accepted")
        await tb.tick()
        for i in range(3):                        # the three continuation subs
            chk(int(d.fub_axready.value) == 0,
                f"fub_axready high while continuation sub {i + 1} was being "
                f"emitted -- the next host command would be swallowed into "
                f"the middle of this one")
            chk(int(d.m_axvalid.value) == 1,
                f"m_axvalid low on continuation sub {i + 1}; its work is "
                f"already latched and cannot be withdrawn")
            await tb.tick()
        d.fub_axvalid.value = 0
        d.m_axready.value = 0

    elif tt == "valid_is_stable_under_backpressure":
        # AXI4: once valid is asserted it must hold, payload unchanged, until
        # ready. The continuation subs assert valid unconditionally, so the
        # risk is the payload moving underneath it.
        await tb.setup()
        d = dut
        tb._present({'addr': 0x7000_0000, 'axlen': 3 * chunk - 1, 'axid': 0x5A})
        d.m_axready.value = 1
        await Timer(1, 'ns')
        await tb.tick()                            # first sub accepted
        d.m_axready.value = 0
        await Timer(1, 'ns')
        held = tb._sample_sub()
        for i in range(12):
            chk(int(d.m_axvalid.value) == 1,
                f"m_axvalid dropped {i} cycles into backpressure with a sub "
                f"still unaccepted")
            chk(tb._sample_sub() == held,
                f"the presented sub changed under backpressure at cycle {i}: "
                f"{tb._sample_sub()} vs {held} -- AXI4 requires the payload to "
                f"hold with valid")
            await tb.tick()
        d.m_axready.value = 1
        await Timer(1, 'ns')
        chk(tb._sample_sub() == held,
            "the sub changed on the cycle the backpressure lifted")
        d.fub_axvalid.value = 0
        d.m_axready.value = 0

    elif tt == "back_to_back_commands":
        # Several host commands with no gap. The sub stream must partition
        # cleanly by `last`, with no sub of one command carrying another's
        # address.
        await tb.setup()
        cmds = [{'addr': 0x8000_0000, 'axlen': chunk - 1, 'axid': 1},
                {'addr': 0x8100_0000, 'axlen': 2 * chunk - 1, 'axid': 2},
                {'addr': 0x8200_0000, 'axlen': 0, 'axid': 3},
                {'addr': 0x8300_0000, 'axlen': 3 * chunk - 1, 'axid': 4}]
        subs = await tb.run_commands(cmds)
        groups = split_by_last(subs)
        chk(len(groups) == len(cmds),
            f"{len(subs)} subs partitioned into {len(groups)} commands by "
            f"`last`, expected {len(cmds)}")
        for c, g in zip(cmds, groups):
            check_cmd(g, c['addr'], c['axlen'], f"id={c['axid']}")
            chk(all(s['axid'] == c['axid'] for s in g),
                f"id={c['axid']}: a sub carried another command's ID "
                f"{[s['axid'] for s in g]}")

    elif tt == "random_backpressure_is_transparent":
        # The sub stream must not depend on WHEN the downstream accepts. This
        # is the case that catches an accounting update on the wrong cycle:
        # with ready always high, an off-by-one hides.
        await tb.setup()
        cmds = [{'addr': 0x9000_0000 + i * 0x1000,
                 'axlen': (i * 3) % 24, 'axid': i} for i in range(8)]
        clean = await tb.run_commands(cmds)
        for seed in (1, 2, 3):
            rng = random.Random(seed)
            await tb.setup()
            noisy = await tb.run_commands(
                cmds, ready=lambda i, r=rng: r.random() < 0.55)
            chk(noisy == clean,
                f"seed={seed}: the sub stream changed under random "
                f"backpressure ({len(noisy)} subs vs {len(clean)}). The "
                f"chopper's accounting must be driven by the handshake, not "
                f"by the cycle count.")

    elif tt == "random_soak":
        rng = random.Random(int(os.environ.get('SEED', '31')))
        lvl = os.environ.get("TEST_LEVEL", "FUNC").upper()
        n = {"GATE": 8, "FUNC": 40, "FULL": 150}.get(lvl, 40)
        await tb.setup()
        for _ in range(n):
            cmd = {'addr': rng.randrange(1 << 24) * STRB_BYTES,
                   'axlen': rng.randrange(256), 'axid': rng.randrange(256)}
            subs = await tb.run_commands(
                [cmd], ready=lambda i, r=rng: r.random() < 0.7)
            check_cmd(subs, cmd['addr'], cmd['axlen'],
                      f"axlen={cmd['axlen']}")
            chk(all(s['axid'] == cmd['axid'] for s in subs),
                f"axlen={cmd['axlen']}: an ID changed mid-command")
    else:
        raise ValueError(f"Unknown TEST_TYPE: {tt}")

    await tb.wait_clocks('aclk', 3)
    assert not fails, f"{len(fails)} check(s) failed:\n  " + "\n  ".join(fails)


# (case, CHUNK, PAD_TO_CHUNK). CHUNK 1 is the degenerate build (every host beat
# is its own DRAM burst); 4 is the board's read path; 4 with PAD is its write
# path, where the splitter pads the W stream out with zero-strobe filler.
_GATE = [("single_sub_passthrough", 4, 0),
         ("regular_split_exact", 4, 0),
         ("axlen_sweep", 4, 0)]
_FUNC = _GATE + [
    ("single_sub_passthrough", 1, 0),
    ("regular_split_exact", 8, 0),
    ("ragged_tail", 4, 0),
    ("ragged_tail", 4, 1),
    ("axlen_sweep", 2, 1),
    ("fields_survive_every_sub", 4, 0),
    ("host_stalls_while_draining", 4, 0),
    ("valid_is_stable_under_backpressure", 4, 0),
    ("back_to_back_commands", 4, 0),
    ("random_backpressure_is_transparent", 4, 0),
    ("random_soak", 4, 0),
    ("random_soak", 4, 1),
]
_TEST_LEVEL = (os.environ.get("REG_LEVEL") or os.environ.get("TEST_LEVEL")
               or "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FUNC}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type, chunk, pad", _PARAMS)
def test_andesite_axi_burst_chopper(request, test_type, chunk, pad):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "mc_axi_burst_chopper"
    test_name = f"test_andesite_axi_burst_chopper_{test_type}_c{chunk}_p{pad}"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/common-ip/"
                       "rtl/filelists/fub/mc_axi_burst_chopper.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True); os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_andesite_axi_burst_chopper",
        sim_build=sim_build, simulator="verilator",
        parameters={"AXI_ID_WIDTH": "8", "AXI_ADDR_WIDTH": "32",
                    "STRB_BYTES": str(STRB_BYTES),
                    "AXI_BEATS_PER_BURST": str(chunk),
                    "PAD_TO_CHUNK": str(pad)},
        extra_env={"DUT": dut_name, "TEST_TYPE": test_type,
                   "CHUNK": str(chunk), "PAD": str(pad),
                   "TEST_LEVEL": _TEST_LEVEL, "COCOTB_LOG_LEVEL": "INFO",
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET"],
        keep_files=True, timescale="1ns/1ps")
