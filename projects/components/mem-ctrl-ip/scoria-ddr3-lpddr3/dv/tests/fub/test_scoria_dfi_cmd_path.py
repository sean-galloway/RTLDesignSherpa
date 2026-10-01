# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit test for `scoria_dfi_cmd_path` -- the conduit that must not pace.

Two board failures are written into this module's header, and both are what
this file is for.

TASK-007, the rule: "it must never insert an idle cycle of its own, because the
CDC command FIFO preserves ORDER but not SPACING -- so any stall here silently
rewrites the interval between every command queued behind it." The previous
revision paced columns here. Holding a column for tRTW=20 at the head of an
8-deep in-order FIFO backed the queue up, and the ACT/PRE/REF behind it --
correctly spaced by the arbiter, needing no DQ bus at all -- drained back to
back on release. Board ILA: REF to ACT compressed from 15 cycles to 3, inside
tRFC; the DRAM discarded the activate, the bank never opened, and 180
consecutive reads came back off an undriven bus. `never_inserts_an_idle_cycle`
is that rule as a measurement.

Task #146, the packing: when one DFI word holds N_SUBCMD JEDEC bursts (the
board's gear 1:4 with x16 BL4), the sub-commands must be issued in ONE DFI
cycle on distinct phases. The earlier expansion over consecutive CYCLES left
the other phase-pair stale and produced the on-board 2-of-4 read corruption.
`sub_packing_is_one_cycle` pins the shape that replaced it.

The two legal holds -- a read with no aligner slot, a write with no staged data
-- are structural, not timing, and the module says so: if either fires it
compresses spacing exactly as above, and the fix belongs upstream. They are
tested as op-specific, because a hold applied to the wrong op class is the same
bug wearing a different hat.
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

OP_NOP, OP_ACT, OP_RD, OP_RDA, OP_WR, OP_WRA = 0x0, 0x1, 0x2, 0x3, 0x4, 0x5
OP_PRE, OP_PREA, OP_REF = 0x6, 0x7, 0x8

NUM_BANKS, ROW_WIDTH, COL_WIDTH, DFI_RATE = 8, 14, 10, 4
MEMTYPE_DDR3 = 0            # memtype_e: scoria_pkg's first entry
ADDR_W = 14                 # DFI_ADDR_WIDTH


def pack(op, *, bank=0, row=0, col=0, rank=0, ap=0):
    """{ap, col, row, bank, rank, op} -- op in the low bits."""
    v = op & 0xF
    v |= (rank & 0x1) << 4
    v |= (bank & 0x7) << 5
    v |= (row & ((1 << ROW_WIDTH) - 1)) << 8
    v |= (col & ((1 << COL_WIDTH) - 1)) << (8 + ROW_WIDTH)
    v |= (ap & 0x1) << (8 + ROW_WIDTH + COL_WIDTH)
    return v


class CmdPathTB(TBBase):
    async def setup(self, *, n_subcmd=1, sub_col_stride=0, sub_phase_stride=1,
                    rd_phase=0, wr_phase=0):
        await self.start_clock('dfi_clk', 10, 'ns')
        d = self.dut
        d.memtype_i.value = MEMTYPE_DDR3
        d.rd_phase_i.value = rd_phase
        d.wr_phase_i.value = wr_phase
        d.n_subcmd_i.value = n_subcmd
        d.sub_col_stride_i.value = sub_col_stride
        d.sub_phase_stride_i.value = sub_phase_stride
        d.cmd_valid_i.value = 0
        d.cmd_data_i.value = 0
        d.rd_op_ready_i.value = 1
        d.wr_op_ready_i.value = 1
        await self.assert_reset()
        await self.wait_clocks('dfi_clk', 5)
        await self.deassert_reset()
        await self.wait_clocks('dfi_clk', 2)
        await Timer(1, 'ns')

    async def assert_reset(self):
        self.dut.dfi_rstn.value = 0

    async def deassert_reset(self):
        self.dut.dfi_rstn.value = 1

    async def setup_clocks_and_reset(self):
        await self.setup()

    async def tick(self):
        await RisingEdge(self.dut.dfi_clk)
        await Timer(1, 'ns')

    def active_phases(self):
        """Phases whose chip select is asserted (cs_n low) this cycle."""
        cs = int(self.dut.dfi_cs_n_o.value)
        return [p for p in range(DFI_RATE) if not ((cs >> p) & 1)]

    def phase_addr(self, p):
        a = int(self.dut.dfi_address_o.value)
        return (a >> (p * ADDR_W)) & ((1 << ADDR_W) - 1)

    def present(self, word):
        self.dut.cmd_valid_i.value = 1
        self.dut.cmd_data_i.value = word

    async def drive(self, word):
        """Present one command and step to the cycle its wire appears on.

        scoria_dfi_cmd_formatter has STRICT-FLOP outputs, so the DFI buses show
        the command one cycle after it is presented. Reading them in the
        presenting cycle sees the PREVIOUS command -- which, from reset, is an
        idle bus, and every phase check then reads "nothing was driven" no
        matter what the module does.
        """
        self.present(word)
        await self.tick()
        self.idle_cmd()
        return self.active_phases()

    def idle_cmd(self):
        self.dut.cmd_valid_i.value = 0
        self.dut.cmd_data_i.value = 0

    async def stream(self, words, *, limit=400):
        """Present `words` back to back; return one record per cycle."""
        d = self.dut
        q = list(words)
        trace = []
        if q:
            self.present(q[0])
        cyc = 0
        while cyc < limit:
            await Timer(1, 'ns')
            took = bool(int(d.cmd_valid_i.value) and int(d.cmd_ready_o.value))
            trace.append({'cyc': cyc,
                          'ready': int(d.cmd_ready_o.value),
                          'took': took,
                          'phases': self.active_phases(),
                          'rd_fire': int(d.rd_fire_o.value),
                          'wr_fire': int(d.wr_fire_o.value),
                          'wr_accept': int(d.wr_accept_o.value)})
            await self.tick()
            if took:
                q.pop(0)
                if q:
                    self.present(q[0])
                else:
                    self.idle_cmd()
            if not q:
                # two more cycles so the REGISTERED fire strobes land
                for k in range(1, 3):
                    await Timer(1, 'ns')
                    trace.append({'cyc': cyc + k, 'ready': int(d.cmd_ready_o.value),
                                  'took': False, 'phases': self.active_phases(),
                                  'rd_fire': int(d.rd_fire_o.value),
                                  'wr_fire': int(d.wr_fire_o.value),
                                  'wr_accept': int(d.wr_accept_o.value)})
                    await self.tick()
                break
            cyc += 1
        self.idle_cmd()
        return trace


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def cocotb_test_scoria_dfi_cmd_path(dut):
    tt = os.environ.get("TEST_TYPE", "never_inserts_an_idle_cycle")
    tb = CmdPathTB(dut)
    fails = []

    def chk(c, m):
        if not c:
            fails.append(m); tb.log.error(m)

    if tt == "never_inserts_an_idle_cycle":
        # THE rule. A stream of mixed ops, nothing structurally blocked: every
        # cycle must accept a command. One inserted idle cycle here rewrites
        # the spacing of everything behind it in the FIFO.
        await tb.setup(rd_phase=2, wr_phase=1)
        ops = [OP_ACT, OP_RD, OP_WR, OP_PRE, OP_REF, OP_RDA, OP_WRA, OP_ACT,
               OP_RD, OP_RD, OP_WR, OP_PREA, OP_ACT, OP_WR, OP_RD]
        words = [pack(o, bank=i % NUM_BANKS, row=0x100 + i, col=8 * i)
                 for i, o in enumerate(ops)]
        trace = await tb.stream(words)
        took = [t for t in trace if t['took']]
        chk(len(took) == len(words),
            f"{len(took)} of {len(words)} commands accepted")
        # The accepted cycles must be CONSECUTIVE from the first.
        cyc = [t['cyc'] for t in trace if t['took']]
        chk(cyc == list(range(cyc[0], cyc[0] + len(words))) if cyc else False,
            f"commands were accepted on cycles {cyc} -- a gap means this layer "
            f"inserted an idle cycle of its own, which rewrites the spacing of "
            f"every command queued behind it (TASK-007: REF to ACT compressed "
            f"15 cycles to 3 on the board)")
        stalls = [t['cyc'] for t in trace[:len(words)] if not t['ready']]
        chk(stalls == [],
            f"cmd_ready_o was low on cycles {stalls} with nothing structurally "
            f"blocked")

    elif tt == "read_holds_only_for_the_aligner":
        # The hold must be op-specific. Applying it to every op turns one
        # structural stall into a general pacer, which is the bug.
        await tb.setup()
        dut.rd_op_ready_i.value = 0
        tb.present(pack(OP_RD, bank=1, col=4))
        await Timer(1, 'ns')
        chk(int(dut.cmd_ready_o.value) == 0,
            "a RD was accepted with the aligner refusing a slot -- the aligner "
            "would lose track of which words belong to which read")
        await tb.tick()
        chk(tb.active_phases() == [],
            f"the RD was placed on the wire anyway (phases "
            f"{tb.active_phases()})")
        # A non-read at the head is unaffected by the READ hold.
        tb.present(pack(OP_ACT, bank=1, row=0x55))
        await Timer(1, 'ns')
        chk(int(dut.cmd_ready_o.value) == 1,
            "an ACT was held by rd_op_ready -- the hold is read-specific, and "
            "generalising it makes this layer a pacer again")
        # Release and the read flows.
        tb.present(pack(OP_RD, bank=1, col=4))
        dut.rd_op_ready_i.value = 1
        await Timer(1, 'ns')
        chk(int(dut.cmd_ready_o.value) == 1,
            "the RD was still held after the aligner freed a slot")
        tb.idle_cmd()

    elif tt == "write_holds_only_for_staged_data":
        await tb.setup()
        dut.wr_op_ready_i.value = 0
        tb.present(pack(OP_WR, bank=2, col=8))
        await Timer(1, 'ns')
        chk(int(dut.cmd_ready_o.value) == 0,
            "a WR was accepted before its data was staged -- the serializer "
            "would drive whatever is in the FIFO")
        chk(int(dut.wr_accept_o.value) == 0,
            "wr_accept_o asserted for a write that was not accepted")
        tb.present(pack(OP_RD, bank=2, col=8))
        await Timer(1, 'ns')
        chk(int(dut.cmd_ready_o.value) == 1,
            "a RD was held by wr_op_ready -- the hold is write-specific")
        tb.idle_cmd()

    elif tt == "column_phase_placement":
        # A column command must land on the phase the PHY expects: rd_phase for
        # reads, wr_phase for writes, phase 0 for everything else. The wrong
        # phase puts the command a quarter-cycle from where the de-interleaver
        # anchors the burst.
        for rd_p, wr_p in ((0, 0), (2, 1), (3, 2)):
            await tb.setup(rd_phase=rd_p, wr_phase=wr_p)
            ph = await tb.drive(pack(OP_RD, bank=1, col=0x20))
            chk(ph == [rd_p], f"rd_phase={rd_p}: the RD landed on phases {ph}")
            ph = await tb.drive(pack(OP_WR, bank=1, col=0x20))
            chk(ph == [wr_p], f"wr_phase={wr_p}: the WR landed on phases {ph}")
            ph = await tb.drive(pack(OP_ACT, bank=1, row=0x33))
            chk(ph == [0],
                f"an ACT landed on phases {ph}, not phase 0 -- only columns "
                f"follow the data phases")

    elif tt == "sub_packing_is_one_cycle":
        # Task #146. Two JEDEC bursts in ONE DFI word: two column commands in
        # ONE cycle, on distinct phases, at col and col+stride. Expanding them
        # over consecutive CYCLES is what left the other phase-pair stale and
        # corrupted 2 of every 4 reads on the board.
        stride_ph, stride_col, base = 2, 4, 0
        await tb.setup(n_subcmd=2, sub_col_stride=stride_col,
                       sub_phase_stride=stride_ph, rd_phase=base, wr_phase=base)
        ph = await tb.drive(pack(OP_RD, bank=1, col=0x10))
        chk(ph == [base, base + stride_ph],
            f"a packed RD drove phases {ph}, expected "
            f"{[base, base + stride_ph]} -- both sub-commands belong in the "
            f"SAME DFI cycle on their own phases")
        if len(ph) == 2:
            a0, a1 = tb.phase_addr(ph[0]), tb.phase_addr(ph[1])
            chk(a1 - a0 == stride_col,
                f"the two subs carry columns 0x{a0:X} and 0x{a1:X}; the second "
                f"must be the first plus sub_col_stride ({stride_col}), or the "
                f"second burst reads the wrong columns")
        # ONE accepted command, ONE fire for the group -- counted from a FRESH
        # setup. The drive() above also fires, and rd_fire_o is registered, so
        # measuring across both reads two strobes for two commands and calls it
        # a doubled group.
        await tb.setup(n_subcmd=2, sub_col_stride=stride_col,
                       sub_phase_stride=stride_ph, rd_phase=base, wr_phase=base)
        trace = await tb.stream([pack(OP_RD, bank=1, col=0x10)])
        chk(sum(t['took'] for t in trace) == 1,
            "a packed group must be one accepted command (one FIFO pop)")
        chk(sum(t['rd_fire'] for t in trace) == 1,
            f"{sum(t['rd_fire'] for t in trace)} rd_fire strobes for one "
            f"packed group -- the data path drives or captures the single DFI "
            f"word once")

    elif tt == "non_column_ops_use_only_sub0":
        # ACT/PRE/REF have no column to fan out. A second sub here would place
        # a duplicate command on another phase -- two activates for one.
        await tb.setup(n_subcmd=2, sub_col_stride=4, sub_phase_stride=2)
        for op in (OP_ACT, OP_PRE, OP_PREA, OP_REF):
            ph = await tb.drive(pack(op, bank=3, row=0x77))
            chk(ph == [0],
                f"op 0x{op:X} with n_subcmd=2 drove phases {ph}; only columns "
                f"fan out")

    elif tt == "runtime_n_subcmd_one_is_single_phase":
        # The build-for-max claim: N_SUBCMD=2 fabric with the RUNTIME value at
        # 1 must behave exactly like the legacy single-command path.
        await tb.setup(n_subcmd=1, sub_col_stride=4, sub_phase_stride=2,
                       rd_phase=1, wr_phase=1)
        ph = await tb.drive(pack(OP_RD, bank=1, col=0x10))
        chk(ph == [1],
            f"with n_subcmd_i=1 the RD drove phases {ph}, expected only the "
            f"base phase -- a fabric sized for packing must be bit-identical "
            f"to the legacy path when the runtime value is 1")
        chk(tb.phase_addr(1) == 0x10,
            f"the single sub carries column 0x{tb.phase_addr(1):X}, not 0x10")
        # And n_subcmd_i=0 is clamped to 1 rather than issuing nothing.
        dut.n_subcmd_i.value = 0
        ph = await tb.drive(pack(OP_RD, bank=1, col=0x10))
        chk(ph == [1],
            f"n_subcmd_i=0 drove phases {ph}; it must clamp to one sub, not "
            f"stop issuing")

    elif tt == "fire_strobes_follow_the_op":
        # The data path schedules off these. A fire on the wrong op class
        # drives or captures a DQ burst that the DRAM is not party to.
        await tb.setup()
        for op, exp_rd, exp_wr in ((OP_RD, 1, 0), (OP_RDA, 1, 0),
                                   (OP_WR, 0, 1), (OP_WRA, 0, 1),
                                   (OP_ACT, 0, 0), (OP_PRE, 0, 0),
                                   (OP_REF, 0, 0)):
            trace = await tb.stream([pack(op, bank=1, row=0x11, col=0x12)])
            rd = sum(t['rd_fire'] for t in trace)
            wr = sum(t['wr_fire'] for t in trace)
            chk((rd, wr) == (exp_rd, exp_wr),
                f"op 0x{op:X}: rd_fire={rd} wr_fire={wr}, expected "
                f"{exp_rd} and {exp_wr}")
            if exp_wr:
                chk(any(t['wr_accept'] for t in trace),
                    f"op 0x{op:X} never asserted wr_accept_o")

    elif tt == "random_soak":
        rng = random.Random(int(os.environ.get('SEED', '53')))
        lvl = os.environ.get("TEST_LEVEL", "FUNC").upper()
        n = {"GATE": 20, "FUNC": 120, "FULL": 400}.get(lvl, 120)
        await tb.setup(rd_phase=2, wr_phase=1)
        ops = [OP_ACT, OP_RD, OP_WR, OP_PRE, OP_REF, OP_RDA, OP_WRA]
        words = [pack(rng.choice(ops), bank=rng.randrange(NUM_BANKS),
                      row=rng.randrange(1 << ROW_WIDTH),
                      col=rng.randrange(1 << COL_WIDTH))
                 for _ in range(n)]
        trace = await tb.stream(words, limit=4 * n + 50)
        took = sum(t['took'] for t in trace)
        chk(took == n, f"{took} of {n} commands accepted")
        cyc = [t['cyc'] for t in trace if t['took']]
        chk(cyc == list(range(cyc[0], cyc[0] + n)) if cyc else False,
            "the accepted cycles are not consecutive -- this layer paced "
            "something")
        # The wire lags the accept by one cycle (strict-flop formatter), so
        # count the DRIVEN cycles rather than pairing them with the accepts.
        driven = [t for t in trace if t['phases']]
        chk(len(driven) == n,
            f"{len(driven)} cycles drove a command for {n} accepted")
        bad = [t['cyc'] for t in driven if len(t['phases']) != 1]
        chk(bad == [],
            f"cycles {bad[:8]} drove more than one phase; at n_subcmd=1 "
            f"exactly one command goes on the wire")
    else:
        raise ValueError(f"Unknown TEST_TYPE: {tt}")

    await tb.wait_clocks('dfi_clk', 3)
    assert not fails, f"{len(fails)} check(s) failed:\n  " + "\n  ".join(fails)


# (case, N_SUBCMD). The packing cases need the two-sub fabric; everything else
# runs on the legacy single-formatter build.
_GATE = [("never_inserts_an_idle_cycle", 1),
         ("column_phase_placement", 1),
         ("sub_packing_is_one_cycle", 2)]
_FUNC = _GATE + [
    ("read_holds_only_for_the_aligner", 1),
    ("write_holds_only_for_staged_data", 1),
    ("non_column_ops_use_only_sub0", 2),
    ("runtime_n_subcmd_one_is_single_phase", 2),
    ("fire_strobes_follow_the_op", 1),
    ("never_inserts_an_idle_cycle", 2),
    ("random_soak", 1),
]
_TEST_LEVEL = (os.environ.get("REG_LEVEL") or os.environ.get("TEST_LEVEL")
               or "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FUNC}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type, n_subcmd", _PARAMS)
def test_scoria_dfi_cmd_path(request, test_type, n_subcmd):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "scoria_dfi_cmd_path"
    test_name = f"test_scoria_dfi_cmd_path_{test_type}_s{n_subcmd}"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/"
                       "rtl/filelists/fub/scoria_dfi_cmd_path.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True); os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_scoria_dfi_cmd_path",
        sim_build=sim_build, simulator="verilator",
        # The RTL guards N_SUBCMD * SUB_PHASE_STRIDE == DFI_RATE at elaboration
        # ("sub-word anchors do not tile the DFI cycle"), so the stride is a
        # PARAMETER as well as a runtime input and the two must agree. Leaving
        # the parameter at its default of 1 makes a two-sub build refuse to
        # elaborate -- which is the guard doing its job.
        parameters={"NUM_BANKS": str(NUM_BANKS), "ROW_WIDTH": str(ROW_WIDTH),
                    "COL_WIDTH": str(COL_WIDTH), "DFI_RATE": str(DFI_RATE),
                    "N_SUBCMD": str(n_subcmd),
                    "SUB_PHASE_STRIDE": str(DFI_RATE // n_subcmd),
                    "SUB_COL_STRIDE": "4"},
        extra_env={"DUT": dut_name, "TEST_TYPE": test_type,
                   "N_SUBCMD": str(n_subcmd), "TEST_LEVEL": _TEST_LEVEL,
                   "COCOTB_LOG_LEVEL": "INFO",
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET"],
        keep_files=True, timescale="1ns/1ps")
