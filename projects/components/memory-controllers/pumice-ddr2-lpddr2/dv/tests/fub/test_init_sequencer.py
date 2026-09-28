# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Unit-test runner for `init_sequencer`. Walks the JEDEC DDR2 init FSM from
RESET through DONE, verifies dfi_init_start_o asserts, and verifies the full
mode-register write sequence:

    EMRS(2) EMRS(3) EMRS(1) -> MRS(0)+DLL-reset -> [PREA, REF x2]
    -> MRS(0) -> EMRS(1) OCD exit

DDR2 has no ZQ calibration, so zqcl_req_o stays low (ZQCL is DDR3+).
"""

import os
import sys
import random
import pytest

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.tbbase import TBBase

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from pumice_coverage import (  # noqa: E402
    get_coverage_compile_args, get_coverage_env,
)

from tbclasses.trackers import InitSequencerTracker  # noqa: E402


MEMTYPE_DDR2   = 0
MEMTYPE_LPDDR2 = 1

# DDR2 MR values are now CSR-backed inputs (mr0_i..mr3_i, driven from MR0..MR3.
# VAL). The TB drives the RDL default set (BL8/CL3/tWR3); the FSM ORs in the DLL
# reset bit (A8) for the first MRS(0) load and leaves the rest verbatim.
DDR2_MR0_BASE    = 0x0433   # MR0 base (BL8/CL3/tWR3) — the CSR default
DDR2_DLL_RESET   = 0x0100   # A8 OR'd in by the FSM for the first MRS(0)
DDR2_MR0_DLL     = DDR2_MR0_BASE | DDR2_DLL_RESET  # first MRS(0) = 0x0533
DDR2_MR0         = DDR2_MR0_BASE                    # second MRS(0) = 0x0433
DDR2_MR1_DEFAULT = 0x0000
DDR2_MR2_DEFAULT = 0x0000
DDR2_MR3_DEFAULT = 0x0000

# Full JEDEC DDR2 mode-register write sequence (index, data), in FSM order.
# JESD79-2 order: EMRS(2), EMRS(3), EMRS(1), MRS(0)+DLL-reset, then (after
# PREA + REF x2) MRS(0), and EMRS(1) OCD-exit.
# (S_OCD_DEF issues the OCD-default EMRS but intentionally leaves the shadow
#  untouched, so it emits no mr_seq_we strobe.)
DDR2_MR_SEQUENCE = [
    (2, DDR2_MR2_DEFAULT),
    (3, DDR2_MR3_DEFAULT),
    (1, DDR2_MR1_DEFAULT),
    (0, DDR2_MR0_DLL),
    (0, DDR2_MR0),
    (1, DDR2_MR1_DEFAULT),
]


# Opcodes, from pumice_pkg.sv.
OP_PREA, OP_REF, OP_MRS = 0x7, 0x8, 0xA

# THE JEDEC DDR2 POWER-UP SEQUENCE, JESD79-2F section 3.3 "Power-up and
# Initialization", as (op, mr_index_or_None). `bank` carries the MR index on an
# MRS and is don't-care otherwise.
#
# Nothing in this repo asserted this ORDER on the command bus before: the
# existing walk checks the six MR-write strobes, which cannot see the PRECHARGE
# ALL and the two REFRESHes that JEDEC places between them, nor their position
# relative to the MR writes. Getting that order wrong is a real and historical
# failure mode here -- the MRS chain itself shipped as EMRS3-before-EMRS2 until
# 64fb2137, benign only because MR2/MR3 happen to be 0 on this part.
DDR2_INIT_CMD_SEQUENCE = [
    (OP_PREA, None),   # precharge all, pre-EMR
    (OP_MRS,  2),      # EMRS(2)
    (OP_MRS,  3),      # EMRS(3)
    (OP_MRS,  1),      # EMRS(1) -- enable DLL
    (OP_MRS,  0),      # MRS(0)  -- with DLL reset (A8)
    (OP_PREA, None),   # precharge all, pre-refresh
    (OP_REF,  None),   # refresh 1 of 2
    (OP_REF,  None),   # refresh 2 of 2
    (OP_MRS,  0),      # MRS(0)  -- DLL reset cleared
    (OP_MRS,  1),      # EMRS(1) -- OCD calibration default
    (OP_MRS,  1),      # EMRS(1) -- OCD calibration exit
]

# Which wait register gates the gap AFTER each command above, from the FSM's
# own r_wait assignments in init_sequencer.sv.
DDR2_INIT_GAP_SOURCE = ['rp', 'mrd', 'mrd', 'mrd', 'dll',
                        'rp', 'rfc', 'rfc', 'mrd', 'mrd', 'mrd']


class InitTB(TBBase):
    CLK = 10

    async def setup(self, memtype: int = MEMTYPE_DDR2,
                    mr0: int = DDR2_MR0_BASE, mr1: int = DDR2_MR1_DEFAULT,
                    mr2: int = DDR2_MR2_DEFAULT, mr3: int = DDR2_MR3_DEFAULT,
                    waits: dict = None):
        self.dut.memtype_i.value             = memtype
        self.dut.dfi_init_complete_i.value   = 0
        self.dut.zqcl_grant_i.value          = 0
        # CSR-backed mode-register values (MR0..MR3.VAL) + init restart control.
        self.dut.mr0_i.value          = mr0
        self.dut.mr1_i.value          = mr1
        self.dut.mr2_i.value          = mr2
        self.dut.mr3_i.value          = mr3
        self.dut.init_restart_i.value = 0
        # JEDEC timing waits. Default ZERO so the FSM advances one state per
        # S_WAIT bounce, which keeps the existing walks deterministic and fast.
        #
        # This comment used to claim "the real tINIT/tRFC/tDLLK budgets are
        # exercised at the macro/top level". They were not -- at ANY level. Every
        # environment zeroed them for speed, so the sequencer's use of its own
        # wait registers was unverified everywhere (pumice TASK-016). The
        # `waits` argument exists for the test that closes that hole; passing
        # nothing keeps the old behaviour exactly.
        w = waits or {}
        self.dut.t_init_wait_i.value = w.get('init', 0)
        self.dut.t_dll_wait_i.value  = w.get('dll', 0)
        self.dut.t_mrd_wait_i.value  = w.get('mrd', 0)
        self.dut.t_rp_wait_i.value   = w.get('rp', 0)
        self.dut.t_rfc_wait_i.value  = w.get('rfc', 0)
        await self.start_clock('mc_clk', freq=self.CLK, units='ns')
        self.dut.mc_rst_n.value = 0
        await self.wait_clocks('mc_clk', 5)
        self.dut.mc_rst_n.value = 1
        await self.wait_clocks('mc_clk', 5)

    def init_start(self) -> int:
        return int(self.dut.dfi_init_start_o.value)

    def init_busy(self) -> int:
        return int(self.dut.init_busy_o.value)

    def init_done(self) -> int:
        return int(self.dut.init_done_o.value)

    def mr_we(self) -> int:
        return int(self.dut.mr_seq_we_o.value)

    def mr_idx(self) -> int:
        return int(self.dut.mr_seq_index_o.value)

    def mr_data(self) -> int:
        return int(self.dut.mr_seq_data_o.value)

    def zqcl_req(self) -> int:
        return int(self.dut.zqcl_req_o.value)

    async def restart(self, waits: dict):
        """Re-run the init sequence on an EXISTING TB, with new wait values.

        Deliberately NOT a second `setup()`. Constructing a second InitTB, or
        calling setup() again, starts a SECOND clock driver on the same mc_clk
        -- two coroutines driving one signal -- and re-opens the TB's log file,
        truncating whatever the first run had already recorded. The first
        version of the wait-scaling test below did exactly that, and the
        symptom was the sequence-match evidence vanishing from the log while
        the test still passed.
        """
        w = waits or {}
        self.dut.t_init_wait_i.value = w.get('init', 0)
        self.dut.t_dll_wait_i.value  = w.get('dll', 0)
        self.dut.t_mrd_wait_i.value  = w.get('mrd', 0)
        self.dut.t_rp_wait_i.value   = w.get('rp', 0)
        self.dut.t_rfc_wait_i.value  = w.get('rfc', 0)
        self.dut.dfi_init_complete_i.value = 0
        self.dut.mc_rst_n.value = 0
        await self.wait_clocks('mc_clk', 5)
        self.dut.mc_rst_n.value = 1
        await self.wait_clocks('mc_clk', 5)

    async def capture_cmd_stream(self, max_cycles: int = 4000):
        """Capture the COMMAND stream the sequencer issues, with cycle stamps.

        `capture_mr_seq` watches the mode-register shadow strobes, which is a
        different thing: it sees the six MR writes but not the PRECHARGE ALL and
        REFRESH commands that JEDEC interleaves between them, and not the gaps.
        Those are the parts nothing checked (pumice TASK-016).

        Stops once init_done_o rises, so it costs only what the sequence costs.
        """
        seen, cyc = [], 0
        for _ in range(max_cycles):
            await RisingEdge(self.dut.mc_clk)
            await Timer(1, units='ps')
            cyc += 1
            if int(self.dut.init_cmd_valid_o.value):
                seen.append(dict(cycle=cyc,
                                 op=int(self.dut.init_cmd_op_o.value),
                                 bank=int(self.dut.init_cmd_bank_o.value),
                                 row=int(self.dut.init_cmd_row_o.value)))
            if self.init_done():
                break
        return seen

    async def capture_mr_seq(self, max_cycles: int = 20):
        """Watch for MR write strobes; return list of (index, data) seen."""
        seen = []
        for _ in range(max_cycles):
            await RisingEdge(self.dut.mc_clk)
            await Timer(1, units='ps')
            if self.mr_we():
                seen.append((self.mr_idx(), self.mr_data()))
        return seen


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_init_sequencer(dut):
    test_type = os.environ.get("TEST_TYPE", "ddr2_init_walk")
    tb = InitTB(dut)
    # Tracker auto-dumps <sim_build>/init.out at end of sim.
    init_tracker = InitSequencerTracker(dut)
    cocotb.start_soon(init_tracker.run())

    if test_type == "ddr2_init_walk":
        await tb.setup(MEMTYPE_DDR2)
        # After reset deassertion, dfi_init_start_o should be high.
        await tb.wait_clocks('mc_clk', 1)
        assert tb.init_start() == 1
        assert tb.init_busy() == 1
        assert tb.init_done() == 0
        # PHY completes init -> FSM walks the full JEDEC MRS sequence.
        tb.dut.dfi_init_complete_i.value = 1
        # Capture the whole sequence (6 MRS strobes; each state pairs with an
        # S_WAIT bounce, and the mid-sequence PREA/REF states add cycles).
        seen = await tb.capture_mr_seq(max_cycles=40)
        assert seen == DDR2_MR_SEQUENCE, (
            f"MR seq mismatch: got {seen}, want {DDR2_MR_SEQUENCE}"
        )
        # DDR2 has no ZQ calibration — zqcl_req must stay low throughout.
        assert tb.zqcl_req() == 0, "zqcl_req asserted for DDR2 (should be DDR3+ only)"
        # FSM reaches DONE after the last MRS.
        for _ in range(20):
            await tb.wait_clocks('mc_clk', 1)
            if tb.init_done():
                break
        assert tb.init_done() == 1, "init_sequencer never reached DONE"
        assert tb.init_busy() == 0

    elif test_type == "wait_for_complete":
        await tb.setup(MEMTYPE_DDR2)
        await tb.wait_clocks('mc_clk', 1)
        assert tb.init_start() == 1
        # Don't assert dfi_init_complete; init should stay busy
        await tb.wait_clocks('mc_clk', 30)
        assert tb.init_busy() == 1
        assert tb.init_done() == 0

    elif test_type == "lpddr2_smoke":
        await tb.setup(MEMTYPE_LPDDR2)
        await tb.wait_clocks('mc_clk', 1)
        assert tb.init_start() == 1
        tb.dut.dfi_init_complete_i.value = 1
        # LPDDR2 JEDEC init (JESD209-2F): MRW Reset(MR63) -> ZQ(MR10) ->
        # MR1/MR2/MR3. Only MR1/MR2/MR3 update the CL/CWL/BL decode shadow;
        # MR63/MR10 are issued to the DRAM but not shadowed. See init_sequencer.sv
        # LPDDR2_MR{1,2,3}_OP.
        expected_lpddr2 = {
            1: 0x23,   # BL8, nWR=3
            2: 0x01,   # RL3/WL1
            3: 0x02,   # DS 40ohm
        }
        seen = await tb.capture_mr_seq(max_cycles=20)
        seen_map = dict(seen)
        for idx, val in expected_lpddr2.items():
            assert seen_map.get(idx) == val, (
                f"LPDDR2 MR{idx} got {seen_map.get(idx)} want {val:#x} (seen={seen})"
            )
        tb.dut.zqcl_grant_i.value = 1
        await tb.wait_clocks('mc_clk', 5)
        assert tb.init_done() == 1

    elif test_type == "random_soak":
        # Soak the init flow by repeatedly pulsing reset and walking the
        # init sequence with random PHY-complete / ZQCL-grant delays.
        # Clock is started only once (via the initial setup); subsequent
        # iterations toggle mc_rst_n manually rather than calling setup()
        # again (which would spawn duplicate clock coroutines).
        rng = random.Random(int(os.environ.get('SEED', '12345')))
        test_level = os.environ.get("TEST_LEVEL", "FUNC").upper()
        n = {"GATE": 8, "FUNC": 40, "FULL": 200}.get(test_level, 40)

        await tb.setup(MEMTYPE_DDR2)   # starts clock + initial reset
        for _ in range(n):
            memtype = rng.choice([MEMTYPE_DDR2, MEMTYPE_LPDDR2])
            tb.dut.memtype_i.value           = memtype
            tb.dut.dfi_init_complete_i.value = 0
            tb.dut.zqcl_grant_i.value        = 0
            # Pulse reset to restart the init FSM.
            tb.dut.mc_rst_n.value = 0
            await tb.wait_clocks('mc_clk', 3)
            tb.dut.mc_rst_n.value = 1
            await tb.wait_clocks('mc_clk', rng.randint(2, 6))
            # Variable PHY-complete delay, then let the FSM run to DONE. The
            # full DDR2 JEDEC walk (PREA, EMRS x3, MRS0+DLL, PREA, REF x2, MRS0,
            # OCD default+exit) is ~24 cycles with zero timing waits; LPDDR2 is
            # shorter. Poll rather than assume a fixed cycle count.
            await tb.wait_clocks('mc_clk', rng.randint(0, 4))
            tb.dut.dfi_init_complete_i.value = 1
            for _ in range(48):
                await tb.wait_clocks('mc_clk', 1)
                if tb.init_done():
                    break
            assert tb.init_done() == 1, f"init not done with memtype={memtype}"

    elif test_type == "mr_restart":
        # CSR-backed MR values + CTRL.init_force_restart. Drives a CUSTOM MR0
        # (as software would when sweeping to defeat an arbitrary board A-lane
        # mapping) and verifies (a) the custom value is emitted on the MRS chain,
        # and (b) init_force_restart re-runs the chain WITHOUT a reset, picking
        # up a freshly-changed MR0 — the runtime re-init path the sweep needs.
        CUSTOM_MR0 = 0x0451
        await tb.setup(MEMTYPE_DDR2, mr0=CUSTOM_MR0)
        await tb.wait_clocks('mc_clk', 1)
        assert tb.init_start() == 1
        tb.dut.dfi_init_complete_i.value = 1
        seen = await tb.capture_mr_seq(max_cycles=40)
        assert (0, CUSTOM_MR0 | DDR2_DLL_RESET) in seen, \
            f"first MRS(0) not custom-with-DLL: got {seen}"
        assert (0, CUSTOM_MR0) in seen, f"second MRS(0) not custom: got {seen}"
        for _ in range(20):
            await tb.wait_clocks('mc_clk', 1)
            if tb.init_done():
                break
        assert tb.init_done() == 1, "custom-MR0 init never reached DONE"

        # Change MR0 and pulse init_force_restart (NO mc_rst_n toggle): the FSM
        # must re-enter init and re-emit the NEWEST MR0.
        NEW_MR0 = 0x0466
        tb.dut.mr0_i.value = NEW_MR0
        tb.dut.init_restart_i.value = 1
        await tb.wait_clocks('mc_clk', 2)
        tb.dut.init_restart_i.value = 0
        assert tb.init_busy() == 1, "init_force_restart did not re-enter init"
        assert tb.init_done() == 0
        seen2 = await tb.capture_mr_seq(max_cycles=40)
        assert (0, NEW_MR0 | DDR2_DLL_RESET) in seen2, \
            f"restart did not re-emit new MR0-with-DLL: got {seen2}"
        assert (0, NEW_MR0) in seen2, f"restart did not re-emit new MR0: got {seen2}"

    elif test_type == "ddr2_init_command_stream":
        # pumice TASK-016. Two questions nothing answered at any level:
        #   (1) does the sequencer issue the JEDEC command sequence, in order,
        #       INCLUDING the precharges and refreshes the MR-strobe walk cannot
        #       see; and
        #   (2) does it actually honour its own wait registers?
        #
        # (2) cannot be asked by comparing against datasheet numbers, because no
        # simulation can afford the real ones -- 200 us of tINIT at 100 MHz is
        # 20,000 cycles before the sequence even starts. So it is asked
        # DIFFERENTIALLY instead: run the same sequence at two wait settings and
        # require every gap to grow by exactly the amount its wait register grew.
        # That needs no model of the FSM's fixed per-state overhead, and it is
        # the check that would catch a sequencer ignoring a wait register --
        # which is the failure mode that matters, since a wait wired to nothing
        # looks identical to a wait set to zero.
        ops = {OP_PREA: 'PREA', OP_REF: 'REF', OP_MRS: 'MRS'}

        first = [True]

        async def run_once(waits):
            # ONE TB for both runs -- see InitTB.restart for why a second one
            # is wrong.
            if first[0]:
                await tb.setup(MEMTYPE_DDR2, waits=waits)
                first[0] = False
            else:
                await tb.restart(waits)
            await tb.wait_clocks('mc_clk', 1)
            tb.dut.dfi_init_complete_i.value = 1
            stream = await tb.capture_cmd_stream()
            assert tb.init_done() == 1, (
                f"init never completed with waits={waits}; captured "
                f"{len(stream)} commands")
            return stream

        base_w = dict(init=0, dll=4, mrd=2, rp=3, rfc=6)
        stream_a = await run_once(base_w)

        got = [(c['op'], c['bank'] if c['op'] == OP_MRS else None)
               for c in stream_a]
        assert got == DDR2_INIT_CMD_SEQUENCE, (
            "DDR2 init command sequence does not match JESD79-2F 3.3.\n"
            "  got : " + " -> ".join(
                f"{ops.get(o, o)}" + (f"({i})" if i is not None else "")
                for o, i in got) + "\n"
            "  want: " + " -> ".join(
                f"{ops.get(o, o)}" + (f"({i})" if i is not None else "")
                for o, i in DDR2_INIT_CMD_SEQUENCE))
        tb.log.info("init command sequence matches JESD79-2F 3.3: %s",
                    " -> ".join(f"{ops.get(o, o)}" + (f"({i})" if i is not None else "")
                                for o, i in got))

        # Second run: bump every wait by a DIFFERENT amount, so a gap that
        # tracks the wrong register is caught too, not just one that tracks
        # nothing.
        bump = dict(init=0, dll=7, mrd=5, rp=9, rfc=11)
        stream_b = await run_once(bump)
        assert len(stream_b) == len(stream_a), (
            f"the two runs issued different command counts "
            f"({len(stream_a)} vs {len(stream_b)})")

        gaps_a = [stream_a[i + 1]['cycle'] - stream_a[i]['cycle']
                  for i in range(len(stream_a) - 1)]
        gaps_b = [stream_b[i + 1]['cycle'] - stream_b[i]['cycle']
                  for i in range(len(stream_b) - 1)]
        bad = []
        for i, (ga, gb) in enumerate(zip(gaps_a, gaps_b)):
            src = DDR2_INIT_GAP_SOURCE[i]
            want_delta = bump[src] - base_w[src]
            got_delta = gb - ga
            if got_delta != want_delta:
                after = DDR2_INIT_CMD_SEQUENCE[i]
                bad.append(
                    f"gap after {ops.get(after[0], after[0])}"
                    f"{('(' + str(after[1]) + ')') if after[1] is not None else ''}"
                    f" is gated by t_{src}_wait: raising it by {want_delta} "
                    f"changed the gap by {got_delta} ({ga} -> {gb})")
        assert not bad, (
            "the init sequencer does not honour its wait registers:\n  "
            + "\n  ".join(bad))
        tb.log.info("all %d inter-command gaps scale exactly with their wait "
                    "registers (rp/mrd/dll/rfc); gaps run1=%s run2=%s",
                    len(gaps_a), gaps_a, gaps_b)

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")

    await tb.wait_clocks('mc_clk', 3)


_GATE = [("ddr2_init_walk",), ("ddr2_init_command_stream",)]
_FUNC = _GATE + [("wait_for_complete",), ("lpddr2_smoke",),
                 ("mr_restart",), ("random_soak",)]
_FULL = _FUNC

# REG_LEVEL SELECTS THIS GRID. It used to read TEST_LEVEL, which held the
# regression level only because the area conftest stamped REG_LEVEL into it --
# and that stamp also overrode every per-cell value a wrapper exported, which is
# TOOL-016. The stamp is gone, so REG_LEVEL is read here directly. TEST_LEVEL
# stays as a manual override for a bare `pytest` run.
_TEST_LEVEL = (os.environ.get("REG_LEVEL") or os.environ.get("TEST_LEVEL")
               or "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", [t[0] for t in _PARAMS],
                         ids=[t[0] for t in _PARAMS])
def test_init_sequencer(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "init_sequencer"
    test_name = f"test_init_sequencer_{test_type}"

    filelist_path = ("projects/components/memory-controllers/pumice-ddr2-lpddr2/"
                     "rtl/filelists/fub/init_sequencer.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": test_type,
        "SEED": os.environ.get('SEED', str(random.randint(0, 100000))),
        # The simulator's depth comes from here now; no conftest stamps it.
        "TEST_LEVEL": _TEST_LEVEL,
        "COCOTB_LOG_LEVEL": "INFO",
        # Persist the TB log. Without this the sequence this test verifies is
        # printed to a stdout that pytest swallows on success, so a passing run
        # left no record of WHAT it checked -- which is the same blind-verdict
        # problem the checkers elsewhere in this suite are guarded against.
        "LOG_PATH": os.path.join(log_dir, f"{test_name}.log"),
        "COCOTB_RESULTS_FILE":
            os.path.join(log_dir, f"results_{test_name}.xml"),
    }

    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    compile_args = ["+define+USE_ASYNC_RESET"]
    sim_args = []
    plus_args = []
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs", "--trace-depth", "99"]
        sim_args     += ["--trace", "--trace-structs", "--trace-depth", "99"]
        plus_args    += ["--trace"]
        extra_env["VERILATOR_TRACE_FST"] = "1"

    compile_args += get_coverage_compile_args()
    extra_env.update(get_coverage_env(test_name, sim_build=sim_build))

    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module,
        testcase="cocotb_test_init_sequencer",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")
