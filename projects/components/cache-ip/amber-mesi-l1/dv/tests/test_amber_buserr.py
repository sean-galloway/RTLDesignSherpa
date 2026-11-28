"""
amber bus-error reporting -- directed + random test (cache-ip/amber-mesi-l1
TASK-008, for riscv-ip/peregrine-rv32im TASK-005).

amber_top at BUS_ERR_EN=1 (MAINT_EN=1, USE_MONITOR=0) on the house AXI4
slave BFMs with error windows (tbclasses/amber_buserr_tb.py):

  failed fill    a read miss whose fill is DECERR / SLVERR is answered with
                 the error bit and installs nothing (the next read misses
                 again); the victim way it overwrote is invalid (one of the
                 set's old lines refills, the others still hit); a write
                 miss's write-allocate fill likewise, memory untouched;
                 READ_FILL_E=0: a failed CleanUnique upgrade answers the
                 store with the error and leaves the line S, data intact
  failed WB      an evicted dirty line whose write-back is SLVERR is
                 dropped: wb_err_valid with its line address, the request
                 that evicted it answered OKAY, the line reads memory's
                 data again; a second failure sets wb_err_ovf and keeps the
                 first address; wb_err_clear clears both
  failed clean   a clean-all whose WriteCleans fail answers OKAY, ends,
                 latches the first failed line (overflow for the second),
                 drops the failed lines, and still writes a good dirty line
  OKAY traffic   (func/full) random reads/writes over good lines, every
                 response err=0 and every read against the scoreboard

Grid: READ_FILL_E 0/1 x gate/func/full; func/full use the randomized
memory timing profile.

Author: RTL Design Sherpa
Created: 2026-11-27
"""

import os
import sys

import cocotb
import pytest
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid
from TBClasses.shared.utilities import get_paths, get_repo_root, sim_build_path

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.cache_ip.amber_mesi_l1.dv.tbclasses.amber_buserr_tb import (  # noqa: E402
    RD_DECERR, RD_SLVERR, WR_ONLY, AmberBusErrTB,
)

FILELIST = 'projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_top.f'
GEOM = dict(SETS=16, WAYS=4, LINE_BYTES=64, BUS_WIDTH=64)
GOOD = 0x0


@cocotb.test(timeout_time=3000, timeout_unit="ms")
async def cocotb_test_amber_buserr(dut):
    level = os.environ.get("TEST_LEVEL", "gate")
    fill_e = int(os.environ.get("READ_FILL_E", "0"))
    seed = int(os.environ.get("RDS_SEED_BASE", "1"))
    tb = AmberBusErrTB(dut, GEOM["SETS"], GEOM["WAYS"], GEOM["LINE_BYTES"],
                       GEOM["BUS_WIDTH"], seed)
    await tb.setup()
    tb.set_profile("fast" if level == "gate" else "normal")
    log = dut._log
    a = tb.addr

    # -- failed read fill ------------------------------------------------
    bad = a(RD_DECERR, 1, 0, 8)
    n = tb.ars
    await tb.read(bad, err=1)
    await tb.read(bad, err=1)                    # not installed: misses again
    assert tb.ars - n == 2, f"failed fill: {tb.ars - n} ARs, expected 2"
    await tb.read(a(RD_SLVERR, 1, 1, 16), err=1)

    # The victim way the failed fill overwrote is invalid: fill set 2 with
    # WAYS good lines, fail a fill there, then exactly one old line refills.
    olds = [a(GOOD, 2, t) for t in range(GEOM["WAYS"])]
    for o in olds:
        await tb.read(o)
    await tb.read(a(RD_DECERR, 2, 7), err=1)
    n = tb.ars
    for o in olds:
        await tb.read(o)
    assert tb.ars - n == 1, f"victim of a failed fill: {tb.ars - n} refills, expected 1"

    # -- failed write-allocate fill ---------------------------------------
    wbad = a(RD_DECERR, 3, 2, 24)
    before = tb.mem_word(wbad)
    n_aw = tb.aws
    await tb.write(wbad, 0x1111_2222_3333_4444, err=1)
    await tb.read(wbad, err=1)
    assert tb.mem_word(wbad) == before, "a failed write-allocate changed memory"

    # -- failed CleanUnique upgrade (read fills install S) -----------------
    if not fill_e:
        up = a(GOOD, 4, 3, 0)
        await tb.read(up)                        # S
        tb.extra_bad.add(up - up % GEOM["LINE_BYTES"])
        n = tb.ars
        await tb.write(up, 0xAAAA_BBBB_CCCC_DDDD, err=1)
        assert tb.ars - n == 1, "the upgrade issued no CleanUnique"
        tb.extra_bad.clear()
        n = tb.ars
        await tb.read(up)                        # still installed, old data
        assert tb.ars == n, "a failed upgrade dropped the S line"

    assert tb.aws == n_aw, "a failed fill wrote back"
    assert tb.wb_err() == (0, 0, 0), f"wb_err raised by fill errors: {tb.wb_err()}"

    # -- failed eviction write-back ---------------------------------------
    wl = a(WR_ONLY, 5, 0, 8)
    await tb.write(wl, 0x5555_6666_7777_8888)    # write-allocate fill OKAY: M
    await tb.read(wl)                            # the cache has it
    for t in range(1, GEOM["WAYS"] + 2):         # evict it
        await tb.read(a(GOOD, 5, t))
    assert tb.wb_err() == (1, wl - wl % 64, 0), f"eviction WB error: {tb.wb_err()}"
    tb.drop_line(wl)
    n = tb.ars
    await tb.read(wl)                            # dropped: memory's old data
    assert tb.ars - n == 1, "the dropped line was still installed"

    # A second failure while valid: overflow, the first address kept.
    wl2 = a(WR_ONLY, 6, 0, 0)
    await tb.write(wl2, 0x9999_0000_9999_0000)
    for t in range(1, GEOM["WAYS"] + 2):
        await tb.read(a(GOOD, 6, t))
    assert tb.wb_err() == (1, wl - wl % 64, 1), f"overflow: {tb.wb_err()}"
    tb.drop_line(wl2)
    await tb.clear()
    assert tb.wb_err()[0::2] == (0, 0), f"clear: {tb.wb_err()}"

    # -- failed clean-all write-backs -------------------------------------
    c1, c2, good = a(WR_ONLY, 7, 1, 0), a(WR_ONLY, 9, 1, 8), a(GOOD, 8, 5, 16)
    await tb.write(c1, 0x0101_0101_0101_0101)
    await tb.write(good, 0x0202_0202_0202_0202)
    await tb.write(c2, 0x0303_0303_0303_0303)
    await tb.clean_all()
    assert tb.wb_err() == (1, c1 - c1 % 64, 1), f"clean-all WB errors: {tb.wb_err()}"
    assert tb.mem_word(good) == 0x0202_0202_0202_0202, "the good line was not cleaned"
    tb.drop_line(c1)
    tb.drop_line(c2)
    n = tb.ars
    await tb.read(c1)                            # dropped
    await tb.read(c2)
    await tb.read(good)                          # cleaned, still installed
    assert tb.ars - n == 2, f"after the clean: {tb.ars - n} refills, expected 2"
    await tb.clean_all()                         # nothing dirty: no new error
    assert tb.wb_err() == (1, c1 - c1 % 64, 1)
    await tb.clear()
    assert tb.wb_err()[0::2] == (0, 0)

    # -- OKAY traffic ------------------------------------------------------
    if level != "gate":
        ops = 1500 if level == "func" else 8000
        rng = tb.rng
        lines = [a(GOOD, s, t) for s in range(GEOM["SETS"]) for t in range(8)]
        for _ in range(ops):
            x = rng.choice(lines) + 8 * rng.randrange(8)
            if rng.random() < 0.4:
                await tb.write(x, rng.getrandbits(64), be=rng.randrange(1, 256))
            else:
                await tb.read(x)
            if rng.random() < 0.005:
                await tb.clean_all()
        await tb.clean_all()
        for w, v in tb.shadow.items():
            if (w >> 16) & 0xF == GOOD:
                assert tb.mem_word(w) == v, f"memory 0x{w:x} after the last clean"
        assert tb.wb_err()[0] == 0, f"OKAY traffic raised a write-back error: {tb.wb_err()}"
        log.info(f"OKAY traffic: {ops} ops, seed {seed}")
    log.info(f"amber bus errors (READ_FILL_E={fill_e}, {level}): {tb.checks} reads "
             f"checked, {tb.ars} ARs, {tb.aws} AWs")


@pytest.mark.parametrize("fill_e", [0, 1])
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_amber_buserr(request, fill_e, test_level):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    name = f"cocotb_test_amber_buserr_e{fill_e}_{test_level}"
    log_path = os.path.join(log_dir, f"{name}.log")
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root,
                                                          filelist_path=FILELIST)
    params = {k: str(v) for k, v in GEOM.items()}
    params.update(MAINT_EN="1", BUS_ERR_EN="1", USE_MONITOR="0",
                  READ_FILL_E=str(fill_e))
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel="amber_top",
        module=module,
        testcase="cocotb_test_amber_buserr",
        parameters=params,
        sim_build=sim_build,
        extra_env={
            "DUT": "amber_top",
            "LOG_PATH": log_path,
            "COCOTB_LOG_LEVEL": "INFO",
            "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{name}.xml"),
            "READ_FILL_E": str(fill_e),
            **level_env(test_level),
        },
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        compile_args=["--timescale", "1ns/1ps", "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND"],
    )
