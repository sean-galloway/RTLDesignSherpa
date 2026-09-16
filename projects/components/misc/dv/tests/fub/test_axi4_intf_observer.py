# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Component-level test for axi4_intf_{master,slave}_observer.

The observers had NO component DV. Both were exercised only through a
20-minute full-harness build in another project, which is how a block whose
monitors were built DISABLED, whose reporter cones were compiled OUT, and whose
26 config inputs were tied to constants stayed green for months.

This test asserts the register layer, which is where all of that was visible:

  1. OBS_CAPS0/1/2 must REPORT what the instance was built with. A capability
     register that disagrees with its own parameters is worse than none -- it
     is a confident wrong answer, and software reads it to decide whether a
     zero counter means "quiet" or "not built".
  2. Config registers must round-trip. Every one of them replaced a hardcoded
     constant; if a write does not stick, the block silently keeps the old
     tie-off behaviour and nothing says so.
  3. Reset values must equal the constants they replaced, so adding the
     registers stayed behaviour-neutral for existing consumers (Genesys 2
     stream, NexysA7 pumice).

Both observers run the SAME body: they share obs_regs.rdl, and the register map
is precisely what must not drift between them.
"""

import hashlib
import os
import sys

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, get_repo_root, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import current_level, level_env, reg_level_grid

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.misc.dv.tbclasses.axi4_intf_observer_tb import AXI4IntfObserverTB  # noqa: E402
from TBClasses.monbus.monbus_types import AXIErrorCode, PktType  # noqa: E402


def _p(name, default):
    return int(os.environ.get(name, default))


@cocotb.test(timeout_time=200, timeout_unit="us")
async def cocotb_test_observer_regs(dut):
    """Capability reporting, config round-trip and reset values.

    Graded: gate proves the bus, the capability contract and the reset
    values; func adds the config round-trip; full adds the read-only sweep.
    """
    _lvl = current_level()
    tb = AXI4IntfObserverTB(dut)
    await tb.setup_clocks_and_reset()

    # ---- 0. prove the BUS before trusting any value ----------------------
    # OBS_BASE_ADDR resets to 0x0004_0000. If this reads 0 the APB window is
    # dead and every other zero in this test means nothing -- distinguishing
    # "register reads 0" from "read never landed" has to come first.
    base = await tb.read_reg("OBS_BASE_ADDR")
    assert base == 0x0004_0000, (
        f"OBS_BASE_ADDR reads 0x{base:08X}, expected its reset 0x00040000. "
        f"The observer APB window is not responding -- nothing else in this "
        f"test can be interpreted until that is fixed.")
    tb.log.info(f"APB alive: OBS_BASE_ADDR=0x{base:08X}")

    # ---- 0b. hwif_in probe: does ANY hardware-driven register read back? --
    # OBS_BASE_ADDR above is sw=rw and reads from STORAGE. Every register below
    # is sw=r/hw=w and reads straight from hwif_in. If storage reads correctly
    # and all of these read 0, the hwif_in path into the regblock is dead --
    # which would be a pre-existing defect these registers merely exposed, not
    # something the new registers caused.
    #
    # OBS_CAPS0 is the decisive one: it is driven by PARAMETERS, so it cannot
    # legitimately be 0 for ANY build. ENABLE_BUS_METER alone defaults to 1'b1,
    # which sets bit 7. The activity-driven ones (FIFO_STAT, STICKY, COMP_*)
    # may honestly read 0 on an idle DUT, so they are logged, not asserted.
    probe = {}
    for name in ("OBS_STAT_DATA", "OBS_FIFO_STAT", "OBS_STICKY",
                 "OBS_COMP_STAT0", "OBS_COMP_STAT1",
                 "OBS_CAPS0", "OBS_CAPS1", "OBS_CAPS2"):
        probe[name] = await tb.read_reg(name)
    tb.log.info("hwif_in probe (all sw=r/hw=w): "
                + " ".join(f"{k}=0x{v:08X}" for k, v in probe.items()))
    if all(v == 0 for v in probe.values()):
        tb.log.error("EVERY hardware-driven register reads 0 while storage-backed "
                     "OBS_BASE_ADDR reads correctly -> hwif_in is not reaching the "
                     "regblock. That is independent of the new registers.")

    # ---- 1. capabilities must match the build ---------------------------
    caps0 = await tb.read_reg("OBS_CAPS0")
    caps1 = await tb.read_reg("OBS_CAPS1")
    caps2 = await tb.read_reg("OBS_CAPS2")
    tb.log.info(f"caps0=0x{caps0:08X} caps1=0x{caps1:08X} caps2=0x{caps2:08X}")

    exp_err   = _p("P_TAP_ERROR", 1)
    exp_tmo   = _p("P_TAP_TIMEOUT", 1)
    exp_compl = _p("P_TAP_COMPL", 1)
    exp_taps  = _p("P_MON_TAPS", 1)
    exp_nrd   = _p("P_NUM_RD_PORTS", 1)
    exp_nwr   = _p("P_NUM_WR_PORTS", 1)
    exp_nar   = _p("P_N_ADDR_RANGES", 0)

    assert (caps0 >> 0) & 1 == exp_err, (
        f"OBS_CAPS0.ERROR_CONE={(caps0 >> 0) & 1} but built with "
        f"TAP_ENABLE_ERROR_LOGIC={exp_err} -- caps must report the BUILD")
    assert (caps0 >> 1) & 1 == exp_tmo, "OBS_CAPS0.TIMEOUT_CONE disagrees with the build"
    assert (caps0 >> 2) & 1 == exp_compl, "OBS_CAPS0.COMPL_CONE disagrees with the build"
    assert (caps0 >> 6) & 1 == exp_taps, (
        f"OBS_CAPS0.MON_TAPS_ARMED={(caps0 >> 6) & 1} but ENABLE_MON_TAPS={exp_taps}. "
        f"This bit existing is the whole point: taps sat hardcoded 0 for months "
        f"and nothing could ask.")
    assert (caps0 >> 12) & 0xF == exp_nar, "OBS_CAPS0.N_ADDR_RANGES disagrees with the build"
    assert (caps1 >> 0) & 0xFF == exp_nrd, "OBS_CAPS1.NUM_RD_PORTS disagrees with the build"
    assert (caps1 >> 8) & 0xFF == exp_nwr, "OBS_CAPS1.NUM_WR_PORTS disagrees with the build"
    assert (caps2 & 0xFFFF) > 0, "OBS_CAPS2.MAX_TRANSACTIONS reads 0 -- table sizing not reported"

    # ---- 2. reset values == the constants they replaced ------------------
    mon_ctrl = await tb.read_reg("MON_CTRL")
    assert (mon_ctrl >> 0) & 1 == 1, "MON_CTRL.ERROR_EN must reset 1 (was cfg_error_enable=1'b1)"
    assert (mon_ctrl >> 1) & 1 == 1, "MON_CTRL.TIMEOUT_EN must reset 1 (was 1'b1)"
    assert (mon_ctrl >> 2) & 1 == 1, "MON_CTRL.COMPL_EN must reset 1 (was 1'b1)"
    assert (mon_ctrl >> 4) & 1 == 0, "MON_CTRL.PERF_EN must reset 0 (was cfg_perf_enable=1'b0)"
    assert (mon_ctrl >> 7) & 1 == 1, "MON_CTRL.MONITOR_EN must reset 1 (ANDs with the build arm)"

    tmo = await tb.read_reg("MON_TIMEOUT")
    assert tmo & 0xFFFF == 1024, f"MON_TIMEOUT reset {tmo & 0xFFFF} != 1024 (was 16'd1024)"
    lat = await tb.read_reg("MON_LATENCY")
    assert lat == 0x0000FFFF, f"MON_LATENCY reset 0x{lat:08X} != 0x0000FFFF"

    if _lvl == "gate":
        tb.log.info("gate: reset + capability contract only "
                    "(func adds the round-trip, full the read-only sweep)")
        return

    # ---- 3. config must actually round-trip ------------------------------
    for name, value in (("MON_CTRL",        0x0000_007F),
                        ("MON_TIMEOUT",     0x0000_0020),
                        ("MON_LATENCY",     0x1234_5678),
                        ("MON_WINDOW",      0x0000_0703),
                        ("ADDR_RANGE_CTRL", 0x0000_000F),
                        ("ADDR_RANGE0_LOW", 0xDEAD_0000),
                        ("ADDR_RANGE0_HIGH", 0xDEAD_FFFF),
                        ("OBS_BASE_ADDR",   0x0002_0000),
                        ("OBS_LIMIT_ADDR",  0x0002_FFFF)):
        await tb.write_reg(name, value)
        got = await tb.read_reg(name)
        assert got == value, (f"{name} round-trip: wrote 0x{value:08X}, read 0x{got:08X} "
                              f"-- a config write that does not stick leaves the old "
                              f"tie-off behaviour in place silently")

    if _lvl != "full":
        tb.log.info("func: stopping before the read-only sweep (full runs it)")
        return

    # ---- 4. capabilities are READ-ONLY -----------------------------------
    await tb.write_reg("OBS_CAPS0", 0xFFFF_FFFF)
    assert await tb.read_reg("OBS_CAPS0") == caps0, "OBS_CAPS0 must be read-only"

    tb.log.info("observer register layer OK")


@cocotb.test(timeout_time=500, timeout_unit="us")
async def cocotb_test_observer_traffic(dut):
    """Does the observer actually OBSERVE? Meters, and monbus packets out.

    The register test proves the block is configurable. This proves it does
    its job: drive real AXI handshakes through the taps and require that the
    bus meters count and that the monbus group emits records. Both observers
    sat for months with their monitors compiled out, emitting nothing, and no
    test existed that would have noticed.
    """
    tb = AXI4IntfObserverTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.start_egress_sink()

    # Flush every complete record rather than waiting for the 16-deep
    # watermark; a short test never reaches it and the group would sit on the
    # records until its flush timeout, long after the checks below.
    await tb.write_reg("OBS_CTRL", 0)
    await tb.write_reg("OBS_BASE_ADDR", 0x0000_0000)
    await tb.write_reg("OBS_LIMIT_ADDR", 0x0000_FFFF)

    caps0 = await tb.read_reg("OBS_CAPS0")
    assert (caps0 >> 6) & 1, "taps not armed in this build; traffic cannot be observed"

    _n = {'gate': 4, 'func': 8, 'full': 24}[current_level()]
    for i in range(_n):
        await tb.drive_read_burst(addr=0x1000 + i * 0x40, arid=i % 2, beats=4)
        await tb.drive_write_burst(addr=0x2000 + i * 0x40, awid=i % 2, beats=4)
    await tb.wait_clocks("aclk", 400)

    # Bus meters live OUTSIDE the tap gate and must count in every build.
    rd_prod = await tb.read_stat(metric=0, is_write=0)
    wr_prod = await tb.read_stat(metric=0, is_write=1)
    tb.log.info(f"meters: rd_productive={rd_prod} wr_productive={wr_prod}")
    assert rd_prod > 0 or wr_prod > 0, (
        f"bus meters counted nothing after 8 read + 8 write bursts "
        f"(rd={rd_prod} wr={wr_prod}) -- the taps are not seeing the bus")

    # And the monbus group must have pushed records out of its AXIL master.
    tb.log.info(f"monbus egress beats: {tb.egress_beats}")
    if (caps0 & 0b0000_0111):        # any of ERROR / TIMEOUT / COMPL built
        assert tb.egress_beats > 0, (
            f"reporter cones are built (caps0=0x{caps0:08X}) and 16 bursts "
            f"completed, but the monbus group emitted nothing. That is the "
            f"exact failure the observers shipped with: monitors enabled, "
            f"cones present, mon_valid flat at 0.")
    tb.log.info("observer traffic path OK")


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_observer_packet_coverage(dut):
    """Every injectable error, and every packet class the observer can emit.

    Counting egress BEATS is not verification: it cannot tell a completion
    from an error, and it cannot explain why two observers that share a
    register map emit different totals. This decodes every record with the
    SHARED monbus decoder and asserts on packet_type/event_code.
    """
    tb = AXI4IntfObserverTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.start_egress_sink()
    await tb.write_reg("OBS_CTRL", 0)                 # flush every record
    await tb.write_reg("OBS_BASE_ADDR", 0x0000_0000)
    await tb.write_reg("OBS_LIMIT_ADDR", 0x0000_FFFF)

    caps0 = await tb.read_reg("OBS_CAPS0")
    built = {"ERROR": caps0 & 1, "TIMEOUT": (caps0 >> 1) & 1,
             "COMPL": (caps0 >> 2) & 1, "THRESHOLD": (caps0 >> 3) & 1,
             "PERF": (caps0 >> 4) & 1, "DEBUG": (caps0 >> 5) & 1}
    tb.log.info(f"cones built: {built}")

    # ---- 1. clean traffic -> COMPLETION only -----------------------------
    # UNIQUE ids per transaction. Reusing an id while the previous
    # transaction is still live in the CAM is an ID collision, and a write
    # whose B lands before its data is attributed reads as a protocol
    # violation -- both are stimulus faults that look like DUT errors.
    _n = {'gate': 2, 'func': 4, 'full': 8}[current_level()]
    for i in range(_n):
        await tb.drive_read_burst(addr=0x1000 + i * 0x40, arid=i, beats=4)
        await tb.wait_clocks("aclk", 40)
        await tb.drive_write_burst(addr=0x2000 + i * 0x40, awid=i + 8, beats=4)
        await tb.wait_clocks("aclk", 40)
    await tb.wait_clocks("aclk", 300)
    clean = tb.log_tally("clean traffic")
    if built["COMPL"]:
        assert "Completion" in tb.types_seen(), (
            f"COMPL cone is built and 8 clean bursts completed, but no "
            f"Completion packet was emitted. Saw: {sorted(tb.types_seen())}")
    assert "Error" not in tb.types_seen(), (
        f"clean traffic produced an Error packet: {clean}")

    # ---- 2. inject every AXI response error ------------------------------
    # SLVERR and DECERR on both the read and the write channel: these are the
    # errors an interface observer can actually be made to see from the bus.
    n_before = len(tb.packets)
    for n, (resp, code) in enumerate(((2, AXIErrorCode.AXI_ERR_RESP_SLVERR),
                                      (3, AXIErrorCode.AXI_ERR_RESP_DECERR))):
        # distinct ids AND a settle gap: the first injection previously used
        # the same id as the second, so the second collided with a CAM entry
        # still in TRANS_ERROR and only one code was ever reported.
        await tb.drive_write_burst(addr=0x3000 + n * 0x100, awid=2 + n, beats=2, bresp=resp)
        await tb.wait_clocks("aclk", 60)
        await tb.drive_read_burst(addr=0x4000 + n * 0x100, arid=4 + n, beats=2, rresp=resp)
        await tb.wait_clocks("aclk", 60)
    await tb.wait_clocks("aclk", 400)
    injected = tb.log_tally("after error injection")

    if built["ERROR"]:
        errs = {c for (n, c) in injected if n == "Error"}
        assert errs, (
            f"ERROR cone built, SLVERR+DECERR injected on both channels, no "
            f"Error packet emitted. Saw: {sorted(tb.types_seen())}")
        for want in (int(AXIErrorCode.AXI_ERR_RESP_SLVERR),
                     int(AXIErrorCode.AXI_ERR_RESP_DECERR)):
            assert want in errs, (
                f"injected AXI error code {want} "
                f"({AXIErrorCode(want).name}) never appeared; got {sorted(errs)}")
        assert len(tb.packets) > n_before, "error injection produced no new packets"

    tb.log.info(f"packet classes observed: {sorted(tb.types_seen())}")
    tb.check_record_framing()


@cocotb.test(timeout_time=4, timeout_unit="ms")
async def cocotb_test_observer_all_classes(dut):
    """Every packet CLASS the observer can emit, on a build with every cone.

    Errors alone are not coverage. This build turns on all six reporter cones
    and four address ranges, enables every runtime cone bit, and then drives
    stimulus shaped to provoke each class in turn. Whatever a class needs to
    fire, the test states it and checks for it by name.
    """
    tb = AXI4IntfObserverTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.start_egress_sink()
    await tb.write_reg("OBS_CTRL", 0)
    await tb.write_reg("OBS_BASE_ADDR", 0x0000_0000)
    await tb.write_reg("OBS_LIMIT_ADDR", 0x0000_FFFF)

    caps0 = await tb.read_reg("OBS_CAPS0")
    n_ranges = (caps0 >> 12) & 0xF
    tb.log.info(f"caps0=0x{caps0:08X} n_addr_ranges={n_ranges}")

    # every runtime cone on, tight thresholds so they can actually trip
    await tb.write_reg("MON_CTRL", 0xFF)          # all EN bits + ADDR_CHECK + MONITOR
    await tb.write_reg("MON_TIMEOUT", 4)          # microseconds, short
    await tb.write_reg("MON_LATENCY", 8)          # trip THRESHOLD easily
    if n_ranges:
        await tb.write_reg("ADDR_RANGE0_LOW", 0x0000_1000)
        await tb.write_reg("ADDR_RANGE0_HIGH", 0x0000_1FFF)
        await tb.write_reg("ADDR_RANGE_CTRL", 0x1)

    # completion + threshold + perf + addr-match: in-range and out-of-range
    _n = {'gate': 4, 'func': 6, 'full': 12}[current_level()]
    _n_out = {'gate': 2, 'func': 4, 'full': 8}[current_level()]
    for i in range(_n):
        await tb.drive_read_burst(addr=0x1000 + i * 0x40, arid=i, beats=4)
        await tb.wait_clocks("aclk", 40)
        await tb.drive_write_burst(addr=0x1000 + i * 0x40, awid=i + 8, beats=4)
        await tb.wait_clocks("aclk", 40)
    for i in range(_n_out):                       # deliberately OUT of range 0
        await tb.drive_read_burst(addr=0x8000 + i * 0x40, arid=i, beats=2)
        await tb.wait_clocks("aclk", 40)
    for n, resp in enumerate((2, 3)):
        await tb.drive_write_burst(addr=0x3000 + n * 0x100, awid=2 + n, beats=2, bresp=resp)
        await tb.wait_clocks("aclk", 60)
        await tb.drive_read_burst(addr=0x4000 + n * 0x100, arid=4 + n, beats=2, rresp=resp)
        await tb.wait_clocks("aclk", 60)
    # timeout: an address with no data, left to expire
    await tb.drive_read_burst(addr=0x5000, arid=6, beats=0)
    await tb.wait_clocks("aclk", 4000)

    tally = tb.log_tally("all classes")
    seen = tb.types_seen()
    tb.check_record_framing()

    want = {"Completion": (caps0 >> 2) & 1, "Error": caps0 & 1,
            "Timeout": (caps0 >> 1) & 1, "Threshold": (caps0 >> 3) & 1,
            "Perf": (caps0 >> 4) & 1, "Debug": (caps0 >> 5) & 1}
    missing = [k for k, built in want.items() if built and k not in seen]
    tb.log.info(f"classes seen={sorted(seen)} built-but-missing={missing}")
    assert not missing, (
        f"cones built but these packet classes never came out: {missing}. "
        f"Tally: {tally}. Check the per-cone runtime enables in "
        f"axi4_*_{{rd,wr}}_mon, then the group's cfg_axi_pkt_mask/err_select.")
    if n_ranges:
        assert "AddrMatch" in seen, (
            f"{n_ranges} address ranges built and range0 armed over "
            f"0x1000-0x1FFF with traffic both inside and outside, but no "
            f"AddrMatch packet. Saw: {sorted(seen)}")


def _types_since(tb, n0):
    """Packet-class names among packets captured after index n0.

    The sink is started ONCE for the whole test (start_egress_sink does
    cocotb.start_soon on an infinite loop, so calling it twice would run two
    samplers against the same signals and corrupt the 3-beat framing), so
    batches are separated by slicing rather than by re-arming.
    """
    out = set()
    for pk in tb.packets[n0:]:
        try:
            out.add(PktType(pk.packet_type).name.replace("PktType", ""))
        except ValueError:
            out.add(f"type{pk.packet_type}")
    return out


@cocotb.test(timeout_time=200, timeout_unit="us")
async def cocotb_test_observer_reset_reissue(dut):
    """TASK-084: does a scenario still emit after an earlier one has run?

    The board symptom (Genesys 2 build-mon): the addr_error scenario emits
    129/122 ADDR_RANGE packets when it is the FIRST thing run after the
    bitstream is programmed, and ZERO if any other scenario ran first. Only
    REPROGRAMMING recovers, and programming is what asserts the global
    aresetn. Every scenario already begins with CTRL.SOFT_RESET.

    The monbus GROUP was excluded in cosim (val/amba/test_monbus_group_soft_reset.py):
    it clears completely across a reset and emits normally afterwards. This is
    the UPSTREAM half, on the observer itself -- and unlike the group probe it
    can count the packet class the board actually lost, AddrMatch.

    Two identical batches separated by a reset pulse; batch 2 must still emit.

    THE REPROGRAM BETWEEN BATCHES IS REQUIRED, NOT INCIDENTAL. The reset
    returns every observer CSR to its reset value -- confirmed behaviour, not
    a defect -- which disarms the address ranges. A board scenario does exactly
    this: SOFT_RESET, then setup() reprograms. Skipping the reprogram here
    would leave batch 2 with no ranges armed; it would emit no AddrMatch for a
    completely legitimate reason and the test would report a reproduction that
    is not one.
    """
    tb = AXI4IntfObserverTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.start_egress_sink()          # ONCE for the whole test

    caps0 = await tb.read_reg("OBS_CAPS0")
    n_ranges = (caps0 >> 12) & 0xF
    assert n_ranges, (
        f"caps0=0x{caps0:08X} reports 0 address ranges, so AddrMatch is "
        f"structurally impossible and this probe cannot say anything about "
        f"TASK-084. It must run on _PARAMS_ALL (N_ADDR_RANGES=4).")

    # Pristine post-reset value, read rather than hardcoded: the mid-test
    # reset is later required to return this register to THIS value.
    rng_ctrl_reset = await tb.read_reg("ADDR_RANGE_CTRL")

    async def _program():
        """Exactly what a board scenario's setup() does after SOFT_RESET."""
        await tb.write_reg("OBS_CTRL", 0)
        await tb.write_reg("OBS_BASE_ADDR", 0x0000_0000)
        await tb.write_reg("OBS_LIMIT_ADDR", 0x0000_FFFF)
        await tb.write_reg("MON_CTRL", 0xFF)      # all EN + ADDR_CHECK + MONITOR
        await tb.write_reg("MON_TIMEOUT", 4)
        await tb.write_reg("MON_LATENCY", 8)
        await tb.write_reg("ADDR_RANGE0_LOW", 0x0000_1000)
        await tb.write_reg("ADDR_RANGE0_HIGH", 0x0000_1FFF)
        await tb.write_reg("ADDR_RANGE_CTRL", 0x1)

    async def _batch(label):
        n = {"gate": 3, "func": 5, "full": 8}[current_level()]
        for i in range(n):
            await tb.drive_read_burst(addr=0x1000 + i * 0x40, arid=i, beats=4)
            await tb.wait_clocks("aclk", 40)
            await tb.drive_write_burst(addr=0x1000 + i * 0x40, awid=i + 8, beats=4)
            await tb.wait_clocks("aclk", 40)
        # deliberately OUT of range 0, so a match is a match and not "everything"
        await tb.drive_read_burst(addr=0x8000, arid=15, beats=2)
        await tb.wait_clocks("aclk", 200)
        tb.log.info(f"[TASK-084] {label}: {len(tb.packets)} packets captured total")

    # ---- Scenario 1 ------------------------------------------------------
    await _program()
    n0 = len(tb.packets)
    await _batch("BATCH-1")
    first = _types_since(tb, n0)
    tb.log.info(f"[TASK-084] batch 1 classes: {sorted(first)}")

    # ---- The reset a board scenario pulses between runs ------------------
    await tb.assert_reset()
    await tb.wait_clocks("aclk", 16)
    await tb.deassert_reset()
    await tb.wait_clocks("aclk", 5)
    await tb.apb.reset_bus()
    # A reset can land mid-record: records are 3 AXIL beats. Drop any partial
    # or batch 2's beats append onto the stub and every later record is
    # mis-framed (check_record_framing below would then fail for the wrong
    # reason).
    tb._rec = []

    rng_ctrl_after = await tb.read_reg("ADDR_RANGE_CTRL")
    tb.log.info(f"[TASK-084] ADDR_RANGE_CTRL: power-on={rng_ctrl_reset:#x} "
                f"programmed=0x1 after-reset={rng_ctrl_after:#x}")

    # ---- Scenario 2: identical traffic, reprogrammed as a scenario would --
    await _program()
    n1 = len(tb.packets)
    await _batch("BATCH-2")
    second = _types_since(tb, n1)
    tb.log.info(f"[TASK-084] batch 2 classes: {sorted(second)}")
    tb.log_tally("both batches")

    # ARMED FIRST: if batch 1 never emitted AddrMatch, batch 2 says nothing.
    assert "AddrMatch" in first, (
        f"batch 1 emitted no AddrMatch with {n_ranges} ranges built and range0 "
        f"armed over 0x1000-0x1FFF. The stimulus or the arming is wrong, so "
        f"nothing about a reset can be concluded. Saw: {sorted(first)}")

    # The reset must genuinely clear config, or the reprogram above is a no-op
    # and batch 2 would prove nothing about recovery.
    assert rng_ctrl_after == rng_ctrl_reset, (
        f"ADDR_RANGE_CTRL reads {rng_ctrl_after:#x} after the reset pulse but "
        f"{rng_ctrl_reset:#x} after power-on reset. The mid-test reset did not "
        f"restore it, so this probe is not reproducing what SOFT_RESET does.")

    # THE REGRESSION: a scenario must not be dead merely because one ran before.
    assert "AddrMatch" in second, (
        f"batch 2 emitted NO AddrMatch after a reset that followed prior "
        f"traffic, while batch 1 did. Identical stimulus, reprogrammed exactly "
        f"as a board scenario does. This reproduces the board's order "
        f"dependence at the observer. batch1={sorted(first)} "
        f"batch2={sorted(second)}. TASK-084.")

    # Framing must survive the reset -- but validate it PER BATCH. The stock
    # check_record_framing() walks EVERY record with a 64-tick monotonicity
    # tolerance, and the reset RESTARTS the observer's timebase, so batch 2's
    # timestamps legitimately sit far below batch 1's. Measured across the
    # boundary: 197 ticks "backwards", which is the reset working, not a
    # framing fault. Calling the stock check here fails for the wrong reason.
    def _framing(recs, label):
        assert recs, f"{label}: no records captured"
        last, back = -1, 0
        for i, (b0, _hi, _lo) in enumerate(recs):
            tag = (b0 >> 60) & 0xF
            ts = b0 & ((1 << 60) - 1)
            assert tag == 0, f"{label} record {i}: beat0 tag={tag}, expected 0"
            assert ts > 0, f"{label} record {i}: source_ts is 0 -- timebase stopped"
            if ts < last:
                back = max(back, last - ts)
            last = max(last, ts)
        assert back < 64, (
            f"{label}: records reordered by {back} ticks, beyond arbiter "
            f"interleave -- the timebase or the merge is wrong WITHIN a batch")
        tb.log.info(f"[TASK-084] {label} framing OK: {len(recs)} records, "
                    f"max out-of-order depth {back}")
        return recs

    b1 = _framing(tb.records[n0:n1], "batch 1")
    b2 = _framing(tb.records[n1:], "batch 2")

    # POSITIVE evidence that the reset reached the observer's TIMEBASE and not
    # merely its CSRs. Compared as min/max rather than first/last because the
    # arbiter legitimately interleaves the read and write monitors.
    ts1_max = max((b0 & ((1 << 60) - 1)) for b0, _h, _l in b1)
    ts2_min = min((b0 & ((1 << 60) - 1)) for b0, _h, _l in b2)
    tb.log.info(f"[TASK-084] timebase: batch1 max ts={ts1_max} "
                f"batch2 min ts={ts2_min}")
    assert ts2_min < ts1_max, (
        f"batch 2's lowest timestamp ({ts2_min}) is not below batch 1's "
        f"highest ({ts1_max}), so the reset did NOT restart the observer's "
        f"timebase. The pulse never reached the block's counters and this "
        f"probe is not testing what it claims to test.")


def _run_observer(request, dut_name, params, testcase="cocotb_test_observer_regs",
                  test_level="gate"):
    module, repo_root_, tests_dir, log_dir, rtl_dict = get_paths({
        'misc_rtl': '../../../rtl',
    })
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_,
        filelist_path=f'projects/components/misc/rtl/filelists/{dut_name}.f')

    # Build key = what actually changes the BUILD (toplevel + parameters),
    # plus the xdist worker. testcase and test_level are runtime-only, so
    # keying on them compiled the same RTL 12 times per observer; keying on
    # nothing would let two processes share a directory and regenerate
    # sources under each other (PUMICE-019). Worker-scoped means cells that
    # share a worker reuse one build and no two processes ever collide.
    p_digest = hashlib.md5(repr(sorted(params.items())).encode()).hexdigest()[:6]
    worker = os.environ.get('PYTEST_XDIST_WORKER', '')
    sim_build = sim_build_path(
        tests_dir, f"{dut_name}_p{p_digest}" + (f"_{worker}" if worker else ""))
    # Per-cell evidence: this was the only wrapper in the area writing no log
    # and no results file, so its level grading left nothing to check.
    tag = f"{dut_name}_{testcase}_{test_level}" + (f"_{worker}" if worker else "")
    os.makedirs(log_dir, exist_ok=True)
    env_log = {'LOG_PATH': os.path.join(log_dir, f"{tag}.log"),
               'COCOTB_RESULTS_FILE': os.path.join(log_dir, f"results_{tag}.xml"),
               'COCOTB_LOG_LEVEL': 'INFO'}

    env = os.environ.copy()
    env.update(env_log)
    env.update(level_env(test_level))
    env.update({f"P_{k}": str(v) for k, v in {
        'TAP_ERROR': params['TAP_ENABLE_ERROR_LOGIC'],
        'TAP_TIMEOUT': params['TAP_ENABLE_TIMEOUT_LOGIC'],
        'TAP_COMPL': params['TAP_ENABLE_COMPL_LOGIC'],
        'MON_TAPS': params['ENABLE_MON_TAPS'],
        'NUM_RD_PORTS': params['NUM_RD_PORTS'],
        'NUM_WR_PORTS': params['NUM_WR_PORTS'],
        'N_ADDR_RANGES': params['N_ADDR_RANGES'],
    }.items()})

    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    wave_args = (["--trace-fst", "--trace-structs", "--trace-depth", "99"]
                 if enable_waves else [])

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=os.path.splitext(os.path.basename(__file__))[0],
        testcase=testcase,
        parameters=params,
        sim_build=sim_build,
        extra_env=env,
        timescale="1ns/1ps",
        compile_args=["--unroll-count", "16384", "--unroll-stmts", "200000",
                      "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC", "-Wno-SELRANGE",
                      "-Wno-PINMISSING", "-Wno-PINCONNECTEMPTY",
                      # UNOPTFLAT on monitor_trans_cam's allocator is a PROVEN
                      # FALSE POSITIVE, not an unexamined silence. Traced every
                      # link Verilator names and all pass through registered
                      # state -- w_free_oh[i] = !r_valid[i], entry_valid[gi] =
                      # r_valid[gi] -- so no alloc output can reach a
                      # *_wants_alloc input. It is word-granularity analysis of
                      # the addr->data->resp chain on one vector.
                      # split_var is the right fix and is silently REFUSED on
                      # public vars ("will not be split because it is public"),
                      # which --public-flat-rw makes all of them. Rewriting the
                      # allocator feed-forward did not help either (3 -> 5
                      # warnings), so the honest option is a documented waiver.
                      "-Wno-UNOPTFLAT",
                      "-Wno-MULTIDRIVEN"] + wave_args,
        waves=enable_waves,
        sim_args=(["--trace", "--trace-structs", "--trace-depth", "99"]
                  if enable_waves else []),
        plus_args=['--trace'] if enable_waves else [],
    )


# Every cone built + address ranges, so the all-classes test can actually
# reach each one. The lean _PARAMS above mirrors how the harness builds it.
_PARAMS_ALL = {
    'NUM_RD_PORTS': 1, 'NUM_WR_PORTS': 1, 'NUM_CHANNELS': 2,
    'ENABLE_MON_TAPS': 1, 'EGRESS_AXIL': 1, 'N_ADDR_RANGES': 4,
    'TAP_ENABLE_ERROR_LOGIC': 1, 'TAP_ENABLE_TIMEOUT_LOGIC': 1,
    'TAP_ENABLE_COMPL_LOGIC': 1, 'TAP_ENABLE_THRESHOLD_LOGIC': 1,
    'TAP_ENABLE_PERF_LOGIC': 1, 'TAP_ENABLE_DEBUG_LOGIC': 1,
}

_PARAMS = {
    'NUM_RD_PORTS': 1, 'NUM_WR_PORTS': 1, 'NUM_CHANNELS': 2,
    'ENABLE_MON_TAPS': 1,
    'TAP_ENABLE_ERROR_LOGIC': 1, 'TAP_ENABLE_TIMEOUT_LOGIC': 1,
    'TAP_ENABLE_COMPL_LOGIC': 1,
    'N_ADDR_RANGES': 0,
    'EGRESS_AXIL': 1,
}


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_axi4_intf_master_observer(request, test_level):
    """Register layer of the MASTER observer."""
    _run_observer(request, 'axi4_intf_master_observer', dict(_PARAMS), test_level=test_level)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_axi4_intf_master_observer_traffic(request, test_level):
    """Observation path of the MASTER observer."""
    _run_observer(request, 'axi4_intf_master_observer', dict(_PARAMS),
                  testcase="cocotb_test_observer_traffic",
                  test_level=test_level)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_axi4_intf_slave_observer_traffic(request, test_level):
    """Observation path of the SLAVE observer."""
    _run_observer(request, 'axi4_intf_slave_observer', dict(_PARAMS),
                  testcase="cocotb_test_observer_traffic",
                  test_level=test_level)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_axi4_intf_master_observer_packets(request, test_level):
    """Packet-class and error-injection coverage, MASTER observer."""
    _run_observer(request, 'axi4_intf_master_observer', dict(_PARAMS),
                  testcase="cocotb_test_observer_packet_coverage",
                  test_level=test_level)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_axi4_intf_slave_observer_packets(request, test_level):
    """Packet-class and error-injection coverage, SLAVE observer."""
    _run_observer(request, 'axi4_intf_slave_observer', dict(_PARAMS),
                  testcase="cocotb_test_observer_packet_coverage",
                  test_level=test_level)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_axi4_intf_slave_observer(request, test_level):
    """Register layer of the SLAVE observer -- same map, same body."""
    _run_observer(request, 'axi4_intf_slave_observer', dict(_PARAMS), test_level=test_level)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_axi4_intf_master_observer_all_classes(request, test_level):
    """Every packet class, MASTER observer, all cones built."""
    _run_observer(request, 'axi4_intf_master_observer', dict(_PARAMS_ALL),
                  testcase="cocotb_test_observer_all_classes",
                  test_level=test_level)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_axi4_intf_slave_observer_all_classes(request, test_level):
    """Every packet class, SLAVE observer, all cones built."""
    _run_observer(request, 'axi4_intf_slave_observer', dict(_PARAMS_ALL),
                  testcase="cocotb_test_observer_all_classes",
                  test_level=test_level)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_axi4_intf_master_observer_reset_reissue(request, test_level):
    """TASK-084: MASTER observer still emits after a mid-run reset."""
    _run_observer(request, 'axi4_intf_master_observer', dict(_PARAMS_ALL),
                  testcase="cocotb_test_observer_reset_reissue",
                  test_level=test_level)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_axi4_intf_slave_observer_reset_reissue(request, test_level):
    """TASK-084: SLAVE observer still emits after a mid-run reset."""
    _run_observer(request, 'axi4_intf_slave_observer', dict(_PARAMS_ALL),
                  testcase="cocotb_test_observer_reset_reissue",
                  test_level=test_level)
