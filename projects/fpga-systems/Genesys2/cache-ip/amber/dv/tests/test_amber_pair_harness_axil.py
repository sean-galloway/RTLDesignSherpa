# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_amber_pair_harness_axil
# Purpose: Drive amber_pair_harness's direct AXIL4-Lite host interface with the
#   house AXIL4 master BFM, bypassing the UART bridge. This is the FAST low-level
#   path for exercising the DUT; it is NOT the UART equivalence evidence. The
#   equivalence evidence is test_amber_pair_harness_uart, which imports and runs
#   the same host sequences through the real uart_axil_bridge.

import os
import sys

import pytest
import cocotb
from cocotb_test.simulator import run

repo_root = os.path.dirname(
    os.path.dirname(
        os.path.dirname(
            os.path.dirname(
                os.path.dirname(
                    os.path.dirname(
                        os.path.dirname(
                            os.path.dirname(os.path.abspath(__file__)))))))))
sys.path.insert(0, repo_root)

from TBClasses.shared.utilities import get_repo_root, get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import reg_level_grid, level_env
from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.axil4.axil4_factories import create_axil4_master
from TBClasses.shared.verilator_cfg import FIELD_COMBO_VLT  # noqa: E402  (not -Wno-MULTIDRIVEN)


AMBER_FRAMEWORK_ROOT = os.path.join(
    repo_root, "projects", "fpga-systems", "Genesys2", "cache-ip", "amber")

# Bridge address map (matches bridge_amber_axil.toml)
ADDR_HARNESS_CSR = 0x0001_0000
ADDR_CYCLE_INJECTOR0 = 0x0002_0000
ADDR_CYCLE_INJECTOR1 = 0x0003_0000
ADDR_TALLY_CNT = 0x0004_0000
ADDR_TALLY_CFGW = 0x0005_0000
ADDR_TALLY_CFGR = 0x0006_0000

# Cycle-injector CSR word offsets (32-bit)
CI_CTRL = 0x00
CI_SEED = 0x04
CI_ADDR_BASE = 0x08
CI_ADDR_MASK = 0x0C
CI_TRANS_COUNT = 0x10
CI_STATUS = 0x14
CI_ACC_COUNT = 0x18
CI_RSP_COUNT = 0x1C
CI_ERR_FLAG = 0x20
CI_RSP_CRC_LO = 0x30
CI_RSP_CRC_HI = 0x34
CI_WDATA_CRC_LO = 0x38
CI_WDATA_CRC_HI = 0x3C

# Harness CSR word offsets
HCSR_CTRL = 0x00
HCSR_STATUS = 0x04
HCSR_CYCLE_LO = 0x08
HCSR_CYCLE_HI = 0x0C
HCSR_FABRIC_DBG = 0x10

# Tally config register offsets (64-bit stride)
TALLY_CAM_CLEAR = 0x100
TALLY_CAM_KEY = 0x108
TALLY_CAM_LOAD = 0x110

# Tally cfgr readback offsets (32-bit words; see tally_regs.rdl)
TALLY_LATCH_STATUS = 0x10   # {VALID[16], FILL[15:0]}
TALLY_LATCH_PKT0 = 0x18
TALLY_LATCH_TS_LO = 0x38
TALLY_LATCH_TS_HI = 0x40
TALLY_LATCH_SEL = 0x120     # cfgw aperture
TALLY_WATCH_CTRL = 0x118    # cfgw aperture

# Cycle-injector latency instrumentation (formal/amber TASK-001 item 2)
CI_LAT_MIN = 0x24
CI_LAT_MAX = 0x28
CI_RUN_CYCLES = 0x2C
CI_LAT_SUM_LO = 0x40
CI_LAT_SUM_HI = 0x44
CI_LAT_HIST0 = 0x48         # .. 0x64, 8 log2 buckets
# Cycle-injector parallelism counters (cache-ip common-ip TASK-002)
CI_OUTST_MAX = 0x68
CI_OUTST_SUM_LO = 0x6C
CI_OUTST_SUM_HI = 0x70
CI_STALL_CYCLES = 0x74
CI_CREDIT_STALL = 0x78
CI_MAX_OUTSTANDING = 16     # the RTL's MAX_OUTSTANDING (CTRL clamp)
# Whether the cache under test is expected to take more than one request
# in flight (jet: yes; amber is blocking and may hold at one or two).
INJECTOR_EXPECT_PIPELINED = False
TALLY_NUM_LATCH = 16


def _key(agent: int, protocol: int, pkt_type: int, event: int) -> int:
    return ((agent & 0xFFFF) << 16) | ((protocol & 0xF) << 12) | \
           ((pkt_type & 0xF) << 8) | (event & 0xFF)


def _default_profile():
    # Wire-truth keys (BUG-004 board capture): all amber monlites emit agent
    # 0x00A0; control events are CORE/PktTypePerf with l1_pkg codes 0x00-0x09;
    # the AXI rd/wr monlites share PktTypeCompletion code 0 and merge into one
    # CAM bin because unit_id is not part of the tally key.
    a = 0x00A0
    return [
        (_key(a, 4, 4, 0x00), 0),  # hit
        (_key(a, 4, 4, 0x01), 1),  # miss
        (_key(a, 4, 4, 0x02), 2),  # snoop accepted
        (_key(a, 4, 4, 0x03), 3),  # evict
        (_key(a, 4, 4, 0x04), 5),  # tag state transition
        (_key(a, 0, 0, 0x0E), 4),  # AXI monlite drop report (health bin)
        (_key(a, 4, 4, 0x05), 6),  # fill start
        (_key(a, 4, 4, 0x06), 7),  # fill end
        (_key(a, 4, 4, 0x07), 8),  # drain start
        (_key(a, 4, 4, 0x08), 9),  # drain end
        (_key(a, 4, 0, 0x09), 10),  # control monlite drop report
    ]


class AmberPairHarnessAXILTest(TBBase):
    def __init__(self, dut, clock_task):
        super().__init__(dut)
        self.clock_task = clock_task
        self.axil = create_axil4_master(
            dut,
            clock=dut.aclk,
            prefix='host_axi_',
            data_width=32,
            addr_width=32,
            multi_sig=True,
            timeout_cycles=5000,
            log=self.log,
        )

    async def reset(self):
        self.dut.aresetn.value = 0
        for _ in range(12):
            await cocotb.triggers.RisingEdge(self.dut.aclk)
        self.dut.aresetn.value = 1
        for _ in range(5):
            await cocotb.triggers.RisingEdge(self.dut.aclk)

        # Sanity check: sample clock at opposite phases to confirm toggling.
        await cocotb.triggers.FallingEdge(self.dut.aclk)
        s0 = int(self.dut.aclk.value)
        await cocotb.triggers.RisingEdge(self.dut.aclk)
        s1 = int(self.dut.aclk.value)
        self.log.info(f"reset complete: aclk sampled {s0} -> {s1}")

    async def write32(self, addr: int, data: int):
        return await self.axil['write'].single_write(addr, data)

    async def read32(self, addr: int):
        return await self.axil['read'].single_read(addr)

    async def write64(self, addr: int, data: int):
        await self.write32(addr, data & 0xFFFF_FFFF)
        await self.write32(addr + 4, (data >> 32) & 0xFFFF_FFFF)

    async def read64(self, addr: int):
        lo = await self.read32(addr)
        hi = await self.read32(addr + 4)
        return (hi << 32) | lo


async def _manual_clock(dut):
    dut.aclk.value = 1
    while True:
        await cocotb.triggers.Timer(5, unit='ns')
        dut.aclk.value = 0
        await cocotb.triggers.Timer(5, unit='ns')
        dut.aclk.value = 1


@cocotb.test(timeout_time=1000, timeout_unit="ms")
async def aperture_probe_test(dut):
    """Write then read every slave aperture to reproduce the bring-up hang."""
    clk_task = cocotb.start_soon(_manual_clock(dut))
    tb = AmberPairHarnessAXILTest(dut, clk_task)
    await tb.reset()

    failures = []

    # harness_csr: write CTRL then read it back
    try:
        await tb.write32(ADDR_HARNESS_CSR + HCSR_CTRL, 0x0000_0000)
        ctrl = await tb.read32(ADDR_HARNESS_CSR + HCSR_CTRL)
        if ctrl != 0x0000_0000:
            failures.append(f"harness_csr CTRL readback mismatch: 0x{ctrl:08x}")
    except Exception as e:
        failures.append(f"harness_csr access failed: {e}")

    # harness_csr cycle counter should advance
    try:
        cyc0 = await tb.read32(ADDR_HARNESS_CSR + HCSR_CYCLE_LO)
        for _ in range(10):
            await cocotb.triggers.RisingEdge(dut.aclk)
        cyc1 = await tb.read32(ADDR_HARNESS_CSR + HCSR_CYCLE_LO)
        if cyc1 <= cyc0:
            failures.append(f"cycle counter did not advance: {cyc0} -> {cyc1}")
    except Exception as e:
        failures.append(f"harness_csr cycle counter read failed: {e}")

    # cycle_injector0: write/read a config register
    try:
        await tb.write32(ADDR_CYCLE_INJECTOR0 + CI_SEED, 0x1234_5678)
        seed = await tb.read32(ADDR_CYCLE_INJECTOR0 + CI_SEED)
        if seed != 0x1234_5678:
            failures.append(f"cycle_injector0 SEED readback mismatch: 0x{seed:08x}")
    except Exception as e:
        failures.append(f"cycle_injector0 access failed: {e}")

    # cycle_injector1: write/read a config register
    try:
        await tb.write32(ADDR_CYCLE_INJECTOR1 + CI_SEED, 0xDEAD_BEEF)
        seed = await tb.read32(ADDR_CYCLE_INJECTOR1 + CI_SEED)
        if seed != 0xDEAD_BEEF:
            failures.append(f"cycle_injector1 SEED readback mismatch: 0x{seed:08x}")
    except Exception as e:
        failures.append(f"cycle_injector1 access failed: {e}")

    # tally_cfgw: write the CAM clear/key/load aperture (32-bit registers;
    # single 32-bit writes only -- see smoke_test's BUG-003 comment).
    # We verify the write completes (no hang); the exact readback of CAM_KEY
    # depends on the generated regblock update timing and is covered by the
    # smoke sequence that checks tally bins.
    try:
        await tb.write32(ADDR_TALLY_CFGW + TALLY_CAM_CLEAR, 0)
        await tb.write32(ADDR_TALLY_CFGW + TALLY_CAM_KEY, _default_profile()[0][0])
        await tb.write32(ADDR_TALLY_CFGW + TALLY_CAM_LOAD, (1 << 31) | 0)
    except Exception as e:
        failures.append(f"tally_cfgw/cfgr access failed: {e}")

    # tally_cnt: read only, should not hang
    try:
        await tb.read64(ADDR_TALLY_CNT)
    except Exception as e:
        failures.append(f"tally_cnt read failed: {e}")

    assert not failures, "; ".join(failures)


@cocotb.test(timeout_time=5000, timeout_unit="ms")
async def smoke_test(dut):
    """Run the amber_board.py smoke sequence in simulation."""
    clk_task = cocotb.start_soon(_manual_clock(dut))
    tb = AmberPairHarnessAXILTest(dut, clk_task)
    await tb.reset()

    # Configure tally legal-set profile. The CAM registers are 32-bit and
    # MUST be written with single 32-bit accesses: a 64-bit decomposition
    # (write64) writes the high word at +4, which aliases onto the same
    # register in the 64-bit cfgw port wrapper (it ignores WSTRB and takes
    # wdata[31:0]), zeroing CAM_KEY before the load and re-firing CAM_LOAD
    # with INDEX=0/VALID=0 (BUG-003). CAM_LOAD = {VALID[31], INDEX[7:0]}
    # per tally_regs.rdl.
    await tb.write32(ADDR_TALLY_CFGW + TALLY_CAM_CLEAR, 0)
    for key, idx in _default_profile():
        await tb.write32(ADDR_TALLY_CFGW + TALLY_CAM_KEY, key)
        await tb.write32(ADDR_TALLY_CFGW + TALLY_CAM_LOAD, (1 << 31) | (idx & 0xFF))

    # Both injectors target the same 4 KB region by default. The env
    # overrides reproduce a board perf-sweep config in simulation (mask =
    # working set, base1 = the second injector's base; e.g. MASK=0xFFFF
    # BASE1=0x40000 is disjoint64k_we64), so a board tally can be checked
    # against the RTL cycle-for-cycle.
    mask = int(os.environ.get('AMBER_SMOKE_MASK', '0xFFF'), 0)
    base = 0x0000_0000
    base1 = int(os.environ.get('AMBER_SMOKE_BASE1', '0'), 0)
    count = int(os.environ.get('AMBER_SMOKE_COUNT', '200'))

    for ci_base, seed, ci_addr_base in [(ADDR_CYCLE_INJECTOR0, 0x1234_5678, base),
                                        (ADDR_CYCLE_INJECTOR1, 0xDEAD_BEEF, base1)]:
        await tb.write32(ci_base + CI_SEED, seed)
        await tb.write32(ci_base + CI_ADDR_BASE, ci_addr_base)
        await tb.write32(ci_base + CI_ADDR_MASK, mask)
        await tb.write32(ci_base + CI_TRANS_COUNT, count)
        ctrl = (64 << 8) | 0x00
        await tb.write32(ci_base + CI_CTRL, ctrl)

    # Start both injectors
    await tb.write32(ADDR_CYCLE_INJECTOR0 + CI_CTRL, (64 << 8) | 0x01)
    await tb.write32(ADDR_CYCLE_INJECTOR1 + CI_CTRL, (64 << 8) | 0x01)

    # Poll for done with a generous but bounded timeout.
    max_cycles = 500_000
    done = False
    for _ in range(max_cycles):
        status = await tb.read32(ADDR_HARNESS_CSR + HCSR_STATUS)
        done0 = bool(status & 0x01)
        done1 = bool(status & 0x02)
        if done0 and done1:
            done = True
            break
    assert done, f"cycle injectors did not finish within {max_cycles} cycles"

    # Read injector status and CRCs
    status0 = await tb.read32(ADDR_CYCLE_INJECTOR0 + CI_STATUS)
    status1 = await tb.read32(ADDR_CYCLE_INJECTOR1 + CI_STATUS)
    err0 = await tb.read32(ADDR_CYCLE_INJECTOR0 + CI_ERR_FLAG)
    err1 = await tb.read32(ADDR_CYCLE_INJECTOR1 + CI_ERR_FLAG)

    assert err0 == 0, f"ci0 error flag: 0x{err0:08x}"
    assert err1 == 0, f"ci1 error flag: 0x{err1:08x}"

    rsp_lo0 = await tb.read32(ADDR_CYCLE_INJECTOR0 + CI_RSP_CRC_LO)
    rsp_hi0 = await tb.read32(ADDR_CYCLE_INJECTOR0 + CI_RSP_CRC_HI)
    rsp_lo1 = await tb.read32(ADDR_CYCLE_INJECTOR1 + CI_RSP_CRC_LO)
    rsp_hi1 = await tb.read32(ADDR_CYCLE_INJECTOR1 + CI_RSP_CRC_HI)
    rsp_crc0 = (rsp_hi0 << 32) | rsp_lo0
    rsp_crc1 = (rsp_hi1 << 32) | rsp_lo1

    dut._log.info(f"ci0 status=0x{status0:08x} err=0x{err0:08x} rsp_crc=0x{rsp_crc0:016x}")
    dut._log.info(f"ci1 status=0x{status1:08x} err=0x{err1:08x} rsp_crc=0x{rsp_crc1:016x}")

    # Read a few tally bins
    bins = []
    for i in range(8):
        val = await tb.read64(ADDR_TALLY_CNT + i * 8)
        bins.append(val)
        dut._log.info(f"tally bin[{i}] = {val}")

    # Observation-alive check: the MonBus path (cache monlite -> arbiter ->
    # group -> tally) must actually count events. A config mistake that
    # silences it (BUG-004: group filter masks all-ones, which the group
    # interprets as "drop every packet type") passes every other assertion
    # in this test -- only the bins catch it.
    assert sum(bins) > 0, \
        "tally bins all zero: MonBus observation path is silent"


async def _load_default_profile(tb):
    await tb.write32(ADDR_TALLY_CFGW + TALLY_CAM_CLEAR, 0)
    for key, idx in _default_profile():
        await tb.write32(ADDR_TALLY_CFGW + TALLY_CAM_KEY, key)
        await tb.write32(ADDR_TALLY_CFGW + TALLY_CAM_LOAD, (1 << 31) | (idx & 0xFF))


async def _run_burst(tb, count: int, *, outstanding: int = 1):
    """Program both injectors on the same 4 KB region and run to done.

    outstanding = CTRL[23:16], requests the injector keeps in flight
    (TASK-002); 1 is the original blocking behaviour."""
    ctrl = ((outstanding & 0xFF) << 16) | (64 << 8)
    for ci_base, seed in [(ADDR_CYCLE_INJECTOR0, 0x1234_5678),
                          (ADDR_CYCLE_INJECTOR1, 0xDEAD_BEEF)]:
        await tb.write32(ci_base + CI_SEED, seed)
        await tb.write32(ci_base + CI_ADDR_BASE, 0x0000_0000)
        await tb.write32(ci_base + CI_ADDR_MASK, 0x0000_0FFF)
        await tb.write32(ci_base + CI_TRANS_COUNT, count)
        await tb.write32(ci_base + CI_CTRL, ctrl)
    await tb.write32(ADDR_CYCLE_INJECTOR0 + CI_CTRL, ctrl | 0x01)
    await tb.write32(ADDR_CYCLE_INJECTOR1 + CI_CTRL, ctrl | 0x01)

    for _ in range(500_000):
        status = await tb.read32(ADDR_HARNESS_CSR + HCSR_STATUS)
        if (status & 0x03) == 0x03:
            return
    raise AssertionError("cycle injectors did not finish")


async def _read_bins(tb, n: int = 8):
    return [await tb.read64(ADDR_TALLY_CNT + i * 8) for i in range(n)]


@cocotb.test(timeout_time=5000, timeout_unit="ms")
async def tally_clear_freeze_test(dut):
    """harness_csr CTRL[0]=tally_clear (write-1-pulse) and CTRL[1]=tally_freeze
    (level) drive monbus_tally_axil. Pins the amber TASK-001 item-1 wiring;
    before it, CTRL was a dead register and both ports were tied off.

    Clear protocol (load-bearing): the MonBus path must DRAIN before the
    clear pulse. tally_clear realigns the tally's 3-beat reassembler, but
    cannot flush a partial record buffered in the upstream group -- a clear
    landing mid-record phase-shifts the record stream and every later packet
    lands in UNEXPECTED. So: settle, freeze, clear. UNEXPECTED is read as a
    canary: misassembly would pump it."""
    clk_task = cocotb.start_soon(_manual_clock(dut))
    tb = AmberPairHarnessAXILTest(dut, clk_task)
    await tb.reset()
    await _load_default_profile(tb)

    async def settle(cycles=256):
        for _ in range(cycles):
            await cocotb.triggers.RisingEdge(dut.aclk)

    async def read_unexpected():
        return await tb.read64(ADDR_TALLY_CNT + 32 * 8)

    # Burst 1: events accumulate.
    await _run_burst(tb, count=48)
    await settle()  # drain the MonBus path into the bins
    assert sum(await _read_bins(tb)) > 0, "burst 1 produced no tally events"
    unc0 = await read_unexpected()

    # CTRL[0] is W1P: write 1 -> one-cycle clear pulse, reads back 0.
    # Freeze first (counting stops; the drained path holds no partial
    # records), then clear with the freeze bit held set.
    await tb.write32(ADDR_HARNESS_CSR + HCSR_CTRL, 0x2)
    await tb.write32(ADDR_HARNESS_CSR + HCSR_CTRL, 0x3)
    ctrl = await tb.read32(ADDR_HARNESS_CSR + HCSR_CTRL)
    assert ctrl & 0x1 == 0, f"CTRL[0] must be self-clearing (read 0x{ctrl:08x})"
    assert ctrl & 0x2, f"CTRL[1] freeze level did not stick (read 0x{ctrl:08x})"

    # The clear walks the count SRAM one entry per cycle; 256 cycles covers
    # any legal TALLY_ADDR_BITS with margin.
    await settle()
    bins = await _read_bins(tb)
    assert sum(bins) == 0, f"tally_clear left nonzero bins: {bins}"
    assert await read_unexpected() == 0, "clear did not zero UNEXPECTED"

    # Frozen burst: events dropped (not counted) while held.
    await _run_burst(tb, count=48)
    await settle()
    bins = await _read_bins(tb)
    assert sum(bins) == 0, f"tally counted while frozen: {bins}"
    assert await read_unexpected() == 0, "UNEXPECTED grew while frozen"

    # Unfreeze: counting resumes.
    await tb.write32(ADDR_HARNESS_CSR + HCSR_CTRL, 0x0)
    await _run_burst(tb, count=48)
    await settle()
    assert sum(await _read_bins(tb)) > 0, "tally did not resume after unfreeze"


@cocotb.test(timeout_time=5000, timeout_unit="ms")
async def injector_latency_test(dut):
    """Cycle-injector latency instrumentation (formal/amber TASK-001 item 2):
    per-request latency min/max/sum, 8-bucket log2 histogram, run-cycle count.
    On the pre-instrument RTL these offsets decoded to 0xDEAD_BEEF, so every
    assertion below is discriminating."""
    clk_task = cocotb.start_soon(_manual_clock(dut))
    tb = AmberPairHarnessAXILTest(dut, clk_task)
    await tb.reset()

    # Pre-run: zero samples -> LAT_MIN reads 0 (not the all-ones init).
    assert await tb.read32(ADDR_CYCLE_INJECTOR0 + CI_LAT_MIN) == 0

    count = 64
    await _run_burst(tb, count=count)

    for ci_base, name in [(ADDR_CYCLE_INJECTOR0, "ci0"),
                          (ADDR_CYCLE_INJECTOR1, "ci1")]:
        lat_min = await tb.read32(ci_base + CI_LAT_MIN)
        lat_max = await tb.read32(ci_base + CI_LAT_MAX)
        run_cycles = await tb.read32(ci_base + CI_RUN_CYCLES)
        sum_lo = await tb.read32(ci_base + CI_LAT_SUM_LO)
        sum_hi = await tb.read32(ci_base + CI_LAT_SUM_HI)
        lat_sum = (sum_hi << 32) | sum_lo
        hist = [await tb.read32(ci_base + CI_LAT_HIST0 + 4 * i) for i in range(8)]

        dut._log.info(f"{name}: min={lat_min} max={lat_max} sum={lat_sum} "
                      f"run_cycles={run_cycles} hist={hist}")

        assert 0 < lat_min <= lat_max, \
            f"{name}: bad min/max {lat_min}/{lat_max}"
        assert count * lat_min <= lat_sum <= count * lat_max, \
            f"{name}: sum {lat_sum} outside [{count * lat_min}, {count * lat_max}]"
        assert sum(hist) == count, \
            f"{name}: histogram total {sum(hist)} != {count}"
        # Busy time covers every wait cycle plus issue/address cycles.
        assert lat_sum <= run_cycles, \
            f"{name}: latency sum {lat_sum} exceeds run cycles {run_cycles}"


@cocotb.test(timeout_time=5000, timeout_unit="ms")
async def tally_latch_bank_test(dut):
    """16-deep first-event latch bank (formal/amber TASK-001 items 1+3):
    an all-types watch mask fills all 16 slots, slot readback is indexed by
    LATCH_SEL, timestamps are non-decreasing, and tally_clear re-arms."""
    clk_task = cocotb.start_soon(_manual_clock(dut))
    tb = AmberPairHarnessAXILTest(dut, clk_task)
    await tb.reset()
    await _load_default_profile(tb)

    # Arm the watch for every packet type (mask bit per 4-bit pkt_type).
    await tb.write32(ADDR_TALLY_CFGW + TALLY_WATCH_CTRL, (1 << 31) | 0xFFFF)
    await _run_burst(tb, count=48)

    status = await tb.read32(ADDR_TALLY_CFGR + TALLY_LATCH_STATUS)
    fill = status & 0xFFFF
    assert fill == TALLY_NUM_LATCH, \
        f"latch fill {fill} != {TALLY_NUM_LATCH} (bank deeper than 4 wanted)"

    # Walk all slots: VALID set, timestamps non-decreasing in capture order.
    prev_ts = -1
    for slot in range(TALLY_NUM_LATCH):
        await tb.write32(ADDR_TALLY_CFGW + TALLY_LATCH_SEL, slot)
        st = await tb.read32(ADDR_TALLY_CFGR + TALLY_LATCH_STATUS)
        assert st & (1 << 16), f"slot {slot} invalid with fill={fill}"
        ts_lo = await tb.read32(ADDR_TALLY_CFGR + TALLY_LATCH_TS_LO)
        ts_hi = await tb.read32(ADDR_TALLY_CFGR + TALLY_LATCH_TS_HI)
        ts = (ts_hi << 32) | ts_lo
        assert ts >= prev_ts, f"slot {slot} ts {ts} < previous {prev_ts}"
        prev_ts = ts

    # tally_clear re-arms the bank (item 1's real payoff).
    await tb.write32(ADDR_HARNESS_CSR + HCSR_CTRL, 0x1)
    for _ in range(256):
        await cocotb.triggers.RisingEdge(dut.aclk)
    status = await tb.read32(ADDR_TALLY_CFGR + TALLY_LATCH_STATUS)
    assert (status & 0xFFFF) == 0, f"latch fill not re-armed: 0x{status:08x}"


async def _ci_snapshot(tb, ci_base):
    """Every injector counter the pipelined-run test compares."""
    async def r64(lo, hi):
        return ((await tb.read32(ci_base + hi)) << 32) | await tb.read32(ci_base + lo)
    return {
        "acc": await tb.read32(ci_base + CI_ACC_COUNT),
        "rsp": await tb.read32(ci_base + CI_RSP_COUNT),
        "err": await tb.read32(ci_base + CI_ERR_FLAG),
        "rsp_crc": await r64(CI_RSP_CRC_LO, CI_RSP_CRC_HI),
        "wdata_crc": await r64(CI_WDATA_CRC_LO, CI_WDATA_CRC_HI),
        "lat_min": await tb.read32(ci_base + CI_LAT_MIN),
        "lat_max": await tb.read32(ci_base + CI_LAT_MAX),
        "lat_sum": await r64(CI_LAT_SUM_LO, CI_LAT_SUM_HI),
        "run_cycles": await tb.read32(ci_base + CI_RUN_CYCLES),
        "hist": [await tb.read32(ci_base + CI_LAT_HIST0 + 4 * i) for i in range(8)],
        "outst_max": await tb.read32(ci_base + CI_OUTST_MAX),
        "outst_sum": await r64(CI_OUTST_SUM_LO, CI_OUTST_SUM_HI),
        "stall": await tb.read32(ci_base + CI_STALL_CYCLES),
        "cstall": await tb.read32(ci_base + CI_CREDIT_STALL),
    }


@cocotb.test(timeout_time=5000, timeout_unit="ms")
async def injector_pipeline_test(dut):
    """Pipelined cycle injector (cache-ip common-ip TASK-002).

    The same 256-transaction burst runs at depth 1 (the original blocking
    behaviour), depth 8 and depth 255 (clamped to MAX_OUTSTANDING). The
    issued sequence is depth-invariant, so both CRCs must match across the
    three; the parallelism counters must be consistent with the depth; and
    the pipelined runs must not take longer than the blocking one. On the
    pre-TASK-002 RTL CTRL[23:16] was ignored and OUTST_MAX decoded to
    0xDEAD_BEEF, so every assertion below is discriminating."""
    clk_task = cocotb.start_soon(_manual_clock(dut))
    tb = AmberPairHarnessAXILTest(dut, clk_task)
    await tb.reset()

    count = 256
    depths = (1, 8, 255)
    snaps = {}
    for depth in depths:
        await _run_burst(tb, count=count, outstanding=depth)
        snaps[depth] = {name: await _ci_snapshot(tb, base)
                        for base, name in [(ADDR_CYCLE_INJECTOR0, "ci0"),
                                           (ADDR_CYCLE_INJECTOR1, "ci1")]}
        for name, s in snaps[depth].items():
            dut._log.info(
                f"depth {depth} {name}: acc={s['acc']} rsp={s['rsp']} err={s['err']} "
                f"lat={s['lat_min']}/{s['lat_sum'] / count:.2f}/{s['lat_max']} "
                f"run_cycles={s['run_cycles']} cpt={s['run_cycles'] / count:.2f} "
                f"outst_max={s['outst_max']} mlp={s['outst_sum'] / max(s['run_cycles'], 1):.2f} "
                f"stall={s['stall']} credit_stall={s['cstall']} "
                f"rsp_crc=0x{s['rsp_crc']:08x} wdata_crc=0x{s['wdata_crc']:08x}")

    for name in ("ci0", "ci1"):
        base = snaps[1][name]
        for depth in depths:
            s = snaps[depth][name]
            credit = min(max(depth, 1), CI_MAX_OUTSTANDING)
            assert s["acc"] == count and s["rsp"] == count, \
                f"{name} depth {depth}: acc/rsp {s['acc']}/{s['rsp']} != {count}"
            assert s["err"] == 0, f"{name} depth {depth}: ERR_FLAG set"
            assert sum(s["hist"]) == count, \
                f"{name} depth {depth}: histogram total {sum(s['hist'])} != {count}"
            assert count * s["lat_min"] <= s["lat_sum"] <= count * s["lat_max"], \
                f"{name} depth {depth}: lat_sum {s['lat_sum']} outside min/max bounds"
            assert 1 <= s["outst_max"] <= credit, \
                f"{name} depth {depth}: OUTST_MAX {s['outst_max']} outside 1..{credit}"
            assert s["outst_sum"] <= s["run_cycles"] * credit, \
                f"{name} depth {depth}: OUTST_SUM {s['outst_sum']} exceeds run_cycles x credit"
            # The issued sequence does not depend on the depth.
            assert s["rsp_crc"] == base["rsp_crc"], \
                f"{name} depth {depth}: rsp CRC 0x{s['rsp_crc']:08x} != depth-1 0x{base['rsp_crc']:08x}"
            assert s["wdata_crc"] == base["wdata_crc"], \
                f"{name} depth {depth}: wdata CRC 0x{s['wdata_crc']:08x} != depth-1 0x{base['wdata_crc']:08x}"
            # No request completes faster than the idle-pipe resident-hit
            # floor measured at depth 1.  Equality is NOT required: under a
            # sustained pipelined stream a hit can meet a busy lookup stage
            # and wait a cycle, so a run in which no hit ever found the pipe
            # idle reports a floor one above (jet ci1 at depth 16: 4 vs 3,
            # deterministic).  A lower minimum would mean a response was
            # mis-timed (or a stray one counted).
            assert s["lat_min"] >= base["lat_min"], \
                f"{name} depth {depth}: lat_min {s['lat_min']} below the depth-1 floor {base['lat_min']}"
            assert s["run_cycles"] <= base["run_cycles"], \
                f"{name} depth {depth}: run_cycles {s['run_cycles']} > depth-1 {base['run_cycles']}"
        assert base["outst_max"] == 1, \
            f"{name}: depth 1 reached OUTST_MAX {base['outst_max']}"
        # The credit stall counter is the injector throttling itself: at depth 1
        # it must be the only thing that ever held an address back.
        if INJECTOR_EXPECT_PIPELINED:
            s8 = snaps[8][name]
            assert s8["outst_max"] >= 2, \
                f"{name} depth 8: the cache never had two requests in flight (OUTST_MAX {s8['outst_max']})"
            assert s8["run_cycles"] < base["run_cycles"], \
                f"{name} depth 8: no throughput gain ({s8['run_cycles']} vs {base['run_cycles']} cycles)"


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_amber_pair_harness_axil(request, test_level):
    module = "test_amber_pair_harness_axil"
    dut_name = "amber_pair_harness_host_tb"
    toplevel = dut_name

    log_dir = os.path.join(AMBER_FRAMEWORK_ROOT, "dv", "tests", "log")
    tests_dir = os.path.join(AMBER_FRAMEWORK_ROOT, "dv", "tests")
    test_name = f"{module}_{test_level}"
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f"{test_name}.log")
    results_path = os.path.join(log_dir, f"results_{test_name}.xml")

    # The amber Genesys2 framework root is not in the global env_python defaults.
    os.environ['AMBER_FRAMEWORK_ROOT'] = AMBER_FRAMEWORK_ROOT

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/fpga-systems/Genesys2/cache-ip/amber/dv/filelists/amber_pair_harness_host_tb.f'
    )

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'COCOTB_TEST_TIMEOUT': '600000',
        'AMBER_FRAMEWORK_ROOT': AMBER_FRAMEWORK_ROOT,
        **level_env(test_level),
    }

    create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    # Match the harness-integration lint waiver set from make/fpga_flow.mk so
    # the cocotb simulation elaborates the same design `make lint` gates.
    compile_args = [
        FIELD_COMBO_VLT, "-Wno-UNUSED", "-Wno-UNDRIVEN", "-Wno-WIDTH",
        "-Wno-CASEINCOMPLETE", "-Wno-SELRANGE", "-Wno-DECLFILENAME",
        "-Wno-UNUSEDSIGNAL", "-Wno-VARHIDDEN", "-Wno-IMPLICIT",
        "-Wno-CASEOVERLAP", "-Wno-MODDUP", "-Wno-PINMISSING",
    ]

    run(
        python_search=[tests_dir, repo_root],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=toplevel,
        module=module,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=True,
        keep_files=True,
        compile_args=compile_args,
    )
