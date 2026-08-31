# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

# TODO: extend every AXI4 / GAXI BFM-driven scenario in this suite with
# the framework's random timing profiles (see bin/TBClasses/amba/
# amba_random_configs.py — backtoback / constrained / fast / slow_*).
# The macro test today only exercises engine-driven traffic; mixing in
# BFM-driven peers with profile rotation will catch interface-level edge
# conditions (skid races, FIFO drain corners, mid-burst stalls) that a
# single timing profile misses.
"""Smoke test for ddr2_char_macro.

Wires up the two AXI4 master-side characterization engines + the
pumice controller behind one tb_top, then runs a tiny end-to-end
workload:

  1. Bring up APB CSR + DFI loopback through the existing
     DDR2LPDDR2TopTB infrastructure.
  2. Wait for init_done.
  3. Program the writer engine for a small LFSR workload, fire
     cfg_wr_start, wait cfg_wr_done.
  4. Program the reader engine to walk the same addresses, fire
     cfg_rd_start, wait cfg_rd_done.
  5. Assert no integrity errors and the CRC contract holds.

The controller's DFI side talks to the existing DFISlavePHY BFM
backed by MemoryModel — so writes persist and reads return the same
bytes.
"""

import logging
import os
import random
import sys

import cocotb
import pytest
from cocotb.triggers import ClockCycles, RisingEdge, Timer
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

# Reuse the controller's TB infrastructure for APB + DFI bring-up. The
# class only touches phy_dfi_* / s_apb_* / memtype_i / t_phy_wrlat_i etc.,
# all of which exist on ddr2_char_macro_tb_top with the same names.
_CTRL_DV_DIR = os.path.abspath(os.path.join(
    "/mnt/data/github/RTLDesignSherpa",
    "projects/components/memory-controllers/pumice-ddr2-lpddr2/dv"))
if _CTRL_DV_DIR not in sys.path:
    sys.path.insert(0, _CTRL_DV_DIR)

from tbclasses.pumice_top_tb import DDR2LPDDR2TopTB  # noqa: E402

# The generators are programmed over APB, by register name, exactly as the host
# programs them on the board -- see chargen_driver for why that equivalence is
# the point rather than a nicety.
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "tbclasses"))
from chargen_driver import ChargenDriver  # noqa: E402


_NBA_SETTLE_PS = 100


# ---------------------------------------------------------------------------
# Engine cfg helpers -- program over APB, by register name.
#
# These used to poke `dut.cfg_*.value` directly, which was possible when the
# macro exported one writer's and one reader's config as flat ports. It is gone
# for two reasons. There are sixteen engines now, so the flat surface would be
# some six hundred wires. And more importantly, poking ports meant the register
# decode those values arrive through was never exercised in simulation -- a
# register that decoded to the wrong address could only be found on silicon.
# Programming over APB makes the sim drive the same path the board does.
# ---------------------------------------------------------------------------


# NAMES. One concept, one name -- the tree already had several for each and
# this file is not adding more:
#   DRAM_BL            JEDEC burst length in DEVICE beats (CSR DFI_PHASE.bl,
#                      RTL DRAM_BL/BL). Scaled to pumice beats as BL_PUMICE.
#   BURST_LEN_MULTIPLE AXI beats in one DRAM burst. Same quantity the RTL
#                      calls CHUNK_BEATS (ifc/chopper/splitter), BURST_WORDS
#                      (pumice_core) and EXP_AXI_BEATS (wr_intake).
#   DFI_RATE           DFI phases per controller clock.
# All three are passed to the RTL explicitly; none is inherited from a
# parameter default, because a default is what silently went stale at BL8.
DFI_RATE = 2        # must track ddr2_char_macro_tb_top's DFI_RATE

# AXI beats in ONE full DRAM burst, for THIS build:
#     DRAM_BL * DRAM_DEVICE_WIDTH / AXI_DATA_WIDTH = 8 * 64 / 64 = 8
# Every generator shape below is expressed as a whole number of these, so each
# AXI burst maps to an integer number of DFI BL8 transactions. Perf numbers are
# only meaningful that way: a burst that does not fill a DRAM burst still costs
# a whole ACT/CAS/precharge cycle at the device, so a short burst reports
# throughput far below what the controller can actually sustain, and a ragged
# one additionally drags in the masked-write path.
#
# The shapes used to say burst=1/2/4 from when DRAM_BL was 4 and the comment
# below read "Burst len = BL=4 so each AXI burst maps 1-to-1 to a DRAM BL
# burst". Commit 72a73fe2 moved DDR2 to BL8 for the on-silicon read fix and did
# not update them, so every shape has been a sub-burst ever since.
DRAM_BL = 8         # must track ddr2_char_macro_tb_top's DRAM_BL
# The board carries an MT47H64M16 -- x16, 2 bytes per device word. The RTL
# decodes the column address at DEVICE granularity (BYTE_OFFSET_WIDTH), so
# the model must be told the same or it stores at beat granularity and the
# two disagree about where a write landed.
DRAM_DEVICE_BYTES = 2   # x16 device
DRAM_BEAT_BYTES   = 4   # 32-bit pumice DRAM beat
BURST_LEN_MULTIPLE = 8


def _chargen(dut, log=None) -> ChargenDriver:
    """The generator-config driver for this dut, created once.

    Cached on the dut because the helpers below are module-level functions
    that only receive `dut` -- threading a driver through every call site
    would be a bigger edit than the behaviour warrants.
    """
    drv = getattr(dut, "_chargen_driver", None)
    if drv is None:
        drv = ChargenDriver(dut, clock=dut.pclk, prefix="s_chargen_apb",
                            addr_width=12, log=log)
        dut._chargen_driver = drv
    return drv


async def _drive_engine_idle(dut) -> None:
    """Put the generator config in its idle state.

    There is nothing to drive any more. Every chargen_regs field resets to 0,
    which means txn_count = 0 and no GO pulse, so all sixteen engines sit in
    S_IDLE out of reset by construction rather than because the bench held
    their ports low. Resetting the APB bus is the whole job.

    Kept as a named step because the call sites read better for it, and
    because "the engines are idle here" is worth being able to point at.
    """
    await _chargen(dut).reset()


def _check_full_burst(burst_len: int, who: str) -> None:
    """A half burst is ILLEGAL in the generators. Reject it here.

    Not a warning and not a perf hint: a generator burst that is not a whole
    number of DFI BL8 transactions is an invalid configuration of this
    environment. Any behaviour observed under one says nothing about the
    design -- it is an illegal stimulus, so results from it are void rather
    than a bug to chase.

    Checked HERE rather than by the RTL's BURST_LEN_MULTIPLE assertion: the
    constraint belongs to the environment that picks the value, not to the
    design. The controller itself accepts ANY legal AxLEN (see
    test_pumice_top_partial_strb / ..._partial_rd / ..._burst_len); it is the
    perf generators that are restricted, because a partial DRAM burst still
    costs the device a full ACT/CAS cycle and so reports throughput well
    below what the controller sustains.

    This exists because three separate places held a stale BL4-era burst
    length after DDR2 moved to BL8 (the shape table, and BURST = 4 in both the
    pacing-sweep and ooo-schmoo suites). All were invisible until checked.
    """
    if burst_len % BURST_LEN_MULTIPLE:
        raise AssertionError(
            f"{who}: burst_len={burst_len} is ILLEGAL -- generator bursts "
            f"must be whole multiples of BURST_LEN_MULTIPLE="
            f"{BURST_LEN_MULTIPLE} (one full DFI BL8 transaction). This is an "
            f"invalid configuration, not a slow one: fix the shape. The "
            f"controller's own sub-burst handling is covered at the "
            f"controller level -- test_pumice_top.py::"
            f"test_pumice_top_partial_strb and ..._partial_rd.")


async def _program_writer(dut, *, start_addr: int, stride_0: int,
                          burst_len: int, txn_count: int,
                          axi_id: int = 0, axi_size: int = 3,
                          lfsr_seed: int = 0, id_mode: int = 0,
                          gap: int = 0, gen: int = 0,
                          wrap_mask_0: int = 0, wrap_mask_1: int = 0) -> None:
    """Stage write generator `gen` over APB. Does NOT start it.

    Staging and launching are separate on purpose: GO starts every selected
    generator on one cycle, and that is only meaningful if the staging is
    already done. `gap` is programmed here too -- it used to be poked
    separately at the call site, between programming and the start pulse,
    which worked only because there was one engine to poke.
    """
    _check_full_burst(burst_len, "writer")
    await _chargen(dut).program_writer(
        gen, start_addr=start_addr, stride_0=stride_0, burst_len=burst_len,
        txn_count=txn_count, axi_id=axi_id, id_mode=id_mode,
        axi_size=axi_size, lfsr_seed=lfsr_seed, gap=gap,
        wrap_mask_0=wrap_mask_0, wrap_mask_1=wrap_mask_1,
    )


async def _program_reader(dut, *, start_addr: int, stride_0: int,
                          burst_len: int, txn_count: int,
                          axi_id: int = 0, axi_size: int = 3,
                          lfsr_seed: int = 0, id_mode: int = 0,
                          gap: int = 0, gen: int = 0,
                          wrap_mask_0: int = 0, wrap_mask_1: int = 0) -> None:
    """Stage read generator `gen` over APB. Does NOT start it."""
    _check_full_burst(burst_len, "reader")
    await _chargen(dut).program_reader(
        gen, start_addr=start_addr, stride_0=stride_0, burst_len=burst_len,
        txn_count=txn_count, axi_id=axi_id, id_mode=id_mode,
        axi_size=axi_size, lfsr_seed=lfsr_seed, gap=gap,
        wrap_mask_0=wrap_mask_0, wrap_mask_1=wrap_mask_1,
    )


async def _start_writers(dut, mask: int = 0x01) -> None:
    """Launch the selected write generators -- one write, one start edge."""
    await _chargen(dut).go(wr_mask=mask)


async def _start_readers(dut, mask: int = 0x01) -> None:
    await _chargen(dut).go(rd_mask=mask)


async def _wait_done(dut, done_signal: str, timeout: int = 500_000) -> None:
    sig = getattr(dut, done_signal)
    for _ in range(timeout):
        await RisingEdge(dut.mc_clk)
        await Timer(_NBA_SETTLE_PS, units="ps")
        if int(sig.value):
            return
    raise TimeoutError(
        f"{done_signal} did not assert within {timeout} cycles"
    )


async def _assert_engines_clean(dut, gen: int = 0, context: str = "") -> None:
    """Assert generator `gen` finished with no protocol or data errors.

    Reads the per-generator STATUS register rather than a pin, because with
    sixteen engines "an error happened" is not useful on its own -- the failure
    message has to say WHICH generator, and the register is what knows.
    """
    drv = _chargen(dut)
    st = await drv.reader_status(gen)
    wr_err, rd_err = await drv.errors()

    assert not (wr_err >> gen) & 1, (
        f"writer {gen} latched a BRESP error{' ' + context if context else ''}")
    assert not st["rresp_error"], (
        f"reader {gen} latched an RRESP error{' ' + context if context else ''}")
    assert not st["data_error"], (
        f"reader {gen} data error{' ' + context if context else ''}")
    assert not st["stray_beat_error"], (
        f"reader {gen} saw stray R beats ({st['stray_beats']}) "
        f"{context}".rstrip())
    assert st["beats_mismatched"] == 0, (
        f"reader {gen} mismatched {st['beats_mismatched']} beats "
        f"{context}".rstrip())


async def _assert_crc_match(dut, gen: int = 0, context: str = "") -> None:
    """Assert the writer/reader pair on `gen` computed the same CRC."""
    exp, act = await _chargen(dut).crc_pair(gen)
    assert exp == act, (
        f"CRC mismatch on pair {gen}"
        f"{' (' + context + ')' if context else ''}: "
        f"exp=0x{exp:08X} act=0x{act:08X}")



# ---------------------------------------------------------------------------
# cocotb test entry
# ---------------------------------------------------------------------------


@cocotb.test(timeout_time=300, timeout_unit="ms")
async def cocotb_test_ddr2_char_macro(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke")
    mem_type  = os.environ.get("MEM_TYPE", "DDR2").upper()

    tb = DDR2LPDDR2TopTB(dut, num_ranks=1, dram_bl=DRAM_BL,
                            dram_device_bytes=DRAM_DEVICE_BYTES,
                            dram_beat_width=DRAM_BEAT_BYTES * 8)
    await _drive_engine_idle(dut)
    # Drain the reader-engine debug FIFO via the framework's GAXISlave.
    # Each received packet carries (actual, expected, mismatch) for one
    # R beat the engine observed — gives the test log EXACTLY which beat
    # went wrong and what the engine's LFSR mirror expected at that
    # phase. multi_sig=True binds the three named signals
    # (rd_dbg_actual, rd_dbg_expected, rd_dbg_mismatch) under the
    # rd_dbg_ prefix; the slave drives rd_dbg_ready.
    from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
    from CocoTBFramework.components.shared.field_config import (
        FieldConfig, FieldDefinition,
    )
    dbg_field_cfg = FieldConfig()
    dbg_field_cfg.add_field(FieldDefinition(name="actual",   bits=64))
    dbg_field_cfg.add_field(FieldDefinition(name="expected", bits=64))
    dbg_field_cfg.add_field(FieldDefinition(name="mismatch", bits=1))
    rd_dbg_slave = GAXISlave(
        dut=dut, title="rd_dbg_drain", prefix="rd_dbg",
        clock=dut.mc_clk, field_config=dbg_field_cfg,
        multi_sig=True, log=tb.log,
    )

    def _on_dbg_beat(packet):
        actual   = getattr(packet, "actual", 0)
        expected = getattr(packet, "expected", 0)
        mismatch = getattr(packet, "mismatch", 0)
        tag = "MISMATCH" if mismatch else "ok"
        tb.log.info(
            "RDDBG %s actual=0x%016X expected=0x%016X",
            tag, actual, expected,
        )

    rd_dbg_slave.add_callback(_on_dbg_beat)
    await tb.reset(mem_type=mem_type, init_complete_delay=20)
    tb.init_register_map()
    tb.init_apb4_master()
    await tb.apb4_master.reset_bus()
    # Second APB window: the generator config block. Created here so the log
    # goes to the same place, and reset before anything is staged.
    await _chargen(dut, log=tb.log).reset()
    tb.init_dfi_slave()
    await tb.program_defaults(dfi_rate=DFI_RATE, dram_bl=DRAM_BL)
    tb.init_dfi_monitor()        # capture DFI cmd/wr-data/rd-data queues
    tb.start_axi_wr_snoop()      # snoop AXI WR side as WR-path ground truth
    tb.start_axi_rd_snoop()      # snoop AXI RD side for RD-path verify
    await tb.wait_for_init_done()

    # 1x1 known-good; 1x2 isolates multi-beat-in-burst; 2x1 isolates
    # multi-burst; 2x2 was the original failing config.
    _B = BURST_LEN_MULTIPLE          # one full DFI BL8 transaction
    SHAPES = {
        # <k DRAM bursts per AXI burst> x <n AXI bursts>. Every entry is a
        # whole number of DRAM bursts (see BURST_LEN_MULTIPLE).
        "smoke":     dict(burst=1 * _B, n=1,    base=0x0000_2000),
        "smoke_1x2": dict(burst=2 * _B, n=1,    base=0x0000_2040),
        "smoke_2x1": dict(burst=1 * _B, n=2,    base=0x0000_2080),
        "smoke_2x2": dict(burst=2 * _B, n=2,    base=0x0000_20C0),
        # Scaled workloads: one DRAM burst per AXI burst. Reader walks the
        # same descriptor + per-beat compares against the local LFSR.
        "kb_4burst":  dict(burst=1 * _B, n=4,    base=0x0001_0000),
        "kb_16burst": dict(burst=1 * _B, n=16,   base=0x0001_0000),
        "kb_17burst": dict(burst=1 * _B, n=17,   base=0x0001_0000),
        "kb_20burst": dict(burst=1 * _B, n=20,   base=0x0001_0000),
        "kb_24burst": dict(burst=1 * _B, n=24,   base=0x0001_0000),
        "kb1":       dict(burst=1 * _B, n=32,   base=0x0001_0000),
        "kb4":       dict(burst=1 * _B, n=128,  base=0x0001_0000),
        "kb32":      dict(burst=1 * _B, n=1024, base=0x0001_0000),
        # The bl1_/bl2_ (sub-burst) and bl8_ shapes were retired here. The
        # generators are fixed to INTEGER MULTIPLES of one DFI BL8
        # transaction, so a sub-burst shape can no longer be expressed and
        # bl8_* had become a duplicate of kb1/kb4 at a different base.
        #
        # Sub-DRAM-burst handling is still covered, and covered better, at the
        # controller level where a byte-exact golden model is available:
        #   test_pumice_top.py  test_pumice_top_partial_strb  (24 cases)
        #   test_pumice_top.py  test_pumice_top_partial_rd    (16 cases)
        #   test_pumice_top.py  test_pumice_top_burst_len     (8 lengths)
        #   test_pumice_top_geared.py  ..._short_burst        (down-gear)
        # Those check every byte and are mutation-verified; the engine
        # generators can only check an LFSR mirror, which is what made a
        # sub-burst failure here read as an opaque phase offset.
    }
    if test_type == "ooo_pacing_schmoo":
        # Combined OOO + pacing + schmoo sweep.
        #
        #   * id_mode != FIXED so each burst carries a different axi id
        #     → the controller's CAMs see id-spread reads + writes, and
        #     the scheduler can reorder across ids (OOO permitted by
        #     AXI4 cross-id).
        #   * axi_id_base swept 0..15 — covers every IW=4 bit start
        #     position. With id_mode=COUNTER the per-burst ids wrap
        #     through all 16 IDs.
        #   * Writes drive FIRST (memory preset), then a schmoo'd
        #     rd_start_delay between wr_done and rd_start exposes
        #     different controller states to the read engine:
        #        0   cycles — rd arrives while wbuf still draining
        #       16   cycles — typical b-complete window
        #       64   cycles — quiescent, no in-flight writes
        #      256   cycles — long quiescent gap before reads
        #   * cfg_wr_gap / cfg_rd_gap pacing per schmoo step (folded
        #     into the same matrix entry to keep test count to 128).
        axi_id_base    = int(os.environ.get("OOO_AXI_ID", "0"))
        id_mode        = int(os.environ.get("OOO_ID_MODE", "1"))
        wr_gap         = int(os.environ.get("OOO_WR_GAP", "0"))
        rd_gap         = int(os.environ.get("OOO_RD_GAP", "0"))
        rd_start_delay = int(os.environ.get("OOO_RD_START_DELAY", "0"))
        tb.log.info(
            "ooo_pacing_schmoo: axi_id=%d id_mode=%d "
            "wr_gap=%d rd_gap=%d rd_start_delay=%d",
            axi_id_base, id_mode, wr_gap, rd_gap, rd_start_delay,
        )

        BURST = BURST_LEN_MULTIPLE   # one full DFI BL8 transaction
        N = 17  # past RD_CAM_DEPTH=16 — exercises slot reuse
        BASE = 0x0001_0000
        BYTES_PER_BEAT = 8
        STRIDE = BURST * BYTES_PER_BEAT
        SEED = 0xDEAD_BEEF

        # --- Writes: preset memory ---
        await _program_writer(dut, start_addr=BASE, stride_0=STRIDE,
                              burst_len=BURST, txn_count=N,
                              axi_id=axi_id_base, id_mode=id_mode,
                              lfsr_seed=SEED, gap=wr_gap)
        await _start_writers(dut)
        await _wait_done(dut, "gen_wr_done", timeout=1_000_000)

        # --- Schmoo: delay before reads kick off ---
        if rd_start_delay > 0:
            await ClockCycles(dut.mc_clk, rd_start_delay)

        # --- Reads: walk same descriptor with same id pattern ---
        await _program_reader(dut, start_addr=BASE, stride_0=STRIDE,
                              burst_len=BURST, txn_count=N,
                              axi_id=axi_id_base, id_mode=id_mode,
                              lfsr_seed=SEED, gap=rd_gap)
        await _start_readers(dut)
        await _wait_done(dut, "gen_rd_done", timeout=1_000_000)

        ctx = (f"axi_id={axi_id_base} id_mode={id_mode} "
               f"wr_gap={wr_gap} rd_gap={rd_gap} "
               f"rd_start_delay={rd_start_delay}")
        await _assert_engines_clean(dut, context=ctx)
        await _assert_crc_match(dut, context=ctx)
        tb.log.info(
            "ooo_pacing_schmoo OK axi_id=%d id_mode=%d "
            "wr_gap=%d rd_gap=%d rd_start_delay=%d",
            axi_id_base, id_mode, wr_gap, rd_gap, rd_start_delay,
        )

    elif test_type == "bank_parallel":
        # THE reason the generator array exists: eight writers and eight
        # readers running CONCURRENTLY, one per DRAM bank.
        #
        # Every other test in this file drives generator 0 and therefore one
        # address stream, which cannot distinguish a controller that refuses to
        # go bank-parallel from a harness that never asked it to. The flat
        # ~12.7 MB/s board result was eventually traced to the arbiter falling
        # back to a single oldest bank, and a single-stream bench could not have
        # told the difference.
        #
        # What this checks is CORRECTNESS under concurrency, not throughput: the
        # DFI loopback models no page timing, so bandwidth measured here means
        # nothing. Eight streams interleaving in the CAMs, the arbiter and the
        # read-return path is a real integrity test regardless.
        BURST = BURST_LEN_MULTIPLE
        BYTES_PER_BEAT = 8
        STRIDE = BURST * BYTES_PER_BEAT          # 64 B per burst

        # EACH GENERATOR SPANS TWO BANKS, so four generators keep all eight
        # busy. There are only four per direction (8+8 did not fit the part),
        # and one generator per bank would have left half the device idle --
        # which is the corner the whole array exists to provoke.
        #
        # The address generator computes base + ((index * stride) & wrap_mask),
        # so a wrap_mask of (window - 1) is a circular window of that size.
        # With pumice's ADDR_MAP.bank_lsb at 10, a contiguous 1024 B run stays
        # in one bank and the next 1024 B lands in the next -- so a 2048 B
        # window walks bank 2g, then bank 2g+1, then wraps.
        #
        # This is the HOST's model of the map it programmed; nothing in the RTL
        # forces it. Get bank_lsb wrong and this still runs, it just measures
        # something other than bank concurrency, which is why the mapping is
        # asserted rather than assumed.
        BANK_LSB    = 10
        BANK_STRIDE = 1 << BANK_LSB              # 1024 B per bank at this map
        BANKS_PER_GEN = 2
        WINDOW      = BANK_STRIDE * BANKS_PER_GEN
        WRAP_MASK   = WINDOW - 1
        N           = WINDOW // STRIDE           # cover the window exactly once
        BASE        = 0x0002_0000

        drv = _chargen(dut, log=tb.log)

        shape = await drv.gen_config()
        NUM_GEN  = shape["num_wr_gen"]
        GEN_MASK = (1 << NUM_GEN) - 1
        assert NUM_GEN == shape["num_rd_gen"], f"asymmetric array: {shape}"
        assert shape["num_banks"] % NUM_GEN == 0, (
            f"{shape} -- banks must divide evenly across generators or the "
            f"span-per-generator is not uniform and some banks see more "
            f"traffic than others purely by arithmetic")
        assert shape["num_banks"] // NUM_GEN == BANKS_PER_GEN, (
            f"{shape} implies {shape['num_banks'] // NUM_GEN} banks per "
            f"generator, but the address window above is built for "
            f"{BANKS_PER_GEN}")

        # Stage every generator first, then launch. Distinct seeds per
        # generator so a stream landing in the wrong window shows up as a CRC
        # mismatch rather than as data that happens to be right for the wrong
        # reason.
        for g in range(NUM_GEN):
            await _program_writer(dut, gen=g,
                                  start_addr=BASE + g * WINDOW,
                                  stride_0=STRIDE, wrap_mask_0=WRAP_MASK,
                                  burst_len=BURST, txn_count=N, axi_id=g,
                                  lfsr_seed=0xA5A5_0000 + g)
        await _start_writers(dut, mask=GEN_MASK)
        await _wait_done(dut, "gen_wr_done", timeout=2_000_000)

        for g in range(NUM_GEN):
            await _program_reader(dut, gen=g,
                                  start_addr=BASE + g * WINDOW,
                                  stride_0=STRIDE, wrap_mask_0=WRAP_MASK,
                                  burst_len=BURST, txn_count=N, axi_id=g,
                                  lfsr_seed=0xA5A5_0000 + g)
        await _start_readers(dut, mask=GEN_MASK)
        await _wait_done(dut, "gen_rd_done", timeout=2_000_000)

        # Every generator, not just the ones that happened to finish first.
        wr_done, rd_done = await drv.done()
        assert wr_done == GEN_MASK, f"writers still running: done=0x{wr_done:02X}"
        assert rd_done == GEN_MASK, f"readers still running: done=0x{rd_done:02X}"

        for g in range(NUM_GEN):
            await _assert_engines_clean(dut, gen=g, context=f"bank {g}")
            await _assert_crc_match(dut, gen=g, context=f"bank {g}")

        # And the hardware's own whole-run verdict, which is what the board
        # reports. Checking it here is what keeps the aggregate honest: it is
        # computed over LAUNCHED pairs, and a bug that made it ignore pairs
        # would pass every per-generator check above.
        assert int(dut.gen_crc_match.value) == 1, (
            "per-pair CRCs all matched but the hardware aggregate says they "
            "did not -- gen_crc_match's launched-pair mask is wrong")
        assert int(dut.gen_any_error.value) == 0, "aggregate error bit set"

        tb.log.info("bank_parallel OK: %d writers + %d readers, %d bursts each, "
                    "%d banks per generator (%d banks covered)",
                    NUM_GEN, NUM_GEN, N, BANKS_PER_GEN,
                    NUM_GEN * BANKS_PER_GEN)

    elif test_type == "pacing_sweep_b2b":
        # Engine-PACING sweep — NOT an AXI random-profile sweep.
        # The AXI_RANDOMIZER_CONFIGS BFM cross-product lives at the
        # controller-only level on test_pumice_core_macro. Here
        # the engines drive the AXI bus directly, so what we sweep is
        # the engines' own inter-burst pacing knobs (cfg_wr_gap,
        # cfg_rd_gap). Each gap pair stresses a different
        # writer/reader timing relationship — fast/fast catches
        # throughput corners; slow/fast catches cam-fill / wbuf-drain
        # corners; skewed (fast wr / slow rd) catches wr2rd_forward
        # arming windows.
        wr_gap = int(os.environ.get("WR_GAP", "0"))
        rd_gap = int(os.environ.get("RD_GAP", "0"))
        tb.log.info("pacing_sweep_b2b: wr_gap=%d rd_gap=%d", wr_gap, rd_gap)

        BURST = BURST_LEN_MULTIPLE   # one full DFI BL8 transaction
        N = 17  # past RD_CAM_DEPTH=16 — exercises slot reuse + same-id
        BASE = 0x0001_0000
        BYTES_PER_BEAT = 8
        STRIDE = BURST * BYTES_PER_BEAT
        SEED = 0xDEAD_BEEF

        await _program_writer(dut, start_addr=BASE, stride_0=STRIDE,
                              burst_len=BURST, txn_count=N, lfsr_seed=SEED,
                              gap=wr_gap)
        await _program_reader(dut, start_addr=BASE, stride_0=STRIDE,
                              burst_len=BURST, txn_count=N, lfsr_seed=SEED,
                              gap=rd_gap)

        await _start_writers(dut)
        await _wait_done(dut, "gen_wr_done", timeout=1_000_000)
        await _start_readers(dut)
        await _wait_done(dut, "gen_rd_done", timeout=1_000_000)

        ctx = f"wr_gap={wr_gap} rd_gap={rd_gap}"
        await _assert_engines_clean(dut, context=ctx)
        await _assert_crc_match(dut, context=ctx)
        tb.log.info(
            "pacing_sweep_b2b OK wr_gap=%d rd_gap=%d", wr_gap, rd_gap,
        )

    elif test_type in SHAPES:
        shape = SHAPES[test_type]
        BURST = shape["burst"]
        N     = shape["n"]
        BASE  = shape["base"]
        BYTES_PER_BEAT = 8   # AXI_DATA_WIDTH=64 → 8 bytes
        STRIDE = BURST * BYTES_PER_BEAT
        SEED = 0xDEAD_BEEF

        await _program_writer(dut, start_addr=BASE, stride_0=STRIDE,
                              burst_len=BURST, txn_count=N,
                              lfsr_seed=SEED)
        await _program_reader(dut, start_addr=BASE, stride_0=STRIDE,
                              burst_len=BURST, txn_count=N,
                              lfsr_seed=SEED)

        # Fire the writer first; let all B's drain before the reader
        # starts walking the same descriptor.
        await _start_writers(dut)
        await _wait_done(dut, "gen_wr_done")

        # Let any in-flight DFI WR data finish landing in memory.
        await ClockCycles(dut.mc_clk, 200)

        # === WR-PATH LOCALIZER ===
        # Compare every AXI WR beat the engine drove (snooped on
        # s_axi_w*) against what now sits in the DFISlavePHY's
        # MemoryModel. A mismatch means the controller corrupted on the
        # way AXI WR → wbuf → wr_beat_sequencer → DFI WR → memory.
        # AR / OOO / snarfing don't apply here — pure write side.
        wr_bad = tb.verify_memory_matches_axi_wr()
        if wr_bad is not None:
            byte_addr, exp_int, act_int = wr_bad
            tb.log.error(
                "WR PATH CORRUPTION: byte_addr=0x%X  "
                "AXI sent=0x%016X  Memory holds=0x%016X  "
                "(controller corrupted AXI WR → DFI WR → memory)",
                byte_addr, exp_int, act_int,
            )
        else:
            tb.log.info("WR-path localizer OK: every snooped AXI WR "
                        "beat matches MemoryModel state "
                        "(controller WR path clean)")

        # Dump 1 beat per burst so we can see which burst's data went
        # wrong if the reader's per-beat compare latches.
        for burst_idx in range(N):
            byte_addr = BASE + burst_idx * STRIDE
            payload = tb.peek_memory(byte_addr, BYTES_PER_BEAT)
            tb.log.info(
                "DUMP burst=%d addr=0x%X mem=%s",
                burst_idx, byte_addr,
                payload.hex() if hasattr(payload, 'hex') else str(payload))

        # Promote the WR-path failure to a test assertion (after the
        # diagnostic dump for easy log scanning).
        assert wr_bad is None, (
            f"WR PATH CORRUPTION at byte_addr=0x{wr_bad[0]:X}: "
            f"AXI sent 0x{wr_bad[1]:016X}, "
            f"Memory holds 0x{wr_bad[2]:016X}"
        )

        await _start_readers(dut)
        await _wait_done(dut, "gen_rd_done")

        # === RD-PATH LOCALIZER ===
        # For every AXI R beat returned, compare against MemoryModel
        # at that byte addr. Snarfing/OOO are transparent — we look up
        # by the actual address the engine asked for, not by AR order.
        rd_bad = tb.verify_axi_rd_matches_memory()
        if rd_bad is not None:
            byte_addr, mem_int, axi_int, rid = rd_bad
            tb.log.error(
                "RD PATH CORRUPTION: byte_addr=0x%X  rid=%d  "
                "Memory holds=0x%016X  AXI R returned=0x%016X  "
                "(controller corrupted DFI RD → AXI R)",
                byte_addr, rid, mem_int, axi_int,
            )
        else:
            tb.log.info("RD-path localizer OK: every AXI R beat matches "
                        "MemoryModel state (controller RD path clean)")

        # Integrity contract — clean DFI loopback should produce zero
        # protocol errors and matching CRCs.
        wr_err, _ = await _chargen(dut).errors()
        assert not wr_err, f"BRESP error latched by writers {wr_err:#04x}"
        assert not (await _chargen(dut).reader_status(0))["rresp_error"], \
            "RRESP error latched"
        # Localizer assert lives BEFORE engine's o_data_error so the
        # log lead with WHICH side broke before the generic "bad LFSR".
        assert rd_bad is None, (
            f"RD PATH CORRUPTION at byte_addr=0x{rd_bad[0]:X} rid={rd_bad[3]}: "
            f"Memory holds 0x{rd_bad[1]:016X}, "
            f"AXI R returned 0x{rd_bad[2]:016X}"
        )
        await _assert_engines_clean(dut)

        # Both CRCs must be VALID, not merely equal: two engines that never
        # ran also agree, and a comparison that passes on an empty run is
        # worse than no comparison.
        drv = _chargen(dut)
        rd_st = await drv.reader_status(0)
        wr_st = await drv.read("WR_GEN0_STATUS")
        assert wr_st & 0x2, "writer 0 never asserted crc_valid"
        assert rd_st["crc_valid"], "reader 0 never asserted crc_valid"
        await _assert_crc_match(dut)

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")


# ---------------------------------------------------------------------------
# Pytest matrix
# ---------------------------------------------------------------------------

# Every entry is an integer number of full DFI BL8 transactions (see
# BURST_LEN_MULTIPLE). Keep it that way: a shape that is not a whole DRAM burst
# makes the perf numbers meaningless (a partial burst still costs the device a
# full ACT/CAS cycle) and is rejected by BURST_LEN_MULTIPLE in the RTL.
_ALL_TYPES = ["smoke", "smoke_1x2", "smoke_2x1", "smoke_2x2",
              "kb_4burst", "kb_16burst", "kb_17burst",
              "kb_20burst", "kb_24burst", "kb1", "kb4", "kb32",
              # Eight writers + eight readers concurrently, one per bank.
              # The only entry here that exercises the generator ARRAY;
              # every other one drives generator 0.
              "bank_parallel"]
_TEST_LEVEL = os.environ.get("TEST_LEVEL", "FUNC").upper()
_PARAMS = _ALL_TYPES   # GATE == FUNC == FULL for now

# bl_8 fix landed (RTLDesignSherpa#22) — axi_intake now splits AXI
# bursts that exceed DRAM BL into chunks. Set kept empty so it can be
# re-populated if a new BL>DRAM_BL config trips.
_XFAIL_BL_GT_DRAM: set[str] = set()


def _params_with_xfail():
    out = []
    for t in _PARAMS:
        if t in _XFAIL_BL_GT_DRAM:
            out.append(pytest.param(
                t,
                marks=pytest.mark.xfail(
                    reason="AXI BL > DRAM BL: wr_beat_sequencer drives "
                           "stray wrdata beats without matching CAS-WR",
                    strict=False,
                ),
            ))
        else:
            out.append(t)
    return out


@pytest.mark.parametrize("test_type", _params_with_xfail(), ids=_PARAMS)
def test_ddr2_char_macro(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "ddr2_char_macro_tb_top"
    test_name = f"test_ddr2_char_macro_{test_type}"

    filelist_path = ("projects/NexysA7/ddr2-characterization/"
                     "ddr2_char_framework/dv/filelists/"
                     "ddr2_char_macro_tb_top.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": test_type,
        "MEM_TYPE": "DDR2",
        "SEED": os.environ.get('SEED', str(random.randint(0, 100000))),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE":
            os.path.join(log_dir, f"results_{test_name}.xml"),
    }
    parameters = {"NUM_RANKS": "1", "PAGE_POLICY": "1",
                  "RD_DBG_FIFO_DEPTH": "32"}

    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    # Inherit the controller's canonical waiver set (autogenerated CSR
    # has known MULTIDRIVEN / UNUSED warnings that are not actionable).
    compile_args = [
        "+define+USE_ASYNC_RESET",
        "-Wno-MULTIDRIVEN", "-Wno-UNUSED", "-Wno-UNDRIVEN", "-Wno-WIDTH",
        "-Wno-CASEINCOMPLETE", "-Wno-SELRANGE", "-Wno-DECLFILENAME",
        "-Wno-UNUSEDSIGNAL", "-Wno-VARHIDDEN", "-Wno-IMPLICIT",
        "-Wno-CASEOVERLAP",
    ]
    sim_args = []
    plus_args = []
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs", "--trace-depth", "99"]
        sim_args     += ["--trace", "--trace-structs", "--trace-depth", "99"]
        plus_args    += ["--trace"]
        extra_env["VERILATOR_TRACE_FST"] = "1"

    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module,
        testcase="cocotb_test_ddr2_char_macro",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, parameters=parameters,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")


# ============================================================================
# Engine-pacing sweep — NOT an AXI random-profile sweep.
#
# The AXI random-profile (BFM AXI_RANDOMIZER_CONFIGS) cross-product
# lives on the controller-only env:
#   projects/components/memory-controllers/pumice-ddr2-lpddr2/dv/tests/macro/
#     test_pumice_core_macro.py::test_pumice_core_macro_profile_sweep
#
# This sweep is the engine-integration analog: it varies the engines'
# own inter-burst pacing knobs (cfg_wr_gap, cfg_rd_gap). Tests
# engine ↔ controller timing relationships rather than BFM
# valid/ready randomization. Same 31-config matrix shape (7 uniform +
# 12 single-axis + 12 skewed) to mirror the discipline of the
# components-side profile sweep.
# ============================================================================

# cfg_wr_gap / cfg_rd_gap are 4-bit ports on the engines (range 0..15).
# Values >15 silently overflow at the SV port but raise OverflowError
# on the cocotb signal assign — that produced 12 spurious pacing_sweep
# failures in the earlier sweep. Cap at 15 = slow extreme within range.
_GAP_VALUES = (0, 1, 2, 4, 8, 15)


def _build_macro_gap_matrix() -> list[tuple[int, int]]:
    """31-entry matrix: 7 uniform + 12 axis-only + 12 skewed pairs."""
    seen: set[tuple[int, int]] = set()
    matrix: list[tuple[int, int]] = []

    def add(t: tuple[int, int]) -> None:
        if t not in seen:
            seen.add(t)
            matrix.append(t)

    # 7 uniform
    for g in _GAP_VALUES:
        add((g, g))
    # 12 single-axis variants (other axis at 0)
    for g in _GAP_VALUES:
        if g == 0:
            continue
        add((g, 0))
        add((0, g))
    # 12 skewed pairs — all values ≤15 (port width limit).
    skewed = [
        (1, 2), (2, 1), (2, 4), (4, 2), (4, 8), (8, 4),
        (8, 15), (15, 8), (4, 15), (15, 4), (1, 15), (15, 1),
    ]
    for t in skewed:
        add(t)
    return matrix


_MACRO_GAP_MATRIX = _build_macro_gap_matrix()


@pytest.mark.parametrize(
    "wr_gap,rd_gap",
    _MACRO_GAP_MATRIX,
    ids=[f"wr_{w}_rd_{r}" for (w, r) in _MACRO_GAP_MATRIX],
)
def test_ddr2_char_macro_pacing_sweep(request, wr_gap, rd_gap):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "ddr2_char_macro_tb_top"
    tag = f"wr_{wr_gap}_rd_{rd_gap}"
    test_name = f"test_ddr2_char_macro_pacing_sweep_{tag}"

    filelist_path = ("projects/NexysA7/ddr2-characterization/"
                     "ddr2_char_framework/dv/filelists/"
                     "ddr2_char_macro_tb_top.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": "pacing_sweep_b2b",
        "MEM_TYPE": "DDR2",
        "WR_GAP": str(wr_gap),
        "RD_GAP": str(rd_gap),
        "SEED": os.environ.get('SEED', str(random.randint(0, 100000))),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE":
            os.path.join(log_dir, f"results_{test_name}.xml"),
    }
    parameters = {"NUM_RANKS": "1", "PAGE_POLICY": "1",
                  "RD_DBG_FIFO_DEPTH": "32"}

    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    compile_args = [
        "+define+USE_ASYNC_RESET",
        "-Wno-MULTIDRIVEN", "-Wno-UNUSED", "-Wno-UNDRIVEN", "-Wno-WIDTH",
        "-Wno-CASEINCOMPLETE", "-Wno-SELRANGE", "-Wno-DECLFILENAME",
        "-Wno-UNUSEDSIGNAL", "-Wno-VARHIDDEN", "-Wno-IMPLICIT",
        "-Wno-CASEOVERLAP",
    ]
    sim_args: list = []
    plus_args: list = []
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs", "--trace-depth", "99"]
        sim_args     += ["--trace", "--trace-structs", "--trace-depth", "99"]
        plus_args    += ["--trace"]
        extra_env["VERILATOR_TRACE_FST"] = "1"

    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module,
        testcase="cocotb_test_ddr2_char_macro",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, parameters=parameters,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")


# ============================================================================
# Combined OOO + pacing + rd-start schmoo. 128-config matrix:
#
#   axi_id_base ∈ {0..15}                                  (16)
#   id_mode     ∈ {COUNTER=1, LFSR=2}                       (2)
#   schmoo step ∈ {fast_imm, fast_defer, slow_same, asym}   (4)
#
# Each schmoo step bundles a (wr_gap, rd_gap, rd_start_delay) tuple so
# pacing is folded into the same matrix entry — keeps test count to
# 128 without losing the spirit of the user's request to combine
# pacing + OOO + delay schmoo.
# ============================================================================

_OOO_ID_MODE_COUNTER = 1
_OOO_ID_MODE_LFSR    = 2

_OOO_SCHMOO_STEPS = [
    # (label,        wr_gap, rd_gap, rd_start_delay)
    # NOTE: cfg_wr_gap / cfg_rd_gap are 4-bit ports on the engines
    # (range 0..15). The original asym entry used rd_gap=16 which
    # raised OverflowError on the cocotb signal assign — that's what
    # produced the 32 spurious "asym" failures in the earlier OOO
    # sweep. Use 15 = legitimate slow extreme within port range.
    ("fast_imm",     0,      0,      0),
    ("fast_defer",   0,      0,      256),
    ("slow_same",    8,      8,      64),
    ("asym",         0,      15,     16),
]


def _build_ooo_matrix():
    matrix = []
    for axi_id in range(16):
        for id_mode in (_OOO_ID_MODE_COUNTER, _OOO_ID_MODE_LFSR):
            for label, wr_gap, rd_gap, rd_start_delay in _OOO_SCHMOO_STEPS:
                matrix.append(
                    (axi_id, id_mode, label, wr_gap, rd_gap, rd_start_delay)
                )
    return matrix


_OOO_MATRIX = _build_ooo_matrix()


@pytest.mark.parametrize(
    "axi_id,id_mode,schmoo_label,wr_gap,rd_gap,rd_start_delay",
    _OOO_MATRIX,
    ids=[
        f"id{a:02d}_mode{m}_{lab}"
        for (a, m, lab, _wg, _rg, _rsd) in _OOO_MATRIX
    ],
)
def test_ddr2_char_macro_ooo_pacing_schmoo(
    request, axi_id, id_mode, schmoo_label, wr_gap, rd_gap, rd_start_delay,
):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "ddr2_char_macro_tb_top"
    tag = f"id{axi_id:02d}_mode{id_mode}_{schmoo_label}"
    test_name = f"test_ddr2_char_macro_ooo_pacing_schmoo_{tag}"

    filelist_path = ("projects/NexysA7/ddr2-characterization/"
                     "ddr2_char_framework/dv/filelists/"
                     "ddr2_char_macro_tb_top.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": "ooo_pacing_schmoo",
        "MEM_TYPE": "DDR2",
        "OOO_AXI_ID":         str(axi_id),
        "OOO_ID_MODE":        str(id_mode),
        "OOO_WR_GAP":         str(wr_gap),
        "OOO_RD_GAP":         str(rd_gap),
        "OOO_RD_START_DELAY": str(rd_start_delay),
        "SEED": os.environ.get('SEED', str(random.randint(0, 100000))),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE":
            os.path.join(log_dir, f"results_{test_name}.xml"),
    }
    parameters = {"NUM_RANKS": "1", "PAGE_POLICY": "1",
                  "RD_DBG_FIFO_DEPTH": "32"}

    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    compile_args = [
        "+define+USE_ASYNC_RESET",
        "-Wno-MULTIDRIVEN", "-Wno-UNUSED", "-Wno-UNDRIVEN", "-Wno-WIDTH",
        "-Wno-CASEINCOMPLETE", "-Wno-SELRANGE", "-Wno-DECLFILENAME",
        "-Wno-UNUSEDSIGNAL", "-Wno-VARHIDDEN", "-Wno-IMPLICIT",
        "-Wno-CASEOVERLAP",
    ]
    sim_args = []
    plus_args = []
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs", "--trace-depth", "99"]
        sim_args     += ["--trace", "--trace-structs", "--trace-depth", "99"]
        plus_args    += ["--trace"]
        extra_env["VERILATOR_TRACE_FST"] = "1"

    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module,
        testcase="cocotb_test_ddr2_char_macro",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, parameters=parameters,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")


# ---------------------------------------------------------------------------
# CSR probe -- debug 101
# ---------------------------------------------------------------------------
# The full smoke test polls STATUS 10,000 times and dies 20 minutes later with
# "init_done never asserted". Waves showed WHY: init_done_o asserts in the RTL
# at 6.545us, but s_apb_PRDATA at the TB top never leaves 0 on ANY of the
# 10,000 reads. The controller is fine; the CSR READ path through
# apb4_to_peakrdl is dead.
#
# This test is the minimum instrument that shows that: bring up, one CSR
# write, read it back, read STATUS. It runs in seconds, not 20 minutes, and it
# fails on the read path instead of on a downstream symptom.


@cocotb.test(timeout_time=100, timeout_unit="us")
async def cocotb_test_ddr2_char_csr_probe(dut):
    """Program, 1 write, 1 read. Isolates the CSR path from the DRAM path."""
    tb = DDR2LPDDR2TopTB(dut, num_ranks=1, dram_bl=DRAM_BL,
                            dram_device_bytes=DRAM_DEVICE_BYTES,
                            dram_beat_width=DRAM_BEAT_BYTES * 8)
    await _drive_engine_idle(dut)
    await tb.reset(mem_type="DDR2", init_complete_delay=20)
    tb.init_register_map()
    tb.init_apb4_master()
    await tb.apb4_master.reset_bus()
    # Second APB window: the generator config block. Created here so the log
    # goes to the same place, and reset before anything is staged.
    await _chargen(dut, log=tb.log).reset()
    tb.init_dfi_slave()

    # 1. WRITE a CSR with a value distinguishable from both 0 and reset.
    #    t_rp_wait is a plain rw field with no hardware side effects, so a
    #    readback mismatch can only be the CSR path itself.
    await tb.apb_program_register("INIT_TIMING1", "t_rp_wait", 0x0B)

    # 2. READ IT BACK. This is the whole experiment: a write we just made,
    #    read through the same window, with nothing else in the way.
    rd = await tb.apb_read_register(
        int(tb.reg_map.registers["INIT_TIMING1"]["address"], 16))
    tb.log.info("CSR readback: INIT_TIMING1 = 0x%08X", rd)

    # 3. Read STATUS a handful of times while init runs (init reaches S_DONE
    #    at ~6.5us, so a few hundred cycles is ample). Log every sample -- a
    #    stuck-at-0 column IS the finding.
    seen = []
    for i in range(12):
        val = await tb.apb_read_register(0x004)
        seen.append(val)
        tb.log.info("STATUS[%2d] = 0x%08X (init_done=%d)", i, val, val & 1)
        await ClockCycles(dut.pclk, 50)

    rtl_done = int(dut.u_dut.u_ctrl.init_done_o.value)
    tb.log.info("RTL init_done_o = %d", rtl_done)

    # The write is the first thing to check: if a value we just wrote does
    # not read back, nothing downstream of the CSR means anything.
    wrote = (rd >> 8) & 0xFF
    assert wrote == 0x0B, (
        "CSR WRITE did not land: wrote t_rp_wait=0x0B to INIT_TIMING1, read "
        "back 0x%08X (t_rp_wait=0x%02X, the reset default). Reads work -- the "
        "readback returned real defaults, not zeros -- so the failure is the "
        "WRITE path through apb4_to_peakrdl, not the read path." % (rd, wrote))

    assert any(seen), (
        "CSR read path is dead: wrote t_rp_wait=0x0B, read back 0x%08X, and "
        "all %d STATUS reads returned 0 while the RTL's own init_done_o = %d. "
        "PREADY returns, so the APB handshake completes and only the read "
        "DATA is lost -- look at apb4_to_peakrdl's rd_data return across the "
        "pclk/aclk crossing, not at pumice." % (rd, len(seen), rtl_done))


def test_ddr2_char_csr_probe(request):
    """Minimal CSR read/write probe -- seconds, not the 20-minute smoke."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "ddr2_char_macro_tb_top"
    test_name = "test_ddr2_char_csr_probe"

    filelist_path = ("projects/NexysA7/ddr2-characterization/"
                     "ddr2_char_framework/dv/filelists/"
                     "ddr2_char_macro_tb_top.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "MEM_TYPE": "DDR2",
        "SEED": os.environ.get('SEED', "12345"),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE":
            os.path.join(log_dir, f"results_{test_name}.xml"),
    }
    parameters = {"NUM_RANKS": "1", "PAGE_POLICY": "1",
                  "RD_DBG_FIFO_DEPTH": "32"}

    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    compile_args = [
        "+define+USE_ASYNC_RESET",
        "-Wno-MULTIDRIVEN", "-Wno-UNUSED", "-Wno-UNDRIVEN", "-Wno-WIDTH",
        "-Wno-CASEINCOMPLETE", "-Wno-SELRANGE", "-Wno-DECLFILENAME",
        "-Wno-UNUSEDSIGNAL", "-Wno-VARHIDDEN", "-Wno-IMPLICIT",
        "-Wno-CASEOVERLAP",
    ]
    sim_args = []
    plus_args = []
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs", "--trace-depth", "99"]
        sim_args     += ["--trace", "--trace-structs", "--trace-depth", "99"]
        plus_args    += ["--trace"]
        extra_env["VERILATOR_TRACE_FST"] = "1"

    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module,
        testcase="cocotb_test_ddr2_char_csr_probe",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, parameters=parameters,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")


# ---------------------------------------------------------------------------
# 1wr / 1rd master probe -- debug 101, with waves
# ---------------------------------------------------------------------------
# The smoke test is already a 1x1 shape, but it waits 500,000 cycles for
# cfg_rd_done and so takes ~3.5 ms of sim (minutes of wall clock) to tell you
# nothing. This runs the SAME single write and single read with short timeouts
# and a live watch on the engine<->pumice AXI handshakes, so a failure names
# which master stalled instead of just timing out.
#
# It exists because the harness's own WR localizer reports "every snooped AXI
# WR beat matches MemoryModel state" even when ZERO beats were snooped -- it
# cannot tell "clean" from "nothing happened". This test can: it counts the
# handshakes directly.


async def _watch_axi(dut, counts):
    """Count AW/W/B and AR/R handshakes on the engine<->pumice AXI buses."""
    m = dut.u_dut
    while True:
        await RisingEdge(dut.mc_clk)
        await Timer(_NBA_SETTLE_PS, units="ps")
        for tag, v, r in (("aw", m.wr_awvalid, m.wr_awready),
                          ("w",  m.wr_wvalid,  m.wr_wready),
                          ("b",  m.wr_bvalid,  m.wr_bready),
                          ("ar", m.rd_arvalid, m.rd_arready),
                          ("r",  m.rd_rvalid,  m.rd_rready)):
            try:
                if int(v.value) and int(r.value):
                    counts[tag] += 1
                if int(v.value):
                    counts[tag + "_v"] += 1
            except ValueError:
                pass          # X during reset


@cocotb.test(timeout_time=100, timeout_unit="us")
async def cocotb_test_ddr2_char_1wr1rd(dut):
    """Program, then ONE write burst and ONE read burst, watching the masters."""
    import collections
    tb = DDR2LPDDR2TopTB(dut, num_ranks=1, dram_bl=DRAM_BL,
                            dram_device_bytes=DRAM_DEVICE_BYTES,
                            dram_beat_width=DRAM_BEAT_BYTES * 8)
    await _drive_engine_idle(dut)
    await tb.reset(mem_type="DDR2", init_complete_delay=20)
    tb.init_register_map()
    tb.init_apb4_master()
    await tb.apb4_master.reset_bus()
    # Second APB window: the generator config block. Created here so the log
    # goes to the same place, and reset before anything is staged.
    await _chargen(dut, log=tb.log).reset()
    tb.init_dfi_slave()
    await tb.program_defaults(dfi_rate=DFI_RATE, dram_bl=DRAM_BL)
    await tb.wait_for_init_done()

    counts = collections.Counter()
    cocotb.start_soon(_watch_axi(dut, counts))

    BASE, SEED = 0x0000_2000, 0xDEAD_BEEF

    def report(phase):
        tb.log.info(
            "%s: AW %d/%d  W %d/%d  B %d/%d  AR %d/%d  R %d/%d "
            "(handshakes/valid-cycles)", phase,
            counts["aw"], counts["aw_v"], counts["w"], counts["w_v"],
            counts["b"], counts["b_v"], counts["ar"], counts["ar_v"],
            counts["r"], counts["r_v"])

    # ---- one write burst ----
    await _program_writer(dut, start_addr=BASE, stride_0=8,
                          burst_len=BURST_LEN_MULTIPLE, txn_count=1, lfsr_seed=SEED)
    await RisingEdge(dut.mc_clk)
    await _start_writers(dut)
    try:
        await _wait_done(dut, "gen_wr_done", timeout=4000)
    except TimeoutError:
        report("WR TIMEOUT")
        raise
    report("after 1 write")

    # B is COMMIT-driven, not DRAM-landed: pumice answers B when the burst
    # commits in the write CAM, several cycles before the DFI write actually
    # clocks into the device. Peeking memory the cycle after B therefore reads
    # stale data. pumice's own _wr_rd_check drains 300 cycles for this reason.
    await ClockCycles(dut.mc_clk, 400)

    assert counts["aw"] == 1, (
        f"expected exactly 1 AW handshake, saw {counts['aw']} "
        f"(valid-cycles {counts['aw_v']}). cfg_wr_done asserted anyway, which "
        f"is why the WR localizer passed vacuously.")
    assert counts["w"] == BURST_LEN_MULTIPLE, (
        f"expected {BURST_LEN_MULTIPLE} W beats (one full DFI BL8 transaction), saw {counts['w']}")
    assert counts["b"] == 1, f"expected 1 B, saw {counts['b']}"

    mem = int.from_bytes(bytes(tb.peek_memory(BASE, 8)), "little")
    tb.log.info("memory @ 0x%04X = 0x%016X", BASE, mem)
    # Did the data land ANYWHERE? Distinguishes "controller never wrote" from
    # "model and RTL disagree about the address".
    _hits = []
    for _a in range(0, 0x8000, 8):
        if any(bytes(tb.peek_memory(_a, 8))):
            _hits.append(hex(_a))
            if len(_hits) >= 6:
                break
    tb.log.info("NONZERO memory at: %s", _hits or "NOWHERE")
    assert mem != 0, (
        f"write completed ({counts['aw']} AW, {counts['w']} W, {counts['b']} B) "
        f"but memory @ {BASE:#x} is still zero -- the beats reached pumice's "
        f"AXI port and did not reach the DRAM model.")

    # ---- one read burst ----
    await _program_reader(dut, start_addr=BASE, stride_0=8,
                          burst_len=BURST_LEN_MULTIPLE, txn_count=1, lfsr_seed=SEED)
    await RisingEdge(dut.mc_clk)
    await _start_readers(dut)
    try:
        await _wait_done(dut, "gen_rd_done", timeout=4000)
    except TimeoutError:
        report("RD TIMEOUT")
        raise
    report("after 1 read")

    assert counts["ar"] == 1, f"expected 1 AR, saw {counts['ar']}"
    assert counts["r"] >= 1, f"no R beats returned: {dict(counts)}"
    rd_st = await _chargen(dut).reader_status(0)
    assert not rd_st["data_error"], "read data mismatch"
    tb.log.info("PASS 1wr/1rd: %s", dict(counts))


def test_ddr2_char_1wr1rd(request):
    """Minimal 1-write / 1-read master probe. Run with WAVES=1 to debug."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "ddr2_char_macro_tb_top"
    test_name = "test_ddr2_char_1wr1rd"

    filelist_path = ("projects/NexysA7/ddr2-characterization/"
                     "ddr2_char_framework/dv/filelists/"
                     "ddr2_char_macro_tb_top.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name, "MEM_TYPE": "DDR2",
        "SEED": os.environ.get('SEED', "12345"),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE":
            os.path.join(log_dir, f"results_{test_name}.xml"),
    }
    parameters = {"NUM_RANKS": "1", "PAGE_POLICY": "1",
                  "RD_DBG_FIFO_DEPTH": "32"}

    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    compile_args = [
        "+define+USE_ASYNC_RESET",
        "-Wno-MULTIDRIVEN", "-Wno-UNUSED", "-Wno-UNDRIVEN", "-Wno-WIDTH",
        "-Wno-CASEINCOMPLETE", "-Wno-SELRANGE", "-Wno-DECLFILENAME",
        "-Wno-UNUSEDSIGNAL", "-Wno-VARHIDDEN", "-Wno-IMPLICIT",
        "-Wno-CASEOVERLAP",
    ]
    sim_args, plus_args = [], []
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs", "--trace-depth", "99"]
        sim_args     += ["--trace", "--trace-structs", "--trace-depth", "99"]
        plus_args    += ["--trace"]
        extra_env["VERILATOR_TRACE_FST"] = "1"

    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module,
        testcase="cocotb_test_ddr2_char_1wr1rd",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, parameters=parameters,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")
