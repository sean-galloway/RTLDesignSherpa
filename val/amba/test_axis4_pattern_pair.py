# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Test: MULTI-CHANNEL axis4_master_pattern_gen -> axis4_slave_pattern_check
#
# Streams a per-channel LFSR pattern from the generator into the checker across
# several tids and verifies PER CHANNEL: no data error, matching per-channel
# beat counts, and gen.o_expected_crc[ch] == chk.o_actual_crc[ch] for every
# active channel -- i.e. the two blocks agree under the shared dataint_crc-32
# scheme that is bit-consistent with the axi4 pattern blocks. Runs with and
# without checker backpressure. AXIS analog of test_axi4_master_pat_crc_pair.

import os

import pytest
import cocotb
from cocotb.triggers import RisingEdge
from cocotb.clock import Clock
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths

NUM_CHANNELS = 4


def _slice_ch(packed, ch, width=32):
    """Extract channel `ch`'s field from a packed [N-1:0][width-1:0] value."""
    return (int(packed) >> (ch * width)) & ((1 << width) - 1)


def _bit_ch(packed, ch):
    return (int(packed) >> ch) & 0x1


async def _reset(dut):
    dut.rst_n.value = 0
    dut.cfg_start_chk.value = 0
    dut.cfg_start_gen.value = 0
    dut.cfg_lfsr_seed.value = 0
    dut.cfg_channel_mask.value = 0
    dut.cfg_num_beats.value = 0
    dut.cfg_beats_per_pkt.value = 0
    dut.cfg_tdest.value = 0
    dut.chk_backpressure.value = 0
    for _ in range(5):
        await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    for _ in range(5):
        await RisingEdge(dut.clk)


def _active_channels(mask):
    if mask == 0:
        return list(range(NUM_CHANNELS))
    return [ch for ch in range(NUM_CHANNELS) if (mask >> ch) & 0x1]


async def _run_pair(dut, num_beats, beats_per_pkt, seed, mask, backpressure):
    active = _active_channels(mask)
    total_beats = num_beats * len(active)

    dut.cfg_lfsr_seed.value = seed
    dut.cfg_channel_mask.value = mask
    dut.cfg_num_beats.value = num_beats
    dut.cfg_beats_per_pkt.value = beats_per_pkt

    # Arm the checker first (seeds all channels), then start the generator.
    dut.cfg_start_chk.value = 1
    await RisingEdge(dut.clk)
    dut.cfg_start_chk.value = 0
    await RisingEdge(dut.clk)
    dut.cfg_start_gen.value = 1
    await RisingEdge(dut.clk)
    dut.cfg_start_gen.value = 0

    # Optional periodic backpressure while the stream runs.
    async def _bp():
        while (int(dut.gen_busy.value) == 1 or
               int(dut.chk_beat_count_total.value) < total_beats):
            dut.chk_backpressure.value = 1
            for _ in range(3):
                await RisingEdge(dut.clk)
            dut.chk_backpressure.value = 0
            for _ in range(2):
                await RisingEdge(dut.clk)

    if backpressure:
        cocotb.start_soon(_bp())

    # Wait for the generator to finish.
    for _ in range(total_beats * 20 + 500):
        await RisingEdge(dut.clk)
        if int(dut.gen_done.value) == 1:
            break
    # Let the last beats drain into the checker.
    for _ in range(200):
        await RisingEdge(dut.clk)
        if int(dut.chk_beat_count_total.value) >= total_beats:
            break
    dut.chk_backpressure.value = 0
    await RisingEdge(dut.clk)

    err        = int(dut.o_data_error.value)
    chk_total  = int(dut.chk_beat_count_total.value)
    gen_total  = int(dut.gen_beat_count_total.value)

    dut._log.info(
        f"active={active} beats/ch={num_beats} gen_total={gen_total} "
        f"chk_total={chk_total} err={err}")

    # Sticky per-beat data integrity across all channels.
    assert err == 0, "checker flagged a per-beat data mismatch"
    assert gen_total == total_beats, \
        f"gen total beats {gen_total} != {total_beats}"
    assert chk_total == total_beats, \
        f"chk total beats {chk_total} != {total_beats}"

    # Per-channel: beat counts + CRC equality (the gen<->chk contract).
    for ch in range(NUM_CHANNELS):
        exp_beats = num_beats if ch in active else 0
        g_beats = _slice_ch(dut.gen_beat_count.value, ch)
        c_beats = _slice_ch(dut.chk_beat_count.value, ch)
        assert g_beats == exp_beats, \
            f"ch{ch}: gen beat count {g_beats} != {exp_beats}"
        assert c_beats == exp_beats, \
            f"ch{ch}: chk beat count {c_beats} != {exp_beats}"

        if exp_beats == 0:
            continue

        g_valid = _bit_ch(dut.gen_expected_crc_valid.value, ch)
        c_valid = _bit_ch(dut.chk_actual_crc_valid.value, ch)
        assert g_valid == 1, f"ch{ch}: gen expected_crc_valid low"
        assert c_valid == 1, f"ch{ch}: chk actual_crc_valid low"

        g_crc = _slice_ch(dut.gen_expected_crc.value, ch)
        c_crc = _slice_ch(dut.chk_actual_crc.value, ch)
        dut._log.info(f"ch{ch}: exp_crc=0x{g_crc:08X} act_crc=0x{c_crc:08X}")
        assert g_crc == c_crc, \
            f"ch{ch}: CRC mismatch exp 0x{g_crc:08X} != act 0x{c_crc:08X}"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_pair(dut):
    """Stream N beats/channel gen->checker; verify per-channel data + CRC."""
    cocotb.start_soon(Clock(dut.clk, 10, units="ns").start())
    await _reset(dut)
    num_beats     = int(os.environ.get("NUM_BEATS", "16"))
    beats_per_pkt = int(os.environ.get("BEATS_PER_PKT", "8"))
    mask          = int(os.environ.get("CHANNEL_MASK", "0"))
    backpressure  = bool(int(os.environ.get("BACKPRESSURE", "0")))
    seed          = 0xA5A50001
    await _run_pair(dut, num_beats, beats_per_pkt, seed, mask, backpressure)


# (id, num_beats, beats_per_pkt, channel_mask, backpressure)
_PARAMS = [
    ("bp0_n16_p8_all",   16,  8, 0x0, 0),   # all 4 channels
    ("bp0_n20_p0_all",   20,  0, 0x0, 0),   # single packet per channel
    ("bp0_n12_p4_m0A",   12,  4, 0xA, 0),   # subset: channels 1 and 3
    ("bp1_n16_p8_all",   16,  8, 0x0, 1),   # all channels + backpressure
    ("bp1_n13_p5_all",   13,  5, 0x0, 1),   # ragged packet + backpressure
]


@pytest.mark.parametrize("test_type, num_beats, beats_per_pkt, channel_mask, backpressure",
                         _PARAMS, ids=[p[0] for p in _PARAMS])
def test_axis4_pattern_pair(request, test_type, num_beats, beats_per_pkt,
                            channel_mask, backpressure):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "tb_axis4_pattern_pair"
    test_name = f"test_axis4_pattern_pair_{test_type}"

    verilog_sources = [
        os.path.join(repo_root, "rtl/common/shifter_lfsr_fibonacci.sv"),
        os.path.join(repo_root, "rtl/common/dataint_crc_xor_shift.sv"),
        os.path.join(repo_root, "rtl/common/dataint_crc_xor_shift_cascade.sv"),
        os.path.join(repo_root, "rtl/common/dataint_crc.sv"),
        os.path.join(repo_root, "rtl/amba/shared/axis4_master_pattern_gen.sv"),
        os.path.join(repo_root, "rtl/amba/shared/axis4_slave_pattern_check.sv"),
        os.path.join(repo_root, tests_dir, "tb_axis4_pattern_pair.sv"),
    ]
    includes = [
        os.path.join(repo_root, "rtl/common/includes"),
        os.path.join(repo_root, "rtl/amba/includes"),
    ]

    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "NUM_BEATS": str(num_beats),
        "BEATS_PER_PKT": str(beats_per_pkt),
        "CHANNEL_MASK": str(channel_mask),
        "BACKPRESSURE": str(backpressure),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml"),
    }

    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module,
        testcase="cocotb_test_pair",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env,
        compile_args=["-Wno-fatal", "-Wno-WIDTHTRUNC", "-Wno-TIMESCALEMOD"],
        keep_files=True, timescale="1ns/1ps")
