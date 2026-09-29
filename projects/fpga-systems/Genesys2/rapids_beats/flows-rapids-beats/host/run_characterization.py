#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: run_characterization
# Purpose: Host campaign for rapids_char_top on the Nexys A7-100T. Drives the
#          board over UART and runs the SAME on-chip self-check the cocotb
#          harness TB (dv/rapids_char_harness_tb.py) verifies in sim:
#            SINK  : o_gen_expected_crc[ch] == wr_crc_value[ch]
#            SOURCE: rd_crc_value[ch]        == o_chk_actual_crc[ch], data_error==0
#          Config is programmed BY NAME (RegisterMap, SRC @0x0000 / SNK @0x1000)
#          through the DUT-REG region; descriptors load through the DESC-LOAD
#          region; gen/chk/mem CSRs live in the HARNESS CSR region.
#
# Usage:
#   source env_python   # provides CocoTBFramework (RegisterMap) + PYTHONPATH
#   ./run_characterization.py --port /dev/ttyUSB1 --channels 4 --active 4 --beats 8
#
# NOTE: --channels MUST match the NUM_CHANNELS the bitstream was built with
#       (RAPIDS_NUM_CHANNELS in the Vivado build; default 4).
#
# Author: sean galloway
# Created: 2026-07-04

"""UART-driven RAPIDS beats characterization campaign (board side)."""

import argparse
import json
import logging
import os
import sys
import time
from datetime import datetime

# --- Path setup: this host dir (for local modules) + repo root (RegisterMap). --
_HOST_DIR = os.path.dirname(os.path.abspath(__file__))
if _HOST_DIR not in sys.path:
    sys.path.insert(0, _HOST_DIR)

_REPO_ROOT = os.environ.get('REPO_ROOT')
if not _REPO_ROOT:
    # flows-rapids-beats/host -> ... -> repo root (6 levels up).
    _REPO_ROOT = os.path.abspath(os.path.join(_HOST_DIR, *([os.pardir] * 6)))
    os.environ['REPO_ROOT'] = _REPO_ROOT
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)
_BIN = os.path.join(_REPO_ROOT, 'bin')
if _BIN not in sys.path:
    sys.path.insert(0, _BIN)

import rapids_char_io as rio  # noqa: E402
from rapids_char_io import RapidsCharIO  # noqa: E402
from descriptor_builder import (  # noqa: E402
    build_data_descriptor, descriptor_to_words)
from rapids_char_golden import golden_crc, LFSR_SEED_DEFAULT  # noqa: E402

RAPIDS_REGMAP_PATH = os.path.join(
    _REPO_ROOT, 'projects/components/dma-ip/rapids/rtl/rapids_regmap.py')

# Address layout — identical to rapids_char_harness_tb.py so the on-chip fetch
# address equals the host-load address.
DESC_BASE = 0x3000_0000        # descriptor RAM byte address base
SRC_DATA_BASE = 0x1000_0000    # source data (m_axi_rd) - address agnostic
DST_DATA_BASE = 0x2000_0000    # sink data dest (m_axi_wr) - address agnostic
CHANNEL_OFFSET = 0x0010_0000

# Atomic launch: the host stages every CSR + descriptor over UART, then a single
# GO write arms the meter window, starts the AXIS gen (sink), and fires all
# descriptor kicks on-chip in a few aclk cycles -- keeping UART latency OUT of
# the measured window. The kick CSRs are resolved BY NAME through
# rapids_harness_csr_regmap.py (mirroring rapids_char_harness.sv); they used to
# be hardcoded region-2 offsets here, which is what TASK-057 removed.
KICK_STRIDE      = 0x1000  # per-channel descriptor stride (matches DESC_BASE math)

# Bus-meter throughput math. One PRODUCTIVE meter cycle == one data beat
# transferred, so peak per-direction bandwidth = BYTES_PER_BEAT * ACLK_HZ and
# effective BW = peak * utilization (util = prod / (prod+bp+starv+idle)).
# BYTES_PER_BEAT is NOT a constant of this program: the bitstream reports its
# own geometry in the harness BUILD register and read_build() sets it from
# there (the Genesys 2 build moved from 512-bit / 64 B to 256-bit / 32 B beats
# on 2026-09-29, and a host that assumed 64 would have doubled every GB/s).
# The values below only hold until read_build() runs.
BYTES_PER_BEAT = 64
ACLK_HZ = 100_000_000
PEAK_BW_PER_DIR = BYTES_PER_BEAT * ACLK_HZ
DESIGN = {}   # what read_build() found; written into every results file


def read_build(io) -> dict:
    """Read the harness BUILD register (by name) and set the beat/bandwidth
    math from it. Returns the design point so callers can print/record it."""
    global BYTES_PER_BEAT, PEAK_BW_PER_DIR
    d = {
        'beat_bytes': io.csr_field("BUILD", "BEAT_BYTES"),
        'data_width': io.csr_field("BUILD", "BEAT_BYTES") * 8,
        'channels': io.csr_field("BUILD", "CHANNELS"),
        'sram_depth': 1 << io.csr_field("BUILD", "SRAM_DEPTH_LOG2"),
        'axi_monitors': bool(io.csr_field("BUILD", "AXI_MONITORS")),
        'observers': bool(io.csr_field("BUILD", "OBSERVERS")),
        'gen_mon': bool(io.csr_field("BUILD", "GEN_MON")),
        'aclk_hz': ACLK_HZ,
    }
    if d['beat_bytes'] == 0:
        raise RuntimeError("BUILD register reads 0 bytes/beat: bitstream predates the BUILD register?")
    d['sram_bytes_per_channel'] = d['sram_depth'] * d['beat_bytes']
    d['peak_bw_gb_s'] = d['beat_bytes'] * ACLK_HZ / 1e9
    BYTES_PER_BEAT = d['beat_bytes']
    PEAK_BW_PER_DIR = BYTES_PER_BEAT * ACLK_HZ
    DESIGN.clear(); DESIGN.update(d)
    return d

# APB half bases (DUT-REG region) — match the RegisterMap start_addresses.
APB_SRC_BASE = rio.APB_SRC_BASE
APB_SNK_BASE = rio.APB_SNK_BASE


class RapidsCharCampaign:
    """Runs the RAPIDS beats on-chip self-check over the UART link."""

    def __init__(self, io: RapidsCharIO, num_channels: int, verbose: bool = False):
        self.io = io
        self.num_channels = num_channels
        self.verbose = verbose
        self.log = logging.getLogger('rapids_char')
        # The bitstream's own geometry (beat size, channels, SRAM depth): every
        # byte and bandwidth figure below derives from it, in sim and on the
        # board. Read lazily -- the cocotb TB constructs this object before its
        # clock runs, so a CSR read here would hang the simulated UART.
        self.design = None

        # Two by-name register maps: SRC half @ 0x0000, SNK half @ 0x1000.
        from TBClasses.apb.register_map import RegisterMap
        self.src_regs = RegisterMap(RAPIDS_REGMAP_PATH, apb_data_width=32,
                                    apb_addr_width=13,
                                    start_address=APB_SRC_BASE, log=self.log)
        self.snk_regs = RegisterMap(RAPIDS_REGMAP_PATH, apb_data_width=32,
                                    apb_addr_width=13,
                                    start_address=APB_SNK_BASE, log=self.log)
        self._src_off = self.src_regs.get_register_offset_map()
        self._snk_off = self.snk_regs.get_register_offset_map()

    # ---- by-name register access (mirrors the cocotb TB) -------------------

    def reg_abs(self, half: str, reg_name: str) -> int:
        regs = self.src_regs if half == 'src' else self.snk_regs
        offs = self._src_off if half == 'src' else self._snk_off
        try:
            return regs.start_address + offs[reg_name]
        except KeyError:
            raise KeyError(
                f"register '{reg_name}' not in rapids_regmap.py "
                f"(offset map has {len(offs)} regs)") from None

    def write_reg(self, half: str, reg_name: str, value: int) -> None:
        addr = self.reg_abs(half, reg_name)
        self.io.dut_reg_write(addr, value)
        if self.verbose:
            self.log.info(f"APB WRITE {half.upper()}.{reg_name} "
                          f"(0x{addr:04X}) = 0x{value:08X}")

    def write_fields(self, half: str, reg_name: str, **fields: int) -> None:
        """Program a DUT register by setting its FIELDS by name (composed at their
        rapids_regmap offsets/widths) rather than a hand-assembled bitmask.
        Unspecified fields default to 0."""
        regs = self.src_regs if half == 'src' else self.snk_regs
        info = regs.registers[reg_name]
        word = 0
        for fname, val in fields.items():
            fld = info.get(fname)
            if not isinstance(fld, dict) or 'offset' not in fld:
                raise KeyError(f"unknown field {reg_name}.{fname}")
            off = fld['offset']
            hi, lo = (int(x) for x in off.split(':')) if ':' in off \
                else (int(off), int(off))
            mask = ((1 << (hi - lo + 1)) - 1) << lo
            word = (word & ~mask) | ((int(val) << lo) & mask)
        self.write_reg(half, reg_name, word)

    # ---- DUT config by name (mirrors _configure_via_apb) -------------------

    def configure_half(self, half: str) -> None:
        all_ch = (1 << self.num_channels) - 1

        self.write_fields(half, 'SCHED_TIMEOUT_CYCLES', TIMEOUT_CYCLES=1_000_000)
        self.write_fields(half, 'SCHED_TIMEOUT_LIMIT', LIMIT=0xFF)
        self.write_fields(half, 'SCHED_CONFIG', SCHED_EN=1, ERR_EN=1)  # TIMEOUT/COMPL/PERF off

        self.write_fields(half, 'DESCENG_CONFIG',
                          DESCENG_EN=1, PREFETCH_EN=1, FIFO_THRESH=4)
        self.write_fields(half, 'DESCENG_ADDR0_BASE',  ADDR0_BASE=0x0000_0000)
        self.write_fields(half, 'DESCENG_ADDR0_LIMIT', ADDR0_LIMIT=0xFFFF_FFFF)
        self.write_fields(half, 'DESCENG_ADDR1_BASE',  ADDR1_BASE=0x0000_0000)
        self.write_fields(half, 'DESCENG_ADDR1_LIMIT', ADDR1_LIMIT=0xFFFF_FFFF)

        # RD/WR_XFER_BEATS hold AxLEN (0 == 1 beat; the engines burst
        # cfg+1 beats while enough remain), ALLOC=16, DRAIN=1. The AxLEN is a
        # sweep axis (--suite-xfer, STREAM knob 1 "beats per transaction");
        # the historical default 8 = 9-beat bursts is kept as the default.
        self.write_fields(half, 'AXI_XFER_CONFIG',
                          RD_XFER_BEATS=self.xfer_axlen, WR_XFER_BEATS=self.xfer_axlen,
                          ALLOC_SIZE=16, DRAIN_SIZE=1)

        self.write_fields(half, 'CTRL_CONFIG', CTRLRD_MAX_TRY=1)
        self.write_fields(half, 'CHANNEL_ENABLE', CH_EN=all_ch)
        self.write_fields(half, 'GLOBAL_CTRL', GLOBAL_EN=1)  # avoid RST bit
        self.log.info(f"{half.upper()} half configured via APB (by name)")

    xfer_axlen = 8   # AXI_XFER_CONFIG.{RD,WR}_XFER_BEATS as programmed (AxLEN)
    resp_delay = 0   # RESP_DELAY: rd (R) and wr (B) hold, aclk cycles (STREAM knob 5)
    interleave = False   # GEN_MODE.INTERLEAVE: round-robin the active channels per beat

    def set_resp_delay(self, rd_cyc: int, wr_cyc: int = None) -> None:
        """Program the harness's axi_response_delay blocks BY NAME: rd_cyc on
        the R channel, wr_cyc (default = rd_cyc) on B. 0 = one register stage."""
        wr_cyc = rd_cyc if wr_cyc is None else wr_cyc
        self.resp_delay = int(rd_cyc)
        self.io.csr_write_reg("RESP_DELAY", RD_DELAY=int(rd_cyc) & 0xFFFF,
                              WR_DELAY=int(wr_cyc) & 0xFFFF)

    def set_interleave(self, on: bool) -> None:
        """Select the AXIS generator's channel schedule for the sink runs BY
        NAME: sequential (one channel's whole run, then the next -- only one
        sink channel ever holds data) or interleaved (round-robin per beat, so
        every active channel holds data at once; rapids TASK-018)."""
        self.interleave = bool(on)
        self.io.csr_write_reg("GEN_MODE", INTERLEAVE=int(self.interleave))

    def set_xfer_axlen(self, axlen: int) -> None:
        """Re-program the per-transaction burst length (AxLEN, 0..255) on BOTH
        halves; takes effect on the next descriptor. STREAM knob 1."""
        self.xfer_axlen = int(axlen)
        for half in ('src', 'snk'):
            self.write_fields(half, 'AXI_XFER_CONFIG',
                              RD_XFER_BEATS=self.xfer_axlen, WR_XFER_BEATS=self.xfer_axlen,
                              ALLOC_SIZE=16, DRAIN_SIZE=1)

    @staticmethod
    def _chain(first_addr: int, data_base: int, beats: int, descs: int, ch: int,
               *, is_src: bool):
        """A chain of `descs` DATA descriptors for one channel, `beats` each,
        contiguous in descriptor RAM (32 B apart) and in data memory
        (beats*64 B apart); next_ptr links them, `last` closes the chain.
        descs=1 is exactly the single descriptor the campaign always built.
        STREAM knob 3 "descriptors per channel"."""
        out = []
        for n in range(descs):
            daddr = first_addr + n * 32
            nxt = (first_addr + (n + 1) * 32) if n + 1 < descs else 0
            dst = data_base + n * beats * BYTES_PER_BEAT
            desc = (build_data_descriptor(dst, 0, beats, channel_id=ch,
                                          last=(n + 1 == descs), next_ptr=nxt)
                    if is_src else
                    build_data_descriptor(0, dst, beats, channel_id=ch,
                                          last=(n + 1 == descs), next_ptr=nxt))
            out.append((daddr, desc))
        return out

    def ensure_build(self) -> dict:
        """Read the harness BUILD register once (first hardware contact) and set
        the beat/bandwidth math from it."""
        if self.design is None:
            self.design = read_build(self.io)
        return self.design

    def configure(self) -> None:
        self.ensure_build()
        # Monitor egress window: sane constants (never 0/0, which stalls the
        # monitor path) — mirrors the cocotb TB's reset defaults.
        self.io.csr_write_reg("MON_BASE", VALUE=0x0000_1000)
        self.io.csr_write_reg("MON_LIMIT", VALUE=0x0000_5000 - 1)
        self.io.csr_write_reg("MON_FLUSHWM", VALUE=3)
        self.io.cam_clear()
        self.configure_half('src')
        self.configure_half('snk')

    # ---- atomic launch: stage kicks as config, then a single on-chip GO -----

    def _stage_kicks(self, half: str, mask: int, *, start_gen: bool) -> None:
        """Stage the on-chip kick sequencer (fired later by go()): which half,
        which channels, and the descriptor base/stride. Replaces the per-channel
        UART kick writes so the kicks land within a few aclk cycles of GO."""
        cfg = (1 if half == 'snk' else 0) | ((1 << 1) if start_gen else 0)
        self.io.csr_write_reg("KICK_CFG", HALF=cfg & 1, START_GEN_ON_GO=(cfg >> 1) & 1)
        self.io.csr_write_reg("KICK_MASK", VALUE=mask)
        self.io.csr_write_reg("KICK_BASE_LO", VALUE=DESC_BASE & 0xFFFF_FFFF)
        self.io.csr_write_reg("KICK_BASE_HI", VALUE=(DESC_BASE >> 32) & 0xFFFF_FFFF)
        self.io.csr_write_reg("KICK_STRIDE", VALUE=KICK_STRIDE)

    def go(self) -> None:
        """Single atomic GO: arm the meter window + start the AXIS gen (if
        staged) + fire every staged descriptor kick, all on-chip within a few
        aclk cycles. No UART latency enters the measured window."""
        self.io.csr_write_reg("GO", GO=1)

    def reset_channels(self) -> None:
        """Pulse CHANNEL_RESET on both halves to clear stale scheduler /
        descriptor-engine state before a run (forces the channel FSMs to
        CH_IDLE and flushes the descriptor FIFOs). The sink does NOT return to
        a clean state on its own after a transfer, so without this a second
        back-to-back run — or any active<build_width config — inherits stale
        state and wedges (sink writes 0 beats). Board-confirmed: baseline 1/4,
        with reset 5/5, and active=1/2/4/8 all pass."""
        allch = (1 << self.num_channels) - 1
        for half in ('snk', 'src'):
            self.write_fields(half, 'CHANNEL_RESET', CH_RST=allch)
            self.write_fields(half, 'CHANNEL_RESET', CH_RST=0x00)

    # ---- polling -----------------------------------------------------------

    def _poll(self, predicate, timeout_s: float, period_s: float = 0.02) -> bool:
        deadline = time.time() + timeout_s
        while time.time() < deadline:
            if predicate():
                return True
            time.sleep(period_s)
        return predicate()

    # ---- SINK self-check: AXIS gen -> sink -> m_axi_wr CRC -----------------

    def run_sink_selfcheck(self, active_channels, beats: int, timeout_s: float,
                           base_seed: int = LFSR_SEED_DEFAULT, descs: int = 1):
        """SINK path: AXIS gen -> DUT sink -> m_axi_wr write-CRC.

        PASS is anchored on the DATA-path CRC: wr_crc_value[ch] must equal the
        golden model (validates the bytes the sink actually wrote to memory).
        The generator's self-expected CRC (o_gen_expected_crc) is read as
        corroboration only; its valid flag is a known intermittent-on-re-arm
        flake, so a gen mismatch/gen-valid==0 is logged NON-FATALLY and never
        fails the run. base_seed selects the LFSR seed (the sink honors it via
        CSR_GEN_SEED); the golden reference uses the same base_seed.
        """
        self.ensure_build()
        self.log.info(f"=== SINK self-check: channels={active_channels}, "
                      f"{beats} beats/channel, base_seed=0x{base_seed:08X} ===")
        n_active = len(active_channels)
        mask = 0
        for ch in active_channels:
            mask |= (1 << ch)

        # Clear any stale scheduler/descriptor state from a prior run first.
        self.reset_channels()

        # ---- STAGE everything over UART (meter NOT armed yet) ---------------
        # 1. Load a SINK DATA descriptor chain per active channel into the SNK
        #    RAM (descs=1 is the single descriptor this always built).
        total_beats = beats * descs
        for ch in active_channels:
            for daddr, desc in self._chain(DESC_BASE + ch * 0x1000,
                                           DST_DATA_BASE + ch * CHANNEL_OFFSET,
                                           beats, descs, ch, is_src=False):
                self.io.load_descriptor('snk', daddr, descriptor_to_words(desc))

        # 2. Reset the sink-write CRC checker (1-cycle pulse in HW).
        self.io.csr_write_reg("MEM_CTRL", WR_CRC_RESET=1)

        # 3. Program the AXIS pattern generator but DO NOT start it -- GO starts
        #    it. GEN_SEED==0 selects the DEADBEEF param default; any other value
        #    is the LFSR seed verbatim. Golden uses the matching base_seed.
        seed_csr = 0 if base_seed == LFSR_SEED_DEFAULT else base_seed
        self.io.csr_write_reg("GEN_SEED", VALUE=seed_csr)
        self.io.csr_write_reg("GEN_NBEATS", VALUE=total_beats)
        self.io.csr_write_reg("GEN_BPP", VALUE=0)        # 0 => one packet per channel
        self.io.csr_write_reg("GEN_CHMASK", VALUE=mask)
        self.io.csr_write_reg("GEN_TDEST", VALUE=0)
        self.io.csr_write_reg("GEN_MODE", INTERLEAVE=int(self.interleave))

        # 4. Stage the descriptor kicks (SNK half, gen-start-on-GO) + the
        #    deterministic window-close target: the meter freezes the cycle after
        #    the wr path completes all `expected_total` writes, so the window
        #    brackets exactly the transfer regardless of when snk_system_idle
        #    (unreliable at large beat counts) asserts.
        expected_total = total_beats * n_active
        self._stage_kicks('snk', mask, start_gen=True)
        self.io.csr_write_reg("OBS_TARGET", VALUE=expected_total)

        # ---- GO: arm meter + start gen + kick all channels, on-chip ---------
        self.go()

        # 5. Wait for all beats written (deterministic; the HW meter freeze does
        #    not depend on this poll -- it just tells the host when to read).
        def done():
            return self.io.csr_read_reg("WR_BEATS_T") == expected_total

        ok_idle = self._poll(done, timeout_s)

        # 6. Golden-anchored scoreboard: wr_crc_value[ch] == golden(ch); the
        #    generator self-CRC is corroboration only (non-fatal on flake).
        return self._score(
            active_channels, total_beats, expected_total, ok_idle,
            base_seed=base_seed,
            beat_count_reg="WR_BEATS_T",
            sched_err_reg="SNK_SCHERR",
            label='SINK',
            authorities=[('wr', "WR_CRC", "WR_CRC_VLD")],
            corroborators=[('gen', "GEN_EXP_CRC", "GEN_EXP_VLD")],
            check_data_error=False)

    # ---- SOURCE self-check: m_axi_rd LFSR -> source -> m_axis chk ----------

    def run_source_selfcheck(self, active_channels, beats: int, timeout_s: float,
                             backpressure: bool = False, descs: int = 1):
        """SOURCE path: m_axi_rd LFSR gen -> DUT source -> m_axis checker.

        PASS validates BOTH data-path CRCs against golden: the read-side memory
        CRC (rd_crc_value) AND the egress checker CRC (o_chk_actual_crc) must
        each equal golden(ch). data_error must be 0.

        The source read-pattern generator has NO seed CSR (it is hardwired to
        the DEADBEEF LFSR_SEED param), so the source path always runs at the
        default seed regardless of any alternate seed swept elsewhere; the
        checker seed is pinned to match (CSR_CHK_SEED=0 => DEADBEEF).

        `backpressure` injects host-paced stalls on the m_axis egress by
        toggling chk_ready_en (the only backpressure knob the harness exposes;
        s_axis_tready = ready_en is a bare level, so there is no rate/PWM knob —
        we pulse it low/high across the poll loop). Data integrity (golden CRC)
        must still hold under the stalls.
        """
        self.ensure_build()
        self.log.info(f"=== SOURCE self-check: channels={active_channels}, "
                      f"{beats} beats/channel, "
                      f"backpressure={'ON' if backpressure else 'off'} ===")
        n_active = len(active_channels)

        mask = 0
        for ch in active_channels:
            mask |= (1 << ch)

        # Clear any stale scheduler/descriptor state from a prior run first.
        self.reset_channels()

        # ---- STAGE everything over UART (meter NOT armed yet) ---------------
        # 1. Reset the source-read LFSR/CRC pattern generator (1-cycle pulse).
        self.io.csr_write_reg("MEM_CTRL", RD_CRC_LFSR_RESET=1)

        # 2. Arm the AXIS pattern checker: chk_ready_en(level) + chk_cfg_start pulse.
        #    Source has no gen, so GO does not touch the checker -- it is armed
        #    here and stays ready. Source seed is fixed at the DEADBEEF param
        #    (no rd-gen seed CSR), so CSR_CHK_SEED=0 => DEADBEEF.
        self.io.csr_write_reg("CHK_SEED", VALUE=0)  # 0 => DEADBEEF, matches rd gen
        if backpressure:
            # Arm with ready held LOW; the poll loop pulses it to create stalls.
            self.io.csr_write_reg("CHK_CTRL", CHK_START=1, CHK_READY_EN=0)
            self.io.csr_write_reg("CHK_CTRL", CHK_START=0, CHK_READY_EN=0)
        else:
            self.io.csr_write_reg("CHK_CTRL", CHK_START=1, CHK_READY_EN=1)
            self.io.csr_write_reg("CHK_CTRL", CHK_START=0, CHK_READY_EN=1)

        # 3. Load a SOURCE DATA descriptor chain per active channel into the
        #    SRC RAM (descs=1 is the single descriptor this always built).
        total_beats = beats * descs
        for ch in active_channels:
            for daddr, desc in self._chain(DESC_BASE + ch * 0x1000,
                                           SRC_DATA_BASE + ch * CHANNEL_OFFSET,
                                           beats, descs, ch, is_src=True):
                self.io.load_descriptor('src', daddr, descriptor_to_words(desc))

        # 4. Stage the descriptor kicks (SRC half, no gen) + deterministic
        #    window-close target: freeze after the egress path checks all beats.
        expected_total = total_beats * n_active
        self._stage_kicks('src', mask, start_gen=False)
        self.io.csr_write_reg("OBS_TARGET", VALUE=expected_total)

        # ---- GO: arm meter + kick all channels, on-chip --------------------
        self.go()

        # 5. Wait for all beats checked (deterministic read trigger; the HW
        #    meter freeze is independent of this poll).
        def done():
            return self.io.csr_read_reg("CHK_BEATS_T") == expected_total

        if backpressure:
            ok_idle = self._poll_backpressure(done, timeout_s)
        else:
            ok_idle = self._poll(done, timeout_s)

        # 6. Golden-anchored scoreboard: rd_crc AND chk_actual_crc == golden.
        #    Source seed is always the DEADBEEF default (see above).
        return self._score(
            active_channels, total_beats, expected_total, ok_idle,
            base_seed=LFSR_SEED_DEFAULT,
            beat_count_reg="CHK_BEATS_T",
            sched_err_reg="SRC_SCHERR",
            label='SOURCE',
            authorities=[('rd', "RD_CRC", "RD_CRC_VLD"),
                         ('chk', "CHK_ACT_CRC", "CHK_ACT_VLD")],
            corroborators=[],
            check_data_error=True)

    def _poll_backpressure(self, predicate, timeout_s: float,
                           period_s: float = 0.02) -> bool:
        """Poll `predicate` while pulsing chk_ready_en to inject egress stalls.

        Each iteration briefly drops ready_en (stall) then re-asserts it, so the
        m_axis stream sees host-paced backpressure yet always makes forward
        progress. ready_en is guaranteed left ASSERTED so the run can drain and
        the final scoreboard sees a completed transfer.
        """
        deadline = time.time() + timeout_s
        while time.time() < deadline:
            if predicate():
                self.io.csr_write_reg("CHK_CTRL", CHK_START=0, CHK_READY_EN=1)  # leave ready asserted
                return True
            # Stall pulse (ready low), then release (ready high). start stays 0.
            self.io.csr_write_reg("CHK_CTRL", CHK_START=0, CHK_READY_EN=0)
            self.io.csr_write_reg("CHK_CTRL", CHK_START=0, CHK_READY_EN=1)
            time.sleep(period_s)
        self.io.csr_write_reg("CHK_CTRL", CHK_START=0, CHK_READY_EN=1)  # ensure ready before final check
        return predicate()

    # ---- shared per-channel scoreboard -------------------------------------

    def _score(self, active_channels, beats, expected_total, ok_idle, *,
               base_seed, beat_count_reg, sched_err_reg, label,
               authorities, corroborators, check_data_error):
        """Golden-anchored per-channel scoreboard.

        `authorities` are (name, crc_reg, vld_reg) tuples where crc_reg / vld_reg
        are harness-CSR register NAMES (resolved by-name via csr_read_reg) whose
        CRC MUST equal the golden model for the run to pass (the DATA-path CRCs).
        `corroborators` are compared against golden too but only produce
        NON-FATAL warnings on mismatch or valid==0 (e.g. the generator's
        self-CRC, whose valid flag is a known intermittent-re-arm flake).
        A golden mismatch on any authority is a genuine DUT DATA BUG.
        """
        errors = []       # fail conditions
        warnings = []     # non-fatal (corroboration / valid-flag flakes)
        results = {}

        beat_total = self.io.csr_read_reg(beat_count_reg)
        status = self.io.read_status()
        if not ok_idle:
            errors.append(f"timeout: status=0x{(status or 0):08X} "
                          f"beat_total={beat_total} (expected {expected_total})")
        if beat_total != expected_total:
            errors.append(f"beat_total={beat_total} != expected {expected_total}")
        if check_data_error and self.io.csr_field("STATUS", "DATA_ERROR"):
            errors.append("o_data_error asserted")

        auth_vld = {name: (self.io.csr_read_reg(vld) or 0)
                    for name, _, vld in authorities}
        corr_vld = {name: (self.io.csr_read_reg(vld) or 0)
                    for name, _, vld in corroborators}
        golden_mismatch = False

        for ch in active_channels:
            self.io.select_channel(ch)
            golden = golden_crc(ch, beats, base_seed)
            ch_res = {'golden': golden}
            ch_ok = True

            for name, crc_reg, _ in authorities:
                crc = self.io.csr_read_reg(crc_reg)
                ch_res[name] = crc
                if not (auth_vld[name] >> ch) & 0x1:
                    warnings.append(f"ch{ch}: {name}_crc_valid=0 (non-fatal; "
                                    f"golden comparison is authoritative)")
                if crc != golden:
                    ch_ok = False
                    golden_mismatch = True
                    errors.append(
                        f"ch{ch}: {label} GOLDEN MISMATCH (DUT DATA BUG) "
                        f"{name}=0x{(crc or 0):08X} golden=0x{golden:08X}")

            for name, crc_reg, _ in corroborators:
                crc = self.io.csr_read_reg(crc_reg)
                ch_res[name] = crc
                cv = (corr_vld[name] >> ch) & 0x1
                if crc != golden or not cv:
                    warnings.append(
                        f"ch{ch}: {name} self-CRC corroboration off "
                        f"(known {name}-valid flake, NON-FATAL) "
                        f"{name}=0x{(crc or 0):08X} valid={cv} "
                        f"golden=0x{golden:08X}")

            results[ch] = ch_res
            if ch_ok:
                auth_str = " ".join(
                    f"{n}=0x{(ch_res.get(n) or 0):08X}" for n, _, _ in authorities)
                print(f"  ch{ch}: {label} PASS golden=0x{golden:08X} "
                      f"[{auth_str}]")
            else:
                print(f"  ch{ch}: {label} FAIL golden=0x{golden:08X}")

        se = self.io.csr_read_reg(sched_err_reg)
        if se not in (0, None):
            errors.append(f"{label.lower()}_sched_error=0x{se:X}")

        # Bus meters: read BOTH interfaces on this run's direction from the frozen
        # window. A SINK run drives AXIS ingress (sin) -> AXI4 write (wr); a SOURCE
        # run drives AXI4 read (rd) -> AXIS egress (sout). Report each interface's
        # engaged utilization + effective bandwidth. Non-fatal on read hiccups.
        if label.upper() == 'SOURCE':
            ifaces = [('rd', 'AXI4-rd'), ('sout', 'AXIS-out')]   # SOURCE path
        else:
            ifaces = [('sin', 'AXIS-in'), ('wr', 'AXI4-wr')]     # SINK path
        perf = {'ifaces': {}}
        for key, disp in ifaces:
            try:
                m = self.io.read_bus_meter(key)
            except Exception as exc:  # noqa: BLE001
                self.log.warning(f"  {label}: {key} bus-meter read failed: {exc}")
                continue
            if m['engaged'] <= 0:
                continue
            eff_bw = PEAK_BW_PER_DIR * m['util']
            rec = {'iface': key, 'util': m['util'],
                   'eff_bw_gb_s': eff_bw / 1e9,
                   'peak_bw_gb_s': PEAK_BW_PER_DIR / 1e9, 'buckets': m}
            print(f"  {label} {disp}: util={m['util']:.1%} "
                  f"eff={eff_bw/1e9:.2f} GB/s (prod={m['prod']} bp={m['bp']} "
                  f"starv={m['starv']} idle={m['idle']})")
            # AXIS interfaces expose exact byte/packet counts (axis_bus_meter).
            # Byte-derived throughput over the full frozen window cross-checks the
            # cycle-utilization figure and is exact regardless of window padding.
            if key in ('sin', 'sout'):
                try:
                    ex = self.io.read_axis_extras(key)
                    win = m['total']
                    bw = (ex['bytes'] * ACLK_HZ / win) if win else 0.0
                    rec['bytes'] = ex['bytes']
                    rec['packets'] = ex['packets']
                    rec['byte_bw_gb_s'] = bw / 1e9
                    print(f"    {disp} axis: {ex['bytes']} B, {ex['packets']} pkts, "
                          f"{bw/1e9:.2f} GB/s (byte-derived)")
                except Exception as exc:  # noqa: BLE001
                    self.log.warning(f"  {label}: {key} axis extras read failed: {exc}")
            perf['ifaces'][key] = rec
        # Interface OBSERVERS (region 3, USE_OBSERVERS=1 builds): the same
        # window, measured by the shared instrument instead of the harness's bare
        # meters -- apples-to-apples with STREAM. Recorded beside the meters with
        # a cross-check, plus what the bare meters cannot give: AXI burst counts
        # and latency histograms, AXIS tap packet counts. Absent -> no key.
        if self.io.obs_present():
            perf['observers'] = {}
            for key, disp in ifaces:
                try:
                    o = self.io.read_observer(key, per_channel=self.num_channels)
                except Exception as exc:  # noqa: BLE001
                    self.log.warning(f"  {label}: {key} observer read failed: {exc}")
                    continue
                orec = {'iface': key, 'util': o['util'],
                        'eff_bw_gb_s': PEAK_BW_PER_DIR * o['util'] / 1e9,
                        'peak_bw_gb_s': PEAK_BW_PER_DIR / 1e9, 'buckets': o}
                if key in ('sin', 'sout') and o['total']:
                    orec['byte_bw_gb_s'] = o['bytes'] * ACLK_HZ / o['total'] / 1e9
                if key in ('rd', 'wr'):
                    try:
                        orec['latency'] = self.io.read_observer_latency(key)
                    except Exception as exc:  # noqa: BLE001
                        self.log.warning(f"  {label}: {key} latency read failed: {exc}")
                m = perf['ifaces'].get(key, {}).get('buckets')
                if m:
                    orec['meter_prod_delta'] = o['prod'] - m['prod']
                print(f"  {label} {disp} OBSERVER: util={o['util']:.1%} "
                      f"eff={orec['eff_bw_gb_s']:.2f} GB/s (prod={o['prod']} bp={o['bp']} "
                      f"starv={o['starv']} idle={o['idle']}"
                      + (f" bursts={o['bursts']}" if 'bursts' in o else
                         f" bytes={o['bytes']} pkts={o['packets']} tap_pkts={o['tap_packets']}")
                      + (f" dprod_vs_meter={orec['meter_prod_delta']}" if m else "") + ")")
                lat = orec.get('latency') or {}
                for mname, ld in lat.items():
                    print(f"    {disp} latency {mname}: n={ld['samples']} mean={ld['mean_cyc']:.1f} "
                          f"p50={ld['p50_cyc']} p90={ld['p90_cyc']} p99={ld['p99_cyc']} cyc")
                perf['observers'][key] = orec
            try:
                perf['observer_sticky'] = self.io.read_observer_sticky()
            except Exception as exc:  # noqa: BLE001
                self.log.warning(f"  {label}: observer sticky read failed: {exc}")
        if not perf['ifaces']:
            perf = None

        passed = len(errors) == 0
        for w in warnings:
            self.log.warning(f"  {label}: {w}")
        for e in errors:
            self.log.error(f"  SCOREBOARD: {e}")
        print(f"{label}: {'PASS' if passed else 'FAIL'} "
              f"({len(active_channels)} channels, {beats} beats each, "
              f"golden-validated){' [WARN: gen-valid flake]' if warnings and passed else ''}")
        return passed, {'errors': errors, 'warnings': warnings,
                        'results': results, 'beat_total': beat_total,
                        'golden_mismatch': golden_mismatch,
                        'perf': perf}

    # ---- suite: sweep a matrix, one row per config -------------------------

    def run_suite(self, channels_list, beats_list, bp_list, seeds_list,
                  timeout_s: float, descs_list=(1,), xfer_list=(8,), delay_list=(0,)):
        """Run the full characterization matrix and return a results list.

        Sweeps: active-channel counts x beats/channel x source-backpressure x
        base_seed. Each config runs BOTH paths (sink + source) with golden
        validation. Notes on the axes (hardware constraints, not omissions):
          * source-backpressure applies only to the SOURCE path (the SINK path
            has no host-controllable backpressure knob); it toggles chk_ready_en.
          * alternate base_seed applies only to the SINK path (the source read
            generator is hardwired to the DEADBEEF LFSR seed), so SOURCE always
            runs and validates at the default seed.
        """
        rows = []
        total = (len(channels_list) * len(beats_list) * len(descs_list)
                 * len(xfer_list) * len(delay_list) * len(bp_list) * len(seeds_list))
        idx = 0
        for delay in delay_list:
         self.set_resp_delay(delay)
         for xfer in xfer_list:
          self.set_xfer_axlen(xfer)
          for n_active in channels_list:
            active = list(range(min(n_active, self.num_channels)))
            for beats in beats_list:
              for descs in descs_list:
                for seed in seeds_list:
                    for bp in bp_list:
                        idx += 1
                        seed_lbl = ('default' if seed == LFSR_SEED_DEFAULT
                                    else f"0x{seed:08X}")
                        name = (f"ch{n_active}_b{beats}_d{descs}_x{xfer}_l{delay}_"
                                f"bp{'on' if bp else 'off'}_seed{seed_lbl}")
                        print(f"\n[{idx}/{total}] {name}")
                        sink_ok, sink_d = self.run_sink_selfcheck(
                            active, beats, timeout_s, base_seed=seed, descs=descs)
                        src_ok, src_d = self.run_source_selfcheck(
                            active, beats, timeout_s, backpressure=bp, descs=descs)
                        rows.append({
                            'name': name,
                            'active_channels': len(active),
                            'channels': active,
                            'beats': beats,                 # per descriptor
                            'descs': descs,                 # per channel (chain)
                            'total_beats': beats * descs,   # per channel
                            'xfer_axlen': xfer,
                            'xfer_beats': xfer + 1,         # burst length in beats
                            'resp_delay': delay,            # R/B hold, aclk cycles
                            'gen_interleave': self.interleave,  # sink channel schedule
                            'source_backpressure': bp,
                            'base_seed': seed,
                            'base_seed_label': seed_lbl,
                            'sink_pass': sink_ok,
                            'source_pass': src_ok,
                            'pass': sink_ok and src_ok,
                            # Backpressure is applied by toggling chk_ready_en
                            # FROM THE HOST over UART (~2.08 ms per write) while
                            # the measurement window is only hundreds of cycles
                            # wide -- it shuts before ready can be raised even
                            # once. So a bp-on SOURCE perf block measures a
                            # deliberately stalled egress, not throughput. The
                            # buckets are kept (they are true) and flagged, so a
                            # later reader does not mistake them for a
                            # measurement. RAPIDS TASK-085.
                            'perf_valid': {'sink': True, 'source': not bp},
                            'sink': _jsonable(sink_d),
                            'source': _jsonable(src_d),
                        })
        return rows


def _jsonable(detail: dict) -> dict:
    """Render a scoreboard detail dict into JSON-friendly hex-string CRCs."""
    out = {'errors': detail.get('errors', []),
           'warnings': detail.get('warnings', []),
           'beat_total': detail.get('beat_total'),
           'golden_mismatch': detail.get('golden_mismatch', False),
           'perf': detail.get('perf'),
           'per_channel': {}}
    for ch, res in (detail.get('results') or {}).items():
        out['per_channel'][str(ch)] = {
            k: (f"0x{v:08X}" if isinstance(v, int) else v)
            for k, v in res.items()}
    return out


def _print_suite_summary(rows) -> None:
    """Print the end-of-suite summary table + first-failure detail."""
    passed = [r for r in rows if r['pass']]
    failed = [r for r in rows if not r['pass']]
    print("\n" + "=" * 78)
    print(f"SUITE SUMMARY: {len(rows)} configs run, "
          f"{len(passed)} passed, {len(failed)} failed")
    print("=" * 78)
    # The direction's throughput is set by its slower (bottleneck) interface.
    def _min_util(detail):
        ifs = ((detail or {}).get('perf') or {}).get('ifaces') or {}
        return min((v['util'] for v in ifs.values()), default=None)

    def _bw(detail, valid=True):
        # valid=False => the window did not measure the transfer (see TASK-085).
        # Printing 0.00 there reads as "the link carried nothing", which is the
        # opposite of what happened: the CRC passed, the data all moved.
        if not valid:
            return "   n/m"
        u = _min_util(detail)
        return f"{PEAK_BW_PER_DIR * u / 1e9:.2f}" if u is not None else "  -"

    # Older result files have no perf_valid key; absent => treat as valid, so
    # every previously recorded JSON still reads exactly as it did before.
    def _pv(row, half):
        return (row.get('perf_valid') or {}).get(half, True)

    print(f"{'#':<4}{'config':<28}{'snk':>5}{'src':>5}{'ovr':>4}"
          f"{'snkGB/s':>9}{'srcGB/s':>9}")
    print("-" * 78)
    for i, r in enumerate(rows, 1):
        print(f"{i:<4}{r['name']:<28}"
              f"{'P' if r['sink_pass'] else 'F':>5}"
              f"{'P' if r['source_pass'] else 'F':>5}"
              f"{'P' if r['pass'] else 'F':>4}"
              f"{_bw(r.get('sink'), _pv(r, 'sink')):>9}"
              f"{_bw(r.get('source'), _pv(r, 'source')):>9}")
    if any(not _pv(r, 'source') for r in rows):
        print("  n/m = not measured: host-paced backpressure stalls the egress for"
              " the whole window (TASK-085).")
        print("        Those rows are DATA-INTEGRITY tests -- their golden CRCs"
              " passed; only the throughput is meaningless.")
    # Peak measured throughput across the suite (best bottleneck-limited window).
    def _peak(key):
        # Only rows whose window actually measured the transfer. Verified
        # 2026-09-23 to be a no-op today (max() already ignores the 0.0 that a
        # bp-on row contributes: sink 5.838 and source 6.247 either way) -- it
        # is here so the intent survives anyone changing max() to a mean.
        vals = [_min_util(r.get(key)) for r in rows if _pv(r, key)]
        vals = [PEAK_BW_PER_DIR * u / 1e9 for u in vals if u is not None]
        return max(vals) if vals else None
    snk_peak, src_peak = _peak('sink'), _peak('source')
    if snk_peak or src_peak:
        print("-" * 78)
        s = f"{snk_peak:.2f}" if snk_peak else "n/a"
        r = f"{src_peak:.2f}" if src_peak else "n/a"
        agg = (f"{snk_peak + src_peak:.2f}" if (snk_peak and src_peak) else "n/a")
        print(f"PEAK MEASURED: sink {s} GB/s + source {r} GB/s "
              f"= {agg} GB/s full-duplex (of 12.8 peak @ 100 MHz)")
    if failed:
        first = failed[0]
        print("-" * 78)
        print(f"FIRST FAILURE: {first['name']}")
        for path in ('sink', 'source'):
            errs = (first.get(path) or {}).get('errors') or []
            if errs:
                print(f"  {path.upper()} errors:")
                for e in errs:
                    print(f"    - {e}")
    # Surface any genuine golden (DUT data) mismatches distinctly.
    # A half is None when a run skipped it (--sink-only / --source-only).
    # _single_row emits that shape and claims schema parity with run_suite,
    # so the printer must honour it rather than assume a dict.
    def _gm(row, half):
        return bool((row.get(half) or {}).get('golden_mismatch'))
    sink_bugs = [r['name'] for r in rows if _gm(r, 'sink')]
    src_bugs = [r['name'] for r in rows if _gm(r, 'source')]
    if sink_bugs or src_bugs:
        print("-" * 78)
        if src_bugs:
            print(f"!! SOURCE golden mismatches (real DUT datapath bug) in: {src_bugs}")
        if sink_bugs:
            print(f"!! SINK golden mismatches in {len(sink_bugs)} config(s).")
    # Diagnostic: if SINK degrades across configs but SOURCE is clean, the cause
    # is the sink-generator RE-ARM limitation, not the RAPIDS datapath. The
    # sink AXIS generator's cfg_gen_start (CSR_GEN_CTRL[0]) is a HELD LEVEL, so
    # over UART it stays high for ~1-2 ms; the generator FSM re-runs while it is
    # high and over-produces into the DUT sink, whose per-channel SRAM alloc is
    # only cleared by aresetn (no host reset exists). The SINK path is reliable
    # only on the FIRST arm after a board reset; SOURCE re-arms cleanly because
    # its read generator has an explicit rd_crc_lfsr_reset pulse each run.
    n_sink_fail = sum(1 for r in rows if not r['sink_pass'])
    n_src_fail = sum(1 for r in rows if not r['source_pass'])
    if n_sink_fail > 1 and n_src_fail == 0:
        print("-" * 78)
        print("NOTE: SOURCE passed every config; SINK failures are the sink-")
        print("      generator re-arm limitation (cfg_gen_start held-level +")
        print("      no host reset for the AXIS generator). SINK is trustworthy")
        print("      only on the first arm after a board reset (aresetn); a")
        print("      per-config board reset would be required to sweep SINK.")
    print("=" * 78)


def _write_results(rows, path: str) -> None:
    """Write the suite results as JSON under the given path."""
    os.makedirs(os.path.dirname(path), exist_ok=True)
    payload = {
        'timestamp': datetime.now().isoformat(timespec='seconds'),
        'design': dict(DESIGN),           # geometry read back from the bitstream
        'total': len(rows),
        'passed': sum(1 for r in rows if r['pass']),
        'failed': sum(1 for r in rows if not r['pass']),
        'configs': rows,
    }
    with open(path, 'w') as fh:
        json.dump(payload, fh, indent=2)
    print(f"Results written to {path}")


def _single_row(name, active, beats, bp, seed, sink, source, interleave=False):
    """One result row for a non-suite run, in the SAME schema run_suite emits.

    Deliberately identical to the suite row: a smoke/single run is one config,
    and giving it its own shape would mean every tool that reads these files
    needs two readers. `sink`/`source` are the (ok, detail) pairs, or None when
    that half was skipped (--sink-only / --source-only).
    """
    sink_ok, sink_d = sink if sink else (None, None)
    src_ok, src_d = source if source else (None, None)
    verdicts = [v for v in (sink_ok, src_ok) if v is not None]
    return {
        'name': name,
        'active_channels': len(active),
        'channels': list(active),
        'beats': beats,
        'descs': 1, 'total_beats': beats,
        'xfer_axlen': RapidsCharCampaign.xfer_axlen,
        'xfer_beats': RapidsCharCampaign.xfer_axlen + 1,
        'resp_delay': RapidsCharCampaign.resp_delay,
        'gen_interleave': bool(interleave),
        'source_backpressure': bp,
        'base_seed': seed,
        'base_seed_label': ('default' if seed == LFSR_SEED_DEFAULT
                            else f"0x{seed:08X}"),
        'sink_pass': sink_ok,
        'source_pass': src_ok,
        'pass': all(verdicts) if verdicts else False,
        # See run_suite: a bp-on source perf block is not a measurement.
        'perf_valid': {'sink': True, 'source': not bp},
        'sink': _jsonable(sink_d) if sink_d else None,
        'source': _jsonable(src_d) if src_d else None,
    }


def _results_path(args, kind: str) -> str:
    """Timestamped path under reports/. Never reuses a name: these are measured
    records and clobbering one loses evidence."""
    from datetime import datetime as _dt
    return args.results or os.path.abspath(os.path.join(
        _RESULTS_DIR, f"rapids_char_{kind}_"
                      f"{_dt.now().strftime('%Y%m%d_%H%M%S')}.json"))


def _parse_int_list(text: str):
    return [int(x, 0) for x in text.split(',') if x.strip()]


def _parse_seed_list(text: str):
    """Parse a seed list; the token 'default' maps to the DEADBEEF param."""
    seeds = []
    for tok in text.split(','):
        tok = tok.strip()
        if not tok:
            continue
        seeds.append(LFSR_SEED_DEFAULT if tok.lower() == 'default'
                     else int(tok, 0))
    return seeds


def _parse_bp_list(text: str):
    """Parse a backpressure list of off/on tokens into booleans."""
    out = []
    for tok in text.split(','):
        tok = tok.strip().lower()
        if not tok:
            continue
        out.append(tok in ('on', '1', 'true', 'yes'))
    return out


_DEFAULT_ALT_SEED = 0xA5A5A5A5
_RESULTS_DIR = os.path.join(_HOST_DIR, os.pardir, 'reports')


def parse_args():
    p = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""\
Modes:
  (default)  single run: sink + source on --active channels, --beats each
  --smoke    fast confidence check (few channels, small beats, both paths)
  --suite    full characterization sweep (channels x beats x backpressure x seed)

Examples:
  %(prog)s --port /dev/ttyUSB2 --channels 4 --active 4 --beats 8
  %(prog)s --port /dev/ttyUSB2 --channels 4 --smoke
  %(prog)s --port /dev/ttyUSB2 --channels 4 --suite
  %(prog)s --suite --suite-channels 1,2,4 --suite-beats 1,4,8,16 \\
           --suite-bp off,on --suite-seeds default,0x12345678
""")
    p.add_argument('--port', default='auto', help="UART device. Default 'auto' probes every /dev/ttyUSB* for the harness (CSR_ID round-trip); pass an explicit path to force it.")
    p.add_argument('--baud', type=int, default=115200)
    p.add_argument('--channels', type=int, default=4,
                   help='NUM_CHANNELS the bitstream was built with')
    p.add_argument('--active', type=int, default=4,
                   help='number of active channels to exercise (single run)')
    p.add_argument('--beats', type=int, default=8,
                   help='beats per channel (single run)')
    p.add_argument('--base-seed', type=lambda s: int(s, 0),
                   default=LFSR_SEED_DEFAULT,
                   help='LFSR base seed (single run). Default 0xDEADBEEF. '
                        'Note: only the SINK path honors the seed; the SOURCE '
                        'read generator is hardwired to 0xDEADBEEF.')
    p.add_argument('--timeout', type=float, default=30.0,
                   help='per-pass completion timeout (seconds)')
    p.add_argument('--sink-only', action='store_true')
    p.add_argument('--interleave', action='store_true',
                   help='sink runs: the AXIS generator round-robins the active channels '
                        'beat by beat (GEN_MODE.INTERLEAVE), so every active channel holds '
                        'data at once. Default: one channel\'s whole run, then the next.')
    p.add_argument('--source-only', action='store_true')
    p.add_argument('--backpressure', action='store_true',
                   help='single run: inject source-egress backpressure')

    # Fast confidence check.
    p.add_argument('--smoke', action='store_true',
                   help='fast confidence check: 2 channels x 4 beats, '
                        'sink + source, golden-validated; exits non-zero on fail')

    # Full sweep.
    p.add_argument('--suite', action='store_true',
                   help='run the full characterization matrix')
    p.add_argument('--suite-channels', default='1,2,4',
                   help='active-channel counts to sweep (default 1,2,4)')
    p.add_argument('--suite-beats', default='1,4,8,16',
                   help='beats/channel to sweep (default 1,4,8,16)')
    p.add_argument('--suite-descs', default='1',
                   help="descriptors per channel (chain length), e.g. 1,2,4,8,16 "
                        "-- STREAM knob 3; default 1")
    p.add_argument('--suite-xfer', default='8',
                   help="AXI_XFER_CONFIG AxLEN values (burst = value+1 beats), "
                        "e.g. 0,1,3,7,15,31,63 -- STREAM knob 1; default 8 (9-beat bursts)")
    p.add_argument('--suite-delay', default='0',
                   help="RESP_DELAY values in aclk cycles (R and B), e.g. "
                        "0,16,32,64,96,128,192,256,384,512 -- STREAM knob 5; default 0")
    p.add_argument('--suite-bp', default='off,on',
                   help='source backpressure to sweep (default off,on)')
    p.add_argument('--suite-seeds', default=f'default,0x{_DEFAULT_ALT_SEED:08X}',
                   help='base seeds to sweep; "default" => 0xDEADBEEF '
                        f'(default: default,0x{_DEFAULT_ALT_SEED:08X})')
    p.add_argument('--results', default=None,
                   help='path for the machine-readable JSON results file '
                        '(default: <flow>/reports/rapids_char_suite_<ts>.json)')

    p.add_argument('-v', '--verbose', action='store_true')
    return p.parse_args()


def main() -> int:
    args = parse_args()
    logging.basicConfig(
        level=logging.INFO if args.verbose else logging.WARNING,
        format='%(levelname)s %(name)s: %(message)s')

    # Resolve the serial port. Default 'auto' probes every /dev/ttyUSB* for the
    # harness (CSR_ID round-trip) since the USB-UART re-enumerates.
    port = rio.autodetect_port(args.baud, want=args.port)

    with RapidsCharIO(port=port, baudrate=args.baud) as io:
        if not io.ping():
            print(f"FAIL: rapids_char_top did not respond with ID "
                  f"0x{rio.CSR_ID_EXPECTED:08X} on {port}")
            return 2
        print(f"Link OK: rapids_char_top ID = 0x{rio.CSR_ID_EXPECTED:08X}")
        campaign = RapidsCharCampaign(io, args.channels, verbose=args.verbose)
        d = campaign.ensure_build()
        print(f"Build: {d['data_width']}-bit datapath ({d['beat_bytes']} B/beat, "
              f"{d['peak_bw_gb_s']:.2f} GB/s per direction), {d['channels']} channels, "
              f"SRAM {d['sram_depth']} beats = {d['sram_bytes_per_channel'] // 1024} KB per channel, "
              f"axi_monitors={int(d['axi_monitors'])} observers={int(d['observers'])} "
              f"gen_mon={int(d['gen_mon'])}")
        if d['channels'] != args.channels:
            print(f"FAIL: --channels {args.channels} but the bitstream was built with "
                  f"{d['channels']} channels (BUILD register); pass --channels {d['channels']}")
            return 2

        campaign.configure()
        campaign.set_interleave(bool(args.interleave))

        # ---- SMOKE mode --------------------------------------------------
        if args.smoke:
            n_active = min(2, args.channels)
            active = list(range(n_active))
            beats = 4
            print(f"\n=== SMOKE: {n_active} channels x {beats} beats, "
                  f"sink + source, golden-validated ===")
            sink_ok, sink_d = campaign.run_sink_selfcheck(active, beats,
                                                     args.timeout)
            src_ok, src_d = campaign.run_source_selfcheck(active, beats,
                                                      args.timeout)
            all_pass = sink_ok and src_ok
            print("=" * 60)
            print(f"SMOKE: SINK {'PASS' if sink_ok else 'FAIL'}, "
                  f"SOURCE {'PASS' if src_ok else 'FAIL'} -> "
                  f"{'PASS' if all_pass else 'FAIL'}")
            _write_results([_single_row(
                f"smoke_ch{n_active}_b{beats}", active, beats, False,
                args.base_seed, (sink_ok, sink_d), (src_ok, src_d))],
                _results_path(args, 'smoke'))
            return 0 if all_pass else 1

        # ---- SUITE mode --------------------------------------------------
        if args.suite:
            channels_list = _parse_int_list(args.suite_channels)
            beats_list = _parse_int_list(args.suite_beats)
            bp_list = _parse_bp_list(args.suite_bp)
            seeds_list = _parse_seed_list(args.suite_seeds)
            descs_list = _parse_int_list(args.suite_descs)
            xfer_list = _parse_int_list(args.suite_xfer)
            delay_list = _parse_int_list(args.suite_delay)
            total = (len(channels_list) * len(beats_list) * len(descs_list)
                     * len(xfer_list) * len(delay_list) * len(bp_list) * len(seeds_list))
            print(f"\n=== SUITE: {total} configs "
                  f"(channels={channels_list} beats={beats_list} descs={descs_list} "
                  f"xfer_axlen={xfer_list} delay={delay_list} bp={args.suite_bp} "
                  f"seeds={args.suite_seeds}) ===")
            rows = campaign.run_suite(channels_list, beats_list, bp_list,
                                      seeds_list, args.timeout,
                                      descs_list=descs_list, xfer_list=xfer_list,
                                      delay_list=delay_list)
            _print_suite_summary(rows)
            results_path = args.results or os.path.abspath(os.path.join(
                _RESULTS_DIR,
                f"rapids_char_suite_"
                f"{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"))
            _write_results(rows, results_path)
            all_pass = all(r['pass'] for r in rows) if rows else False
            return 0 if all_pass else 1

        # ---- Default single run -----------------------------------------
        n_active = min(args.active, args.channels)
        active_channels = list(range(n_active))
        all_pass = True
        sink_res = source_res = None
        if not args.source_only:
            ok, sink_d = campaign.run_sink_selfcheck(active_channels, args.beats,
                                                args.timeout,
                                                base_seed=args.base_seed)
            all_pass = all_pass and ok
            sink_res = (ok, sink_d)
        if not args.sink_only:
            ok, src_d = campaign.run_source_selfcheck(active_channels, args.beats,
                                                  args.timeout,
                                                  backpressure=args.backpressure)
            all_pass = all_pass and ok
            source_res = (ok, src_d)

        print("=" * 60)
        print(f"OVERALL: {'PASS' if all_pass else 'FAIL'}")
        _write_results([_single_row(
            f"run_ch{n_active}_b{args.beats}_"
            f"bp{'on' if args.backpressure else 'off'}"
            f"{'_il' if args.interleave else ''}",
            active_channels, args.beats, bool(args.backpressure),
            args.base_seed, sink_res, source_res,
            interleave=campaign.interleave)],
            _results_path(args, 'run'))
        return 0 if all_pass else 1


if __name__ == '__main__':
    sys.exit(main())
