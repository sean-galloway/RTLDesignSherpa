#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Host-side driver for the BCH loop harness (bch_loop_top / bch_loop_harness).

Wraps `UARTAxiBridge` (projects/fpga-systems/bin, the shared board+UART layer)
with by-name register access via `UartRegisterMap`, backed by the
PeakRDL-generated `bch_loop_regs_regmap.py`. No offsets live here.

Because the bridge is INJECTABLE, the identical driver drives the FPGA over
pyserial or a cocotb sim over `CocotbUartChannel`.

    from bch_loop import BchLoopDriver, EXPECTED_BUILD_ID
    d = BchLoopDriver(port="/dev/ttyUSB1")
    assert d.build_id() == EXPECTED_BUILD_ID
    r = d.run(mode=BchLoopDriver.INJ_COUNT, count=8, blocks=64)
"""
from __future__ import annotations

import os
import sys
import time
from dataclasses import dataclass, field
from typing import Optional

_REPO_ROOT = os.environ.get("REPO_ROOT")
if not _REPO_ROOT:
    raise RuntimeError("REPO_ROOT is not set. Source RTLDesignSherpa/env_python first.")

_FPGA_BIN = os.path.join(_REPO_ROOT, "projects/fpga-systems/bin")
if _FPGA_BIN not in sys.path:
    sys.path.insert(0, _FPGA_BIN)

from uart_axi_bridge import UARTAxiBridge                          # noqa: E402
from uart_link import find_port                                    # noqa: E402
from TBClasses.harness.uart_register_map import UartRegisterMap    # noqa: E402

HARNESS_BASE = 0x0
REGMAP = os.path.join(
    _REPO_ROOT, "projects/fpga-systems/Genesys2/bch/build-loop/dv/tbclasses/"
    "bch_loop_regs_regmap.py")
OBS_REGMAP = os.path.join(
    _REPO_ROOT, "projects/components/utility-ip/misc/rtl/regs/generated/"
    "obs_regs_top_regmap.py")

# The fabric's two expansion windows, each answered by an interface observer
# running the SAME obs_regs regblock: the pipeline's axi4_intf_master_observer
# on the bch_regs window (AXI4 flavour only; the AXIS flavour stubs the window
# to read-0) and the harness's axis4_intf_observer on the obs window (always
# built; on the AXI4 flavour its seams are tied off and it reads 0).
OBS_AXI4_BASE = 0x00010000
OBS_AXIS_BASE = 0x00020000
EXPECTED_BUILD_ID = 0x4243_4850   # "BCHP"

# This harness is fixed at BCH(4224,4120) t=8 over GF(2^13); the PROFILE CSR
# exposes n, t, m, spb but not k, so the host carries the one known k here.
CFG_N = 4224
CFG_K = 4120
CFG_T = 8


@dataclass
class DecoderStats:
    name: str
    blk_ok: int
    blk_corr: int
    blk_unc: int
    blk_frame: int
    sym_corr: int
    pkts: int
    crc: int
    crc_ok: bool
    data_err: bool

    @property
    def blocks(self) -> int:
        return self.blk_ok + self.blk_corr + self.blk_unc + self.blk_frame


@dataclass
class RunResult:
    blocks: int
    mode: int
    count: int
    rate: int
    bypass: bool
    cycles: int
    crc_expected: int
    a: DecoderStats
    b: DecoderStats
    inj_symbols: int
    inj_blocks: int
    inj_over_t: int
    obs: dict = field(default_factory=dict)
    iface_obs: dict = field(default_factory=dict)
    iface: str = "AXIS"
    axi4_stage: int = 0
    axi4_resp_err: bool = False
    axi4_overflow: bool = False
    decoders: int = 1
    timed_out: bool = False
    notes: list = field(default_factory=list)
    gen_seed: int = 0

    @property
    def present(self):
        return (self.a,)

    @property
    def cycles_per_block(self) -> float:
        return self.cycles / self.blocks if self.blocks else 0.0


class BchLoopDriver:
    INJ_NONE = 0
    INJ_COUNT = 1
    INJ_BURST = 2
    INJ_RATE = 3
    INJ_RANDOM = 4
    INJ_LOCALIZED = 5
    INJ_BADBLOCK = 6
    INJ_DEBUG = 7

    def __init__(self, port: Optional[str] = None, baudrate: int = 115200,
                 bridge: Optional[UARTAxiBridge] = None, timeout: float = 1.0):
        if bridge is None:
            if port is None or port == "auto":
                port = find_port()
            bridge = UARTAxiBridge(port=port, baudrate=baudrate, timeout=timeout)
        self.bridge = bridge
        self.regs = UartRegisterMap(bridge, start_address=HARNESS_BASE, regmap_file=REGMAP)
        self.obs_axi4 = UartRegisterMap(bridge, start_address=OBS_AXI4_BASE, regmap_file=OBS_REGMAP)
        self.obs_axis = UartRegisterMap(bridge, start_address=OBS_AXIS_BASE, regmap_file=OBS_REGMAP)
        self._topo = None

    def build_id(self) -> int:
        return self.regs.read("BUILD_ID")

    def scratch_roundtrip(self, values=(0xDEADBEEF, 0x00000000, 0xA5A55A5A)):
        out = []
        for v in values:
            self.regs.write_word("SCRATCH", v)
            r = self.regs.read("SCRATCH")
            out.append((v, r, v == r))
        return out

    def profile(self) -> dict:
        w = self.regs.read("PROFILE")
        return dict(n=w & 0xFFFF, t=(w >> 16) & 0xFF, m=(w >> 24) & 0xF, spb=(w >> 28) & 0xF,
                    k=CFG_K)

    def soft_reset(self) -> None:
        self.regs.write("CTRL", rmw=True, soft_reset=1)

    def clear(self) -> None:
        self.regs.write("CTRL", rmw=True, clear=1)

    def configure(self, mode: int, count: int = 0, rate: int = 0, blocks: int = 8,
                  gen_seed: int = 0, inj_seed: Optional[int] = None,
                  bypass: bool = False, throttle_a: bool = False, throttle_b: bool = False) -> None:
        self.regs.write("GEN_BLOCKS", blocks=blocks & 0xFFFF)
        self.regs.write_word("GEN_SEED", gen_seed & 0xFFFFFFFF)
        self.regs.write("INJ_CFG", mode=mode & 7,
                        errors=count & 0xFF, rate=rate & 0xFFFF)
        if inj_seed is not None:
            self.regs.write_word("INJ_SEED", inj_seed & 0xFFFFFFFF)
        self.regs.write("CTRL", rmw=True, bypass=int(bypass), throttle_a=int(throttle_a),
                        throttle_b=int(throttle_b), inj_seed_on_start=1)

    def set_inj_ranges(self, cnt_min: int, cnt_max: int, len_min: int, len_max: int) -> None:
        self.regs.write("INJ_CNT", cnt_min=cnt_min & 0xFF, cnt_max=cnt_max & 0xFF)
        self.regs.write("INJ_LEN", len_min=len_min & 0xFFFF, len_max=len_max & 0xFFFF)

    def start(self) -> None:
        self.regs.write("GO", start=1)

    def status(self) -> dict:
        w = self.regs.read("STATUS")
        names = ["busy", "gen_done", "chk_a_done", "chk_b_done", "data_err_a", "data_err_b",
                 "crc_a_ok", "crc_b_ok", "axi4_resp_err"]
        out = {n: bool(w >> i & 1) for i, n in enumerate(names)}
        out["axi4_stage"] = (w >> 11) & 0x1F
        out["axi4_overflow"] = bool(w >> 16 & 1)
        return out

    def wait_done(self, timeout_s: float = 10.0, poll_s: float = 0.0) -> bool:
        deadline = time.monotonic() + timeout_s
        while time.monotonic() < deadline:
            if not self.status()["busy"]:
                return True
            if poll_s:
                time.sleep(poll_s)
        return False

    def _decoder(self, name: str, suffix: str, st: dict) -> DecoderStats:
        r = self.regs.read
        return DecoderStats(
            name=name,
            blk_ok=r(f"BLK_OK_{suffix}"), blk_corr=r(f"BLK_CORR_{suffix}"),
            blk_unc=r(f"BLK_UNC_{suffix}"), blk_frame=r(f"BLK_FRAME_{suffix}"),
            sym_corr=r(f"SYM_CORR_{suffix}"), pkts=r(f"PKTS_{suffix}"), crc=r(f"CRC_{suffix}"),
            crc_ok=st[f"crc_{suffix.lower()}_ok"], data_err=st[f"data_err_{suffix.lower()}"])

    def topology(self) -> dict:
        if self._topo is None:
            w = self.regs.read("TOPOLOGY")
            self._topo = {
                "decoders": (w & 0x7) or 1,
                "kes_a":    bool(w >> 4 & 1),
                "iface":    "AXI4" if (w >> 12 & 1) else "AXIS",
                "name_a":   "RIBM" if not (w >> 4 & 1) else "other",
            }
        return self._topo

    def _meters(self) -> dict:
        out = {}
        for end in ("IN", "OUT", "CW_OUT", "CW_IN"):
            b = {k.lower(): self.regs.read(f"OBS_{end}_{k}")
                 for k in ("PRODUCTIVE", "BACKPRESSURE", "STARVATION", "IDLE")}
            window = sum(b.values())
            b["window"] = window
            b["utilisation"] = (b["productive"] / window) if window else 0.0
            out[end.lower()] = b
        return out

    AXIS_PORTS = ("msg_in", "cw_out", "cw_in", "msg_out")
    AXI4_PORTS = (("enc_rd", 0, 0), ("dec_rd", 1, 0), ("enc_wr", 0, 1), ("dec_wr", 1, 1))
    HIST_BINS = 16

    def _obs_stat(self, m: UartRegisterMap, *, tap: int, metric: int,
                  is_write: int = 0, channel: int = 0, bin_: int = 0,
                  hist_metric: int = 0) -> int:
        m.write("OBS_STAT_SEL", tap=tap, metric=metric, is_write=is_write,
                channel=channel, **{"bin": bin_, "hist_metric": hist_metric})
        return m.read("OBS_STAT_DATA")

    def _obs_buckets(self, m: UartRegisterMap, *, tap: int, is_write: int = 0) -> dict:
        b = {name: self._obs_stat(m, tap=tap, is_write=is_write, metric=i)
             for i, name in enumerate(("productive", "backpressure", "starvation", "idle"))}
        window = sum(b.values())
        b["window"] = window
        b["utilisation"] = (b["productive"] / window) if window else 0.0
        return b

    def observer_caps(self) -> dict:
        out = {}
        for name, m in (("axi4", self.obs_axi4), ("axis", self.obs_axis)):
            w0, w1 = m.read("OBS_CAPS0"), m.read("OBS_CAPS1")
            out[name] = {"bus_meter": bool(w0 >> 7 & 1), "mon_taps": bool(w0 >> 6 & 1),
                         "rd_ports": w1 & 0xFF, "wr_ports": (w1 >> 8) & 0xFF,
                         "channels": (w1 >> 16) & 0xFF,
                         "caps0": w0, "caps1": w1}
        return out

    def axis_observer(self) -> dict:
        out = {}
        for tap, name in enumerate(self.AXIS_PORTS):
            d = self._obs_buckets(self.obs_axis, tap=tap)
            lo = self._obs_stat(self.obs_axis, tap=tap, metric=11)
            hi = self._obs_stat(self.obs_axis, tap=tap, metric=12)
            d["bytes"] = (hi << 32) | lo
            d["beats"] = self._obs_stat(self.obs_axis, tap=tap, metric=13)
            d["packets"] = self._obs_stat(self.obs_axis, tap=tap, metric=14)
            out[name] = d
        return out

    def axi4_observer(self, hist: bool = False) -> dict:
        out = {}
        for name, tap, iw in self.AXI4_PORTS:
            d = self._obs_buckets(self.obs_axi4, tap=tap, is_write=iw)
            d["hist_total"] = self._obs_stat(self.obs_axi4, tap=tap, is_write=iw, metric=10)
            if hist:
                metrics = (0,) if iw else (0, 1)
                d["hist"] = {hm: [self._obs_stat(self.obs_axi4, tap=tap, is_write=iw,
                                                 metric=9, hist_metric=hm, bin_=b)
                                  for b in range(self.HIST_BINS)]
                             for hm in metrics}
            out[name] = d
        return out

    def iface_observer(self, hist: bool = False) -> dict:
        if self.topology()["iface"] == "AXI4":
            return {"axi4": self.axi4_observer(hist=hist)}
        return {"axis": self.axis_observer()}

    def collect(self, blocks: int, mode: int, count: int, rate: int, bypass: bool,
                gen_seed: int = 0, timed_out: bool = False, meters: bool = True,
                iface_obs: bool = False) -> RunResult:
        st = self.status()
        r = self.regs.read
        return RunResult(
            blocks=blocks, mode=mode, count=count, rate=rate, bypass=bypass,
            cycles=r("CYCLES"), crc_expected=r("CRC_EXPECTED"),
            decoders=1, iface=self.topology()["iface"],
            axi4_stage=st["axi4_stage"], axi4_resp_err=st["axi4_resp_err"],
            axi4_overflow=st["axi4_overflow"],
            a=self._decoder("RIBM", "A", st),
            b=self._decoder("unused", "B", st),
            inj_symbols=r("INJ_SYMBOLS"), inj_blocks=r("INJ_BLOCKS"), inj_over_t=r("INJ_OVER_T"),
            obs=self._meters() if meters else {},
            iface_obs=self.iface_observer() if iface_obs else {},
            timed_out=timed_out, gen_seed=gen_seed & 0xFFFFFFFF)

    def run(self, mode: int = 0, count: int = 0, rate: int = 0, blocks: int = 8,
            gen_seed: int = 0, inj_seed: Optional[int] = None, bypass: bool = False,
            meters: bool = True, iface_obs: bool = False,
            throttle_a: bool = False, throttle_b: bool = False, timeout_s: float = 10.0) -> RunResult:
        self.soft_reset()
        self.clear()
        self.configure(mode, count, rate, blocks, gen_seed, inj_seed, bypass, throttle_a, throttle_b)
        self.start()
        done = self.wait_done(timeout_s)
        return self.collect(blocks, mode, count, rate, bypass, gen_seed=gen_seed,
                            timed_out=not done, meters=meters, iface_obs=iface_obs)
