#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Host-side driver for the Reed-Solomon loop harness (rs_loop_top / rs_loop_harness).

Wraps `UARTAxiBridge` (projects/fpga-systems/bin, the shared board+UART layer)
with by-name register access via `UartRegisterMap`, backed by the
PeakRDL-generated `rs_loop_regs_regmap.py`. No offsets live here.

Because the bridge is INJECTABLE, the identical driver drives the FPGA over
pyserial or a cocotb sim over `CocotbUartChannel`.

    from rs_loop import RsLoopDriver, EXPECTED_BUILD_ID
    d = RsLoopDriver(port="/dev/ttyUSB1")
    assert d.build_id() == EXPECTED_BUILD_ID
    r = d.run(mode=RsLoopDriver.INJ_COUNT, count=8, blocks=64)
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
    _REPO_ROOT, "projects/fpga-systems/NexysA7/reed-solomon/build-loop/dv/tbclasses/"
    "rs_loop_regs_regmap.py")
EXPECTED_BUILD_ID = 0x5253_4C50   # "RSLP"


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
    cmp_data_mismatch: int
    cmp_status_mismatch: int
    cmp_beats: int
    cmp_err: bool
    cmp_misaligned: bool
    obs: dict = field(default_factory=dict)
    iface: str = "AXIS"
    axi4_stage: int = 0
    axi4_resp_err: bool = False
    axi4_overflow: bool = False
    decoders: int = 2
    compare: bool = True
    timed_out: bool = False
    notes: list = field(default_factory=list)

    @property
    def present(self):
        """Only the decoders this bitstream actually built.

        A single-decoder build ties checker B off, so its counters read zero.
        Scoring them anyway reports every run as a failure -- which is exactly
        what happened the first time the ENABLE_COMPARE = 0 build was run.
        """
        return (self.a,) if self.decoders < 2 else (self.a, self.b)

    @property
    def cycles_per_block(self) -> float:
        return self.cycles / self.blocks if self.blocks else 0.0


class RsLoopDriver:
    INJ_NONE, INJ_COUNT, INJ_BURST, INJ_RATE = 0, 1, 2, 3

    def __init__(self, port: Optional[str] = None, baudrate: int = 115200,
                 bridge: Optional[UARTAxiBridge] = None, timeout: float = 1.0):
        if bridge is None:
            if port is None or port == "auto":
                port = find_port()
            bridge = UARTAxiBridge(port=port, baudrate=baudrate, timeout=timeout)
        self.bridge = bridge
        self.regs = UartRegisterMap(bridge, start_address=HARNESS_BASE, regmap_file=REGMAP)
        self._topo = None        # TOPOLOGY is static per bitstream; read once

    # -- identity -----------------------------------------------------------
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
        return dict(n=w & 0xFFFF, t=(w >> 16) & 0xFF, m=(w >> 24) & 0xF, spb=(w >> 28) & 0xF)

    # -- control ------------------------------------------------------------
    def soft_reset(self) -> None:
        self.regs.write("CTRL", rmw=True, soft_reset=1)

    def clear(self) -> None:
        self.regs.write("CTRL", rmw=True, clear=1)

    def configure(self, mode: int, count: int = 0, rate: int = 0, blocks: int = 8,
                  gen_seed: int = 0, inj_seed: Optional[int] = None,
                  bypass: bool = False, throttle_a: bool = False, throttle_b: bool = False) -> None:
        self.regs.write("GEN_BLOCKS", blocks=blocks & 0xFFFF)
        self.regs.write_word("GEN_SEED", gen_seed & 0xFFFFFFFF)
        self.regs.write("INJ_CFG", mode=mode & 3, errors=count & 0xFF, rate=rate & 0xFFFF)
        if inj_seed is not None:
            self.regs.write_word("INJ_SEED", inj_seed & 0xFFFFFFFF)
        self.regs.write("CTRL", rmw=True, bypass=int(bypass), throttle_a=int(throttle_a),
                        throttle_b=int(throttle_b), inj_seed_on_start=1)

    def start(self) -> None:
        """The kick. One write, and no read-modify-write: configure() has
        already programmed every setup register, and GO is its own register so
        this cannot disturb one. Every consumer starts off the same cycle."""
        self.regs.write("GO", start=1)

    def status(self) -> dict:
        w = self.regs.read("STATUS")
        names = ["busy", "gen_done", "chk_a_done", "chk_b_done", "data_err_a", "data_err_b",
                 "cmp_err", "crc_a_ok", "crc_b_ok", "cmp_misaligned", "axi4_resp_err"]
        out = {n: bool(w >> i & 1) for i, n in enumerate(names)}
        # the AXI4 stage dones are a 5-bit field, not a flag: bit 0 is the
        # seed write, then encode, inject, decode, drain. 0x1F means the whole
        # chain ran. Held from one kick to the next, like every other done here.
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
        """What the bitstream built, read from TOPOLOGY rather than assumed.

        Static for a given bitstream, so it is read once and cached. The host
        has to discover this: the same harness RTL builds one decoder or two,
        with either solver in either slot, and a host that hardcoded "riBM and
        Euclid" would mislabel every result on a single-decoder build and
        score a tied-off checker as a failure.
        """
        if self._topo is None:
            # the register map reads whole REGISTERS; fields come out by
            # position, the same way status() unpacks STATUS
            w = self.regs.read("TOPOLOGY")
            self._topo = {
                "decoders": (w & 0x7) or 1,
                "kes_a":    bool(w >> 4 & 1),
                "kes_b":    bool(w >> 5 & 1),
                "compare":  bool(w >> 8 & 1),
                "iface":    "AXI4" if (w >> 12 & 1) else "AXIS",
                "name_a":   "Euclid" if (w >> 4 & 1) else "riBM",
                "name_b":   "Euclid" if (w >> 5 & 1) else "riBM",
            }
        return self._topo

    def _meters(self) -> dict:
        """The two bandwidth meters, as buckets AND as a utilisation.

        Every cycle of a valid/ready channel lands in exactly one bucket, so
        the four sum to the measured window and productive/window is the
        utilisation outright -- no separate cycle count needed, and no risk of
        dividing by a window that includes the host's own polling, because the
        hardware freezes the meters when the run ends.
        """
        out = {}
        for end in ("IN", "OUT"):
            b = {k.lower(): self.regs.read(f"OBS_{end}_{k}")
                 for k in ("PRODUCTIVE", "BACKPRESSURE", "STARVATION", "IDLE")}
            window = sum(b.values())
            b["window"] = window
            b["utilisation"] = (b["productive"] / window) if window else 0.0
            out[end.lower()] = b
        return out

    def collect(self, blocks: int, mode: int, count: int, rate: int, bypass: bool,
                timed_out: bool = False) -> RunResult:
        st = self.status()
        r = self.regs.read
        topo = self.topology()
        return RunResult(
            blocks=blocks, mode=mode, count=count, rate=rate, bypass=bypass,
            cycles=r("CYCLES"), crc_expected=r("CRC_EXPECTED"),
            decoders=topo["decoders"], compare=topo["compare"], iface=topo["iface"],
            axi4_stage=st["axi4_stage"], axi4_resp_err=st["axi4_resp_err"],
            axi4_overflow=st["axi4_overflow"],
            a=self._decoder(topo["name_a"], "A", st),
            b=self._decoder(topo["name_b"], "B", st),
            inj_symbols=r("INJ_SYMBOLS"), inj_blocks=r("INJ_BLOCKS"), inj_over_t=r("INJ_OVER_T"),
            cmp_data_mismatch=r("CMP_DATA_MISMATCH"), cmp_status_mismatch=r("CMP_STATUS_MISMATCH"),
            cmp_beats=r("CMP_BEATS"), cmp_err=st["cmp_err"],
            obs=self._meters(),
            cmp_misaligned=st["cmp_misaligned"], timed_out=timed_out)

    def run(self, mode: int = 0, count: int = 0, rate: int = 0, blocks: int = 8,
            gen_seed: int = 0, inj_seed: Optional[int] = None, bypass: bool = False,
            throttle_a: bool = False, throttle_b: bool = False, timeout_s: float = 10.0) -> RunResult:
        """One run: reset the datapath, clear the stats, configure, start, wait, collect."""
        self.soft_reset()
        self.clear()
        self.configure(mode, count, rate, blocks, gen_seed, inj_seed, bypass, throttle_a, throttle_b)
        self.start()
        done = self.wait_done(timeout_s)
        return self.collect(blocks, mode, count, rate, bypass, timed_out=not done)
