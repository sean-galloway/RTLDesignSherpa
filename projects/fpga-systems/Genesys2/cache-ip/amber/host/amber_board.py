#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Host driver for the amber Genesys2 pair-rig bring-up harness.

This is the named-register API that both the board CLI and the cocotb cosim
import. The transport is injected (a UARTAxiBridge over pyserial in board
mode, or over a CocotbUartChannel in sim), so the SAME code drives silicon
and simulation.

Marginal-UART hardening is supplied by MarginalUartChannel, a ByteChannel
decorator that lives in this file's directory and is used only on the real
board -- the FT232R on Genesys2 drops whole transactions, and the retry/junk
logic belongs below the ASCII command interpreter, not inside the bridge
protocol.
"""

from __future__ import annotations

import argparse
import logging
import os
import sys
import time
from typing import List, Optional, Tuple

import amber_env  # noqa: F401  (path setup before shared-layer imports)

from boards import get_board
from marginal_uart_channel import MarginalUartChannel
from TBClasses.harness.device import Device, DeviceBus
from uart_axi_bridge import UARTAxiBridge
from uart_link import UartLink, find_port, scratch_probe


# Apertures exported by bridge_amber_axil (matches bridge_amber_axil.toml).
HARNESS_CSR_BASE = 0x0001_0000
CYCLE_INJECTOR0_BASE = 0x0002_0000
CYCLE_INJECTOR1_BASE = 0x0003_0000
TALLY_CNT_BASE = 0x0004_0000
TALLY_CFGW_BASE = 0x0005_0000
TALLY_CFGR_BASE = 0x0006_0000


def _here_dir() -> str:
    return os.path.dirname(os.path.abspath(__file__))


def _regmap_path(name: str) -> str:
    """Absolute path to a hand-authored regmap in this directory."""
    return os.path.join(_here_dir(), name)


HARNESS_CSR_REGMAP = _regmap_path("amber_harness_csr_regmap.py")
CYCLE_INJECTOR_REGMAP = _regmap_path("amber_cycle_injector_regmap.py")
TALLY_CNT_REGMAP = _regmap_path("amber_tally_cnt_regmap.py")
TALLY_CFGW_REGMAP = _regmap_path(
    os.path.join("..", "..", "..", "..", "..", "components",
                 "utility-ip", "misc", "rtl", "regs", "generated",
                 "tally_regs_top_regmap.py")
)


def harness_probe():
    """Return a UartLink probe that round-trips the harness CSR CTRL register.

    The amber harness has no BUILD_ID constant, but CTRL is a plain RW storage
    register, so a scratch round-trip is safe and proves the bridge is alive.
    """
    return scratch_probe(HARNESS_CSR_BASE, magic=0xC0FFEE5A)


class CycleInjector(Device):
    """One amber_cycle_injector instance, addressed entirely by name."""

    def configure(self, *, seed: int, addr_base: int, addr_mask: int,
                  count: int, we_mix: int) -> int:
        """Program configuration registers with run held low.

        Returns the CTRL word that was staged, so the caller can start the
        injector later without a read-modify-write.
        """
        # Marginal-UART hardening: run=0 goes down FIRST, then config, then
        # TRANS_COUNT twice (a dropped first write could otherwise leave 0,
        # which some injector semantics treat as "run forever").
        self.write("CTRL", run=0, we_mix=we_mix)
        self.write_word("SEED", seed)
        self.write_word("ADDR_BASE", addr_base)
        self.write_word("ADDR_MASK", addr_mask)
        self.write_word("TRANS_COUNT", count)
        self.write_word("TRANS_COUNT", count)
        self.write("CTRL", run=0, we_mix=we_mix)
        return (we_mix & 0xFF) << 8

    def start(self, ctrl_shadow: int) -> None:
        """Set the run bit using the config-time CTRL shadow."""
        self.write_word("CTRL", ctrl_shadow | 1)

    def status(self) -> dict:
        return {
            "status": self.read("STATUS"),
            "acc_count": self.read("ACC_COUNT"),
            "rsp_count": self.read("RSP_COUNT"),
            "err_flag": self.read("ERR_FLAG"),
        }

    def crcs(self) -> dict:
        lo = self.read("RSP_CRC_LO")
        hi = self.read("RSP_CRC_HI")
        rsp_crc = (hi << 32) | lo
        lo = self.read("WDATA_CRC_LO")
        hi = self.read("WDATA_CRC_HI")
        wdata_crc = (hi << 32) | lo
        return {"rsp_crc": rsp_crc, "wdata_crc": wdata_crc}


class AmberDriver:
    """Unified named-register driver for the amber pair-rig harness."""

    def __init__(self, bridge, *, log: Optional[logging.Logger] = None):
        self.bridge = bridge
        self.log = log or logging.getLogger("amber_driver")
        self.bus = self._build_bus()
        self._ctrl_shadow: dict[str, int] = {}

    def _build_bus(self) -> DeviceBus:
        bus = DeviceBus(self.bridge, log=self.log)
        bus.add("harness", base=HARNESS_CSR_BASE,
                regmap_file=HARNESS_CSR_REGMAP)
        bus.add("ci0", base=CYCLE_INJECTOR0_BASE,
                regmap_file=CYCLE_INJECTOR_REGMAP, cls=CycleInjector)
        bus.add("ci1", base=CYCLE_INJECTOR1_BASE,
                regmap_file=CYCLE_INJECTOR_REGMAP, cls=CycleInjector)
        bus.add("tally_cnt", base=TALLY_CNT_BASE,
                regmap_file=TALLY_CNT_REGMAP)
        bus.add("tally_cfgw", base=TALLY_CFGW_BASE,
                regmap_file=TALLY_CFGW_REGMAP)
        bus.add("tally_cfgr", base=TALLY_CFGR_BASE,
                regmap_file=TALLY_CFGW_REGMAP)
        return bus

    # ------------------------------------------------------------------
    # Tally
    # ------------------------------------------------------------------
    def clear_and_load_profile(self, profile: List[Tuple[int, int]]) -> None:
        cfgw = self.bus["tally_cfgw"]
        cfgw.write("CAM_CLEAR", CLEAR=1)
        for key, idx in profile:
            cfgw.write_word("CAM_KEY", key & 0xFFFF_FFFF)
            cfgw.write("CAM_LOAD", VALID=1, INDEX=idx & 0xFF)

    # ------------------------------------------------------------------
    # Cycle injectors
    # ------------------------------------------------------------------
    def configure_ci(self, name: str, *, seed: int, addr_base: int,
                     addr_mask: int, count: int, we_mix: int) -> None:
        shadow = self.bus[name].configure(
            seed=seed, addr_base=addr_base, addr_mask=addr_mask,
            count=count, we_mix=we_mix)
        self._ctrl_shadow[name] = shadow

    def start_ci(self, name: str) -> None:
        self.bus[name].start(self._ctrl_shadow[name])

    def start_all(self) -> None:
        self.start_ci("ci0")
        self.start_ci("ci1")

    def wait_done(self, timeout: float = 120.0, poll: float = 0.1,
                  sleep_fn=None) -> bool:
        """Poll harness STATUS until both injectors report done."""
        sleep_fn = sleep_fn or time.sleep
        deadline = time.time() + timeout
        harness = self.bus["harness"]
        while time.time() < deadline:
            status = harness.read("STATUS")
            if harness.field("STATUS", "ci0_done", status) and \
               harness.field("STATUS", "ci1_done", status):
                return True
            sleep_fn(poll)
        return False

    def ci_status(self, name: str) -> dict:
        return self.bus[name].status()

    def ci_crcs(self, name: str) -> dict:
        return self.bus[name].crcs()


# ----------------------------------------------------------------------
# Default legal-set profile
# ----------------------------------------------------------------------
def _key(agent: int, protocol: int, pkt_type: int, event: int) -> int:
    return ((agent & 0xFFFF) << 16) | ((protocol & 0xF) << 12) | \
           ((pkt_type & 0xF) << 8) | (event & 0xFF)


def _amber_agent(unit: int) -> int:
    return (unit << 8) | 0xA0


def build_default_profile() -> List[Tuple[int, int]]:
    """Minimal legal-set profile for amber pair-rig smoke runs.

    Keys are {agent_id[15:0], protocol[3:0], pkt_type[3:0], event_code[7:0]}.
    """
    return [
        (_key(_amber_agent(0x01), 4, 0, 0x00), 0),  # l1 hit
        (_key(_amber_agent(0x01), 4, 0, 0x01), 1),  # l1 miss
        (_key(_amber_agent(0x01), 4, 0, 0x02), 2),  # l1 snoop
        (_key(_amber_agent(0x02), 0, 0, 0x00), 3),  # rd monlite event
        (_key(_amber_agent(0x03), 0, 0, 0x00), 4),  # wr monlite event
    ]


# ----------------------------------------------------------------------
# Smoke campaign (used by both board CLI and cocotb cosim)
# ----------------------------------------------------------------------
def smoke(driver: AmberDriver, *, count: int = 20000, blind: bool = False,
          sleep_fn=None, say=print) -> dict:
    """Both injectors hammer the same 4KB region, then dump tallies.

    blind=True is write-only: for boards whose read path is still being
    debugged. The run/done evidence is LED LD7 (busy).
    """
    sleep_fn = sleep_fn or time.sleep

    say(f"[smoke] configuring both cycle injectors for {count} "
        f"transactions each")

    driver.clear_and_load_profile(build_default_profile())

    mask = 0x0000_0FFF
    base = 0x0000_0000
    driver.configure_ci("ci0", seed=0x1234_5678, addr_base=base,
                        addr_mask=mask, count=count, we_mix=64)
    driver.configure_ci("ci1", seed=0xDEAD_BEEF, addr_base=base,
                        addr_mask=mask, count=count, we_mix=64)

    say("[smoke] starting cycle injectors")
    driver.start_all()

    if blind:
        # Sim-friendly: if no real wall-clock sleep is available, just return
        # after starting; the caller is responsible for not using blind mode
        # in a cosim that cannot wall-clock sleep.
        if sleep_fn is not None:
            say("[smoke] BLIND mode (write-only): watch LED LD7 (busy) - "
                "lit while the injectors run, OFF when both are done. "
                "Status/tally dumps require the read path and are skipped.")
            sleep_fn(30.0)
            say("[smoke] run window elapsed - LD7 should be OFF now.")
        else:
            say("[smoke] BLIND mode requested but no sleep function; "
                "skipping wall-clock wait.")
        return {"blind": True}

    if not driver.wait_done(timeout=120.0, sleep_fn=sleep_fn):
        say("[smoke] ERROR: timed out waiting for done")
        return {"ok": False, "reason": "timeout"}

    say("[smoke] dumping cycle injector status")
    say(f"  ci0: {driver.ci_status('ci0')}")
    say(f"  ci1: {driver.ci_status('ci1')}")

    say("[smoke] dumping cycle injector CRCs")
    crc0 = driver.ci_crcs("ci0")
    crc1 = driver.ci_crcs("ci1")
    say(f"  ci0: {crc0}")
    say(f"  ci1: {crc1}")
    if crc0["rsp_crc"] == crc1["rsp_crc"]:
        say("[smoke] ci0/ci1 read CRCs MATCH")
    else:
        say("[smoke] ci0/ci1 read CRCs MISMATCH "
            "(expected; interleaving is racy)")

    say("[smoke] dumping tally bins")
    tally = driver.bus["tally_cnt"]
    bins = [tally.read(f"COUNT{i}") for i in range(8)]
    for i, c in enumerate(bins):
        say(f"  bin[{i}] = {c}")
    unexpected = tally.read("UNEXPECTED")
    say(f"  UNEXPECTED = {unexpected}")

    return {
        "ok": True,
        "crc0": crc0,
        "crc1": crc1,
        "bins": bins,
        "unexpected": unexpected,
    }


# ----------------------------------------------------------------------
# Board transport construction
# ----------------------------------------------------------------------
def open_amber_link(port: Optional[str] = None, *, board_name: str = "genesys2",
                    baudrate: int = 115200, timeout: float = 1.0) -> UartLink:
    """Open a UartLink to the amber harness, with optional port discovery."""
    board = get_board(board_name)
    if port and port != "auto":
        return UartLink(port, baudrate=baudrate, timeout=timeout)
    port = board.find_uart_port(probe=harness_probe(), want=port,
                                baudrate=baudrate, timeout=0.4,
                                label="amber Genesys2 harness")
    return UartLink(port, baudrate=baudrate, timeout=timeout)


def build_amber_bridge(link: UartLink) -> UARTAxiBridge:
    """Wrap a UartLink with the marginal-UART decorator and build the bridge."""
    channel = MarginalUartChannel(link, log=logging.getLogger("amber_bridge"))
    return UARTAxiBridge(channel=channel)


# ----------------------------------------------------------------------
# CLI
# ----------------------------------------------------------------------
def main(argv=None) -> int:
    ap = argparse.ArgumentParser(
        description="Host driver for the amber Genesys2 pair-rig harness")
    ap.add_argument("--port", default=None,
                    help="UART device path; omit to auto-detect")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--board", default="genesys2")
    ap.add_argument("--smoke", action="store_true",
                    help="run coherence smoke test and dump tallies")
    ap.add_argument("--count", type=int, default=20000)
    ap.add_argument("--blind", action="store_true",
                    help="write-only smoke (no reads); watch LED LD7")

    args = ap.parse_args(argv)

    link = open_amber_link(args.port, board_name=args.board,
                           baudrate=args.baud)
    bridge = build_amber_bridge(link)
    driver = AmberDriver(bridge)

    try:
        if args.smoke:
            result = smoke(driver, count=args.count, blind=args.blind,
                           sleep_fn=time.sleep)
            return 0 if result.get("ok") or result.get("blind") else 1
        else:
            print("Use --smoke to run the board smoke test.")
    finally:
        bridge.close()

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
