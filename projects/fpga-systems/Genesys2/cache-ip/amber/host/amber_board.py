#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Host driver for the amber pair-rig Genesys2 bring-up harness.

Talks to the board over the UART->AXIL bridge installed in amber_pair_harness.
The bridge command protocol is:

    W <addr_hex> <data_hex>\n  -> OK\n
    R <addr_hex>\n             -> 0x<data_hex>\n
Addresses are 32-bit byte offsets; data is 32-bit little-endian as emitted by
uart_axil_bridge.
"""

from __future__ import annotations

import argparse
import os
import sys
import time
from typing import Optional

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "..", "bin"))

import serial

from boards import get_board


# Bridge address map (matches bridge_amber_axil.toml / harness CSR map)
ADDR_HARNESS_CSR = 0x0001_0000
ADDR_TRAFFIC_GEN0 = 0x0002_0000
ADDR_TRAFFIC_GEN1 = 0x0003_0000
ADDR_TALLY_CNT = 0x0004_0000
ADDR_TALLY_CFGW = 0x0005_0000
ADDR_TALLY_CFGR = 0x0006_0000

# Traffic-gen CSR word offsets (32-bit)
TG_CTRL = 0x00
TG_SEED = 0x04
TG_ADDR_BASE = 0x08
TG_ADDR_MASK = 0x0C
TG_TRANS_COUNT = 0x10
TG_STATUS = 0x14
TG_ACC_COUNT = 0x18
TG_RSP_COUNT = 0x1C
TG_ERR_FLAG = 0x20
TG_RSP_CKSUM_LO = 0x30
TG_RSP_CKSUM_HI = 0x34
TG_WDATA_CKSUM_LO = 0x38
TG_WDATA_CKSUM_HI = 0x3C

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


class AmberBoard:
    """UART-connected amber pair-rig board."""

    def __init__(self, port: str, baud: int = 115200, timeout: float = 1.0) -> None:
        self.ser = serial.Serial(port, baud, timeout=timeout)
        # Drain any stale input.
        self.ser.reset_input_buffer()
        # Host-side shadow of each traffic generator's CTRL register
        # (set by config_gen) so start_gen never needs a read.
        self._ctrl_shadow: dict[int, int] = {}

    @classmethod
    def auto(cls, board_name: str = "genesys2", baud: int = 115200) -> "AmberBoard":
        """Open the board UART using the board registry."""
        board = get_board(board_name)
        ports = board.find_uart_ports()
        if not ports:
            raise RuntimeError(f"no UART port found for {board_name}")
        return cls(ports[0], baud)

    def close(self) -> None:
        self.ser.close()

    def _cmd(self, cmd: str) -> str:
        """Send a command and return the response line.

        Tolerates stray boot/programming bytes (NULs, dots) that the
        freshly-configured board emits on the UART before the bridge's
        first response: skip lines with no alphanumeric payload.
        """
        self.ser.write((cmd + "\n").encode())
        for _ in range(4):
            resp = self.ser.readline().decode(errors="replace").strip().strip("\x00").lstrip(".")
            if resp:
                break
        else:
            raise RuntimeError(f"no response to command: {cmd}")
        if resp == "ERR":
            raise RuntimeError(f"bridge ERR for command: {cmd}")
        return resp

    def write(self, addr: int, data: int) -> None:
        """Write a 32-bit word over AXIL."""
        resp = self._cmd(f"W {addr:08x} {data:08x}")
        if resp != "OK":
            raise RuntimeError(f"unexpected write response: {resp!r}")

    def read(self, addr: int) -> int:
        """Read a 32-bit word over AXIL."""
        resp = self._cmd(f"R {addr:08x}")
        if not resp.startswith("0x"):
            raise RuntimeError(f"unexpected read response: {resp!r}")
        return int(resp[2:], 16)

    def config_gen(self, base: int, seed: int, addr_base: int, addr_mask: int,
                   count: int, we_mix: int) -> None:
        """Program a traffic generator's configuration registers."""
        self.write(base + TG_SEED, seed & 0xFFFF_FFFF)
        self.write(base + TG_ADDR_BASE, addr_base & 0xFFFF_FFFF)
        self.write(base + TG_ADDR_MASK, addr_mask & 0xFFFF_FFFF)
        self.write(base + TG_TRANS_COUNT, count & 0xFFFF_FFFF)
        ctrl = ((we_mix & 0xFF) << 8) | 0x00  # run bit clear for now
        self.write(base + TG_CTRL, ctrl)
        self._ctrl_shadow[base] = ctrl

    def start_gen(self, base: int) -> None:
        """Set the run bit on a traffic generator.

        Blind-safe: uses the config_gen ctrl shadow instead of a
        read-modify-write (the board read path can hang while writes
        work, and we_mix is host-owned state anyway).
        """
        ctrl = self._ctrl_shadow.get(base)
        if ctrl is None:
            ctrl = self.read(base + TG_CTRL)
        self.write(base + TG_CTRL, ctrl | 1)

    def gen_status(self, base: int) -> dict:
        """Read a traffic generator's status counters."""
        return {
            "status": self.read(base + TG_STATUS),
            "acc_count": self.read(base + TG_ACC_COUNT),
            "rsp_count": self.read(base + TG_RSP_COUNT),
            "err_flag": self.read(base + TG_ERR_FLAG),
        }

    def gen_checksums(self, base: int) -> dict:
        """Read a traffic generator's response and issued-write-data XOR checksums."""
        return {
            "rsp_cksum": self.read64(base + TG_RSP_CKSUM_LO),
            "wdata_cksum": self.read64(base + TG_WDATA_CKSUM_LO),
        }

    def start_all(self) -> None:
        """Start both traffic generators."""
        self.start_gen(ADDR_TRAFFIC_GEN0)
        self.start_gen(ADDR_TRAFFIC_GEN1)

    def wait_done(self, timeout: float = 60.0, poll: float = 0.1) -> bool:
        """Poll harness STATUS until both generators report done."""
        deadline = time.time() + timeout
        while time.time() < deadline:
            status = self.read(ADDR_HARNESS_CSR + HCSR_STATUS)
            done0 = bool(status & 0x01)
            done1 = bool(status & 0x02)
            if done0 and done1:
                return True
            time.sleep(poll)
        return False

    def tally_clear_profile(self) -> None:
        """Clear the tally legal-set CAM."""
        self.write64(ADDR_TALLY_CFGW + TALLY_CAM_CLEAR, 0)

    def tally_load_key(self, key: int) -> None:
        """Load the current CAM key value (precedes CAM_LOAD)."""
        self.write64(ADDR_TALLY_CFGW + TALLY_CAM_KEY, key & 0xFFFF_FFFF)

    def tally_load_entry(self, index: int, key: int) -> None:
        """Load one legal-set entry: key -> dense bin index."""
        self.write64(ADDR_TALLY_CFGW + TALLY_CAM_KEY, key & 0xFFFF_FFFF)
        valid_index = (1 << 16) | (index & 0xFFFF)
        self.write64(ADDR_TALLY_CFGW + TALLY_CAM_LOAD, valid_index)

    def tally_read_count(self, bin_index: int) -> int:
        """Read a 32-bit tally bin count (8-byte stride)."""
        return self.read(ADDR_TALLY_CNT + bin_index * 8)

    def tally_read_all(self, n_bins: int) -> list[int]:
        """Sweep and return the first n_bins counts."""
        return [self.tally_read_count(i) for i in range(n_bins)]

    def write64(self, addr: int, data: int) -> None:
        """Write a 64-bit word as two 32-bit writes (low then high)."""
        self.write(addr, data & 0xFFFF_FFFF)
        self.write(addr + 4, (data >> 32) & 0xFFFF_FFFF)

    def read64(self, addr: int) -> int:
        """Read a 64-bit word as two 32-bit reads (low then high)."""
        lo = self.read(addr)
        hi = self.read(addr + 4)
        return (hi << 32) | lo


def build_default_profile() -> list[tuple[int, int]]:
    """A minimal legal-set profile for amber pair-rig smoke runs.

    Keys are {agent_id[15:0], protocol[3:0], pkt_type[3:0], event_code[7:0]}.
    These map the CORE protocol (4) events from the l1_monlite observer and
    the AXI protocol (0) events from the rd/wr monlite observers to a handful
    of dense bins. Everything else lands in the UNEXPECTED bin.
    """
    def key(agent: int, protocol: int, pkt_type: int, event: int) -> int:
        return ((agent & 0xFFFF) << 16) | ((protocol & 0xF) << 12) | \
               ((pkt_type & 0xF) << 8) | (event & 0xFF)

    # amber_top unit IDs: 0x01=l1 core, 0x02=rd monlite, 0x03=wr monlite.
    # Agent ID in the packet is 16'h00A0 combined with unit_id in the upper byte.
    def amber_agent(unit: int) -> int:
        return (unit << 8) | 0xA0

    return [
        (key(amber_agent(0x01), 4, 0, 0x00), 0),  # l1 hit
        (key(amber_agent(0x01), 4, 0, 0x01), 1),  # l1 miss
        (key(amber_agent(0x01), 4, 0, 0x02), 2),  # l1 snoop
        (key(amber_agent(0x02), 0, 0, 0x00), 3),  # rd monlite event
        (key(amber_agent(0x03), 0, 0, 0x00), 4),  # wr monlite event
    ]


def smoke(board: AmberBoard, count: int = 20000, blind: bool = False) -> None:
    """Both gens hammer the same 4KB region (forces coherence), then dump tallies.

    blind=True is write-only: for boards whose read path is still being
    debugged. The run/done evidence is LED LD7 (busy): on while the gens
    run, off when both are done.
    """
    print(f"[smoke] configuring both generators for {count} transactions each")

    board.tally_clear_profile()
    for key, idx in build_default_profile():
        board.tally_load_entry(idx, key)

    # Both gens target the same 4 KB region.
    mask = 0x0000_0FFF
    base = 0x0000_0000
    board.config_gen(ADDR_TRAFFIC_GEN0, seed=0x1234_5678,
                     addr_base=base, addr_mask=mask,
                     count=count, we_mix=64)
    board.config_gen(ADDR_TRAFFIC_GEN1, seed=0xDEAD_BEEF,
                     addr_base=base, addr_mask=mask,
                     count=count, we_mix=64)

    print("[smoke] starting generators")
    board.start_all()
    if blind:
        # No reads: give the gens wall-clock time, then report by LED.
        print("[smoke] BLIND mode (write-only): watch LED LD7 (busy) - lit while")
        print("[smoke] the gens run, OFF when both are done. Status/tally dumps")
        print("[smoke] require the read path and are skipped.")
        time.sleep(30.0)
        print("[smoke] run window elapsed - LD7 should be OFF now.")
        return
    if not board.wait_done(timeout=120.0):
        print("[smoke] ERROR: timed out waiting for done")
        return

    print("[smoke] dumping generator status")
    print("  gen0:", board.gen_status(ADDR_TRAFFIC_GEN0))
    print("  gen1:", board.gen_status(ADDR_TRAFFIC_GEN1))

    print("[smoke] dumping generator checksums")
    cksum0 = board.gen_checksums(ADDR_TRAFFIC_GEN0)
    cksum1 = board.gen_checksums(ADDR_TRAFFIC_GEN1)
    print(f"  gen0: {cksum0}")
    print(f"  gen1: {cksum1}")
    if cksum0["rsp_cksum"] == cksum1["rsp_cksum"]:
        print("[smoke] gen0/gen1 read checksums MATCH")
    else:
        print("[smoke] gen0/gen1 read checksums MISMATCH (expected; interleaving is racy)")

    print("[smoke] dumping tally bins")
    bins = board.tally_read_all(8)
    for i, c in enumerate(bins):
        print(f"  bin[{i}] = {c}")
    unexpected = board.tally_read_count(32)
    print(f"  UNEXPECTED = {unexpected}")


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.strip().splitlines()[0])
    ap.add_argument("--port", default=None, help="UART device path")
    ap.add_argument("--baud", type=int, default=115200, help="UART baud rate")
    ap.add_argument("--board", default="genesys2", help="board registry name")
    ap.add_argument("--smoke", action="store_true",
                    help="run coherence smoke test and dump tallies")
    ap.add_argument("--count", type=int, default=20000,
                    help="transactions per generator in smoke mode")
    ap.add_argument("--blind", action="store_true",
                    help="write-only smoke (no reads); watch LED LD7 for run/done")

    args = ap.parse_args(argv)

    if args.port:
        board = AmberBoard(args.port, baud=args.baud)
    else:
        board = AmberBoard.auto(args.board, baud=args.baud)

    try:
        if args.smoke:
            smoke(board, count=args.count)
        else:
            print("Use --smoke to run the board smoke test.")
    finally:
        board.close()

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
