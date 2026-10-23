#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Emit leg C3's crossbar: LiteX's AXI interconnect, converted to Verilog.

Run with the LiteX venv's python (bin/regen.sh does). The topology is the one
every leg reads -- rtl/bridges/configs/bridge_fb_data.toml and its
connectivity CSV, loaded through gen_fabric_legs.load() -- so LiteX cannot
disagree with the other legs about ports, widths, windows or reachability.

The crossbar is built exactly as litex.soc.interconnect.axi.AXICrossbar
builds it -- one AXIDecoder per master, one AXIArbiter per slave, an
AXIInterface between each pair -- with one difference: a pair exists only
where the connectivity CSV connects it. AXICrossbar itself takes no
connectivity and joins every master to every slave; the other legs all
receive the sparse matrix, so C3 does too. Each pair interface is "rw", as in
AXICrossbar (AXIArbiter cannot be built with no write or no read masters, so
a read-only slave needs it); the direction a port lacks is tied idle at that
port and synthesis removes it.

What LiteX's AXI crossbar does (and does not) do, read from its source
(litex 2026.8, soc/interconnect/axi/axi_full.py):
  - IDs pass through unchanged: no slot bits, so a slave sees the master's own
    8-bit ID. Responses are routed by the arbiter's grant, not by ID.
  - An arbiter keeps its grant until the granted master has no transaction
    outstanding at that slave and nothing is valid; only then does it
    round-robin.
  - A decoder holds a master to one slave while it has responses pending;
    a command to a different slave waits until they drain.
  - An address no slave decodes is never accepted (there is no error slave):
    the command waits forever. So is an unconnected pair.

Output (generated, tracked so the sim needs no LiteX install):
    rtl/generated/fb_litex_xbar/fb_litex_xbar.v
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.metadata
import math
import sys
from pathlib import Path

from migen import ClockDomain, Module, Signal
from litex.gen.fhdl.verilog import convert
from litex.soc.interconnect.axi import AXIInterface
from litex.soc.interconnect.axi.axi_full import AXIArbiter, AXIDecoder

sys.path.insert(0, str(Path(__file__).resolve().parent))
from gen_fabric_legs import CONFIG, OUT, Port, load  # noqa: E402

NAME = "fb_litex_xbar"
LITEX_VERSION = importlib.metadata.version("litex")
CHANNELS = {"w": ("aw", "w", "b"), "r": ("ar", "r")}
# LiteX field -> AXI signal suffix, per channel (payload and params, as in
# AXIInterface.get_ios). region is LiteX's; the benchmark port set has none.
FIELDS = {
    "aw": ("id", "addr", "len", "size", "burst", "lock", "cache", "prot", "qos", "region"),
    "ar": ("id", "addr", "len", "size", "burst", "lock", "cache", "prot", "qos", "region"),
    "w": ("data", "strb", "last"),
    "b": ("id", "resp"),
    "r": ("id", "data", "resp", "last"),
}
# Which side drives each channel's payload and valid: m = the master side.
FROM_MASTER = {"aw": True, "w": True, "b": False, "ar": True, "r": False}


def mode(p: Port) -> str:
    return {"rd": "r", "wr": "w", "rw": "rw"}[p.channels]


class FbLitexXbar(Module):
    def __init__(self, masters: list[Port], slaves: list[Port], conn: dict[str, set[str]]):
        dw, aw, idw = masters[0].data_width, masters[0].addr_width, masters[0].id_width
        # LiteX's sync logic is in the sys domain: sys_clk, and sys_rst
        # (synchronous, active high) -- the wrapper drives it from ~aresetn.
        self.clock_domains.cd_sys = ClockDomain("sys")
        self.ios: set[Signal] = {self.cd_sys.clk, self.cd_sys.rst}

        def iface(p: Port) -> AXIInterface:
            return AXIInterface(data_width=dw, address_width=aw, id_width=idw, mode=mode(p))

        def expose(p: Port, bus: AXIInterface, is_master: bool):
            """Port the interface out as <prefix><channel><field>; tie unused channels."""
            for kind, chans in CHANNELS.items():
                used = kind in mode(p)
                for ch in chans:
                    c = getattr(bus, ch)
                    inbound = FROM_MASTER[ch] == is_master   # driven from outside
                    for f in ("valid",) + FIELDS[ch]:
                        sig = getattr(c, f)
                        if not used:
                            if inbound:
                                self.comb += sig.eq(0)
                            continue
                        if f == "region":                    # not on the port set
                            if inbound:
                                self.comb += sig.eq(0)
                            continue
                        pin = Signal(len(sig), name=f"{p.prefix}{ch}{f}")
                        self.comb += (sig.eq(pin) if inbound else pin.eq(sig))
                        self.ios.add(pin)
                    rdy = Signal(name=f"{p.prefix}{ch}ready")
                    if used:
                        self.comb += (rdy.eq(c.ready) if inbound else c.ready.eq(rdy))
                        self.ios.add(rdy)
                    elif not inbound:
                        self.comb += c.ready.eq(1)

        m_bus = {m.name: iface(m) for m in masters}
        s_bus = {s.name: iface(s) for s in slaves}
        for m in masters:
            expose(m, m_bus[m.name], True)
        for s in slaves:
            expose(s, s_bus[s.name], False)

        # One AXIInterface per connected pair.
        shift = int(math.log2(dw // 8))
        pair: dict[tuple[str, str], AXIInterface] = {}
        for m in masters:
            for s in slaves:
                if s.name in conn[m.name]:
                    pair[(m.name, s.name)] = AXIInterface(
                        data_width=dw, address_width=aw, id_width=idw)

        def decoder(s: Port):
            bits = int(math.log2(s.size))
            return lambda a: (a >> (bits - shift)) == (s.base >> bits)

        for m in masters:
            row = [(decoder(s), pair[(m.name, s.name)]) for s in slaves if (m.name, s.name) in pair]
            self.submodules += AXIDecoder(m_bus[m.name], row)
        for s in slaves:
            col = [pair[(m.name, s.name)] for m in masters if (m.name, s.name) in pair]
            self.submodules += AXIArbiter(col, s_bus[s.name])


def input_digest(config: Path) -> str:
    """sha256 of everything the output depends on but LiteX itself (whose
    version gets its own header line): the topology, this script and the
    loader it imports, concatenated in this order. bin/regen.sh recomputes it
    with sha256sum to tell a current output from a stale one without LiteX."""
    h = hashlib.sha256()
    for f in digest_inputs(config):
        h.update(f.read_bytes())
    return h.hexdigest()


def digest_inputs(config: Path) -> list[Path]:
    here = Path(__file__).resolve()
    return [config, config.with_name(config.stem + "_connectivity.csv"), here,
            here.with_name("gen_fabric_legs.py")]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--config", type=Path, default=CONFIG)
    ap.add_argument("--out", type=Path, default=OUT)
    args = ap.parse_args()
    masters, slaves, conn = load(args.config)
    top = FbLitexXbar(masters, slaves, conn)
    print(f"[gen_litex_xbar] building {NAME} ({len(masters)}x{len(slaves)}, litex {LITEX_VERSION})")
    text = str(convert(top, ios=top.ios, name=NAME))
    digest = input_digest(args.config)
    # LiteX stamps the conversion time; drop it so a regen of the same inputs
    # writes the same bytes.
    text = "".join(ln for ln in text.splitlines(keepends=True) if not ln.startswith("// Date"))
    head = ("// Generated by: projects/fpga-systems/Genesys2/fabric-benchmark/bin/gen_litex_xbar.py\n"
            "// Source:       rtl/bridges/configs/bridge_fb_data.toml (+ _connectivity.csv)\n"
            f"// DO NOT EDIT -- regenerate (bin/regen.sh). LiteX {LITEX_VERSION} AXIDecoder/AXIArbiter, leg C3.\n"
            f"// litex: {LITEX_VERSION}\n"
            f"// inputs-sha256: {digest}\n")
    d = args.out / NAME
    d.mkdir(parents=True, exist_ok=True)
    (d / f"{NAME}.v").write_text(head + text)
    print(f"[gen_litex_xbar] {d / (NAME + '.v')}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
