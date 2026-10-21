#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Emit every leg's `fb_data_fabric` from ONE port set (PRD.md section 4).

The data fabric under test is the only block that changes between legs, so the
harness instantiates a module called `fb_data_fabric` and each leg's filelist
decides which file defines it:

    leg A   bridge   wraps the bridge generator's `bridge_fb_data`
    leg B1  xbar     wraps Xilinx `axi_crossbar_v2_1_37_axi_crossbar`
    leg B2  sc       wraps `fb_sc_wrapper`, the IP-integrator block design
                     around Xilinx SmartConnect (fpga/tcl/vendor_ip.tcl)

Both wrappers are generated here from the same inputs the bridge generator
reads -- `rtl/bridges/configs/bridge_fb_data.toml` and its connectivity CSV --
so the legs cannot disagree about ports, widths, windows, IDs or which master
reaches which slave. A topology change is one TOML edit and a regen.

Matching rule (PRD.md section 2): the vendor fabric is configured to the
bridge's measured limits, never deeper:
    per-master acceptance  16   (bridge master adapter AR/AW_TRK_DEPTH)
    per-slave issuing      16   (bridge slave adapter bridge_cam DEPTH)
    no register slices          (bridge built with xbar_pipeline = false)
    round-robin, no priority    (bridge arbitration = "rr")

The wrapper port set carries no USER and no REGION: neither leg's slaves use
region. Slave-side IDs are SID bits in every leg, slot = TOML master order:
{master slot, master id} in leg B1; {master slot, remap slot} zero-extended
in leg A, whose bridge remaps IDs wider than a slot (bridge TASK-018) -- the
wrapper sizes those ports from bridge_fb_data_pkg::XBAR_ID_WIDTH.

SmartConnect carries no ID to its slaves: the ID width at every MI port is
read-only and 0 (it orders responses itself and expects in-order slaves). So
leg B2's slave-side ID is 0, and nothing downstream may depend on it: the
LFSR source and CRC sink take the channel from the address in every leg
(fb_endpoints CH_SEL_ADDR=1), and SmartConnect is configured with no AxUSER,
so it carries nothing the other two legs do not. Responses come back on the
master's own ID (SmartConnect tracks it); the slaves' RID/BID go nowhere.

The vendor IP is not hand-configured either: this script also writes
rtl/generated/fb_vendor_ip_cfg/fb_vendor_ip_cfg.tcl, which vendor_ip.tcl
sources to customize the IP-catalog AXI Crossbar (the same parameters as the
leg B1 wrapper, which bin/check_xbar_params.py proves) and to build the
SmartConnect block design (ports, windows, connectivity as exclusions).

Output (generated, never hand-edited):
    rtl/generated/fb_data_fabric_bridge/fb_data_fabric.sv
    rtl/generated/fb_data_fabric_xbar/fb_data_fabric.sv
    rtl/generated/fb_data_fabric_sc/fb_data_fabric.sv
    rtl/generated/fb_vendor_ip_cfg/fb_vendor_ip_cfg.tcl
"""
from __future__ import annotations

import argparse
import csv
import math
import re
import sys
import tomllib
from dataclasses import dataclass
from pathlib import Path

AREA = Path(__file__).resolve().parent.parent
CONFIG = AREA / "rtl/bridges/configs/bridge_fb_data.toml"
OUT = AREA / "rtl/generated"
BRIDGE_PKG = AREA / "rtl/bridges/generated/bridge_fb_data/bridge_fb_data_pkg.sv"

ACCEPTANCE = 16
ISSUING = 16
XBAR = "axi_crossbar_v2_1_37_axi_crossbar"
TIE0, TIE1 = "1'b0", "1'b1"

# Request-side fields in the order the wrappers list them. (name, width key)
AR = [("arid", "mid"), ("araddr", "aw"), ("arlen", 8), ("arsize", 3), ("arburst", 2),
      ("arlock", 1), ("arcache", 4), ("arprot", 3), ("arqos", 4)]
AW = [("awid", "mid"), ("awaddr", "aw"), ("awlen", 8), ("awsize", 3), ("awburst", 2),
      ("awlock", 1), ("awcache", 4), ("awprot", 3), ("awqos", 4)]
R = [("rid", "mid"), ("rdata", "dw"), ("rresp", 2), ("rlast", 1)]
W = [("wdata", "dw"), ("wstrb", "sw"), ("wlast", 1)]
B = [("bid", "mid"), ("bresp", 2)]


@dataclass(frozen=True)
class Port:
    name: str
    prefix: str
    channels: str          # rd | wr | rw
    id_width: int
    addr_width: int
    data_width: int
    base: int = 0
    size: int = 0

    @property
    def rd(self) -> bool:
        return self.channels in ("rd", "rw")

    @property
    def wr(self) -> bool:
        return self.channels in ("wr", "rw")


def load(config: Path) -> tuple[list[Port], list[Port], dict[str, set[str]]]:
    data = tomllib.loads(config.read_text())["bridge"]
    masters = [Port(m["name"], m["prefix"], m["channels"], m["id_width"], m["addr_width"],
                    m["data_width"]) for m in data["masters"]]
    slaves = [Port(s["name"], s["prefix"], s["channels"], s["id_width"], s["addr_width"],
                   s["data_width"], int(s["base_addr"], 0), int(s["addr_range"], 0))
              for s in data["slaves"]]
    conn_path = config.with_name(config.stem + "_connectivity.csv")
    conn: dict[str, set[str]] = {}
    with conn_path.open() as fh:
        rows = list(csv.reader(fh))
    header = rows[0][1:]
    for row in rows[1:]:
        conn[row[0]] = {s for s, bit in zip(header, row[1:]) if bit.strip() == "1"}
    check(masters, slaves, conn)
    return masters, slaves, conn


def check(masters: list[Port], slaves: list[Port], conn: dict[str, set[str]]) -> None:
    """Refuse anything the single-width vendor crossbar cannot express."""
    widths = {p.data_width for p in masters + slaves}
    if len(widths) != 1:
        sys.exit(f"gen_fabric_legs: one data width required on every port, got {widths}")
    mid = {m.id_width for m in masters}
    if len(mid) != 1:
        sys.exit(f"gen_fabric_legs: one master ID width required, got {mid}")
    sid = mid.pop() + max(1, math.ceil(math.log2(len(masters))))
    for s in slaves:
        if s.id_width != sid:
            sys.exit(f"gen_fabric_legs: slave {s.name} id_width {s.id_width}, expected {sid}")
        if s.size & (s.size - 1) or s.base % s.size:
            sys.exit(f"gen_fabric_legs: slave {s.name} window must be a power of two, aligned")
    for m in masters:
        if m.name not in conn:
            sys.exit(f"gen_fabric_legs: master {m.name} missing from connectivity")


def widths(masters: list[Port], slaves: list[Port]) -> dict[str, int]:
    dw = masters[0].data_width
    return {"mid": masters[0].id_width, "sid": slaves[0].id_width,
            "aw": masters[0].addr_width, "dw": dw, "sw": dw // 8}


def decl(direction: str, width: int, name: str) -> str:
    vec = f"[{width - 1}:0] " if width > 1 else ""
    return f"    {direction:<6} logic {vec}{name}"


def port_list(masters: list[Port], slaves: list[Port], w: dict[str, int]) -> list[str]:
    def fields(port: Port, side: str) -> list[str]:
        idk = "mid" if side == "m" else "sid"
        req_in = "input" if side == "m" else "output"
        rsp_in = "output" if side == "m" else "input"

        def width(key: str | int) -> int:
            return w[idk] if key == "mid" else (w[key] if isinstance(key, str) else key)

        out = []
        if port.wr:
            out += [decl(req_in, width(k), port.prefix + n) for n, k in AW]
            out += [decl(req_in, 1, port.prefix + "awvalid"), decl(rsp_in, 1, port.prefix + "awready")]
            out += [decl(req_in, width(k), port.prefix + n) for n, k in W]
            out += [decl(req_in, 1, port.prefix + "wvalid"), decl(rsp_in, 1, port.prefix + "wready")]
            out += [decl(rsp_in, width(k), port.prefix + n) for n, k in B]
            out += [decl(rsp_in, 1, port.prefix + "bvalid"), decl(req_in, 1, port.prefix + "bready")]
        if port.rd:
            out += [decl(req_in, width(k), port.prefix + n) for n, k in AR]
            out += [decl(req_in, 1, port.prefix + "arvalid"), decl(rsp_in, 1, port.prefix + "arready")]
            out += [decl(rsp_in, width(k), port.prefix + n) for n, k in R]
            out += [decl(rsp_in, 1, port.prefix + "rvalid"), decl(req_in, 1, port.prefix + "rready")]
        return out

    lines = ["    input  logic aclk", "    input  logic aresetn"]
    for m in masters:
        lines.append(f"    // master {m.name} ({m.channels})")
        lines += fields(m, "m")
    for s in slaves:
        lines.append(f"    // slave {s.name} ({s.channels}) 0x{s.base:08X} + 0x{s.size:X}")
        lines += fields(s, "s")
    # commas on every declaration but the last; comments carry none
    decls = [i for i, ln in enumerate(lines) if not ln.lstrip().startswith("//")]
    return [ln + ("," if i in decls[:-1] else "") for i, ln in enumerate(lines)]


HEADER = """\
// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Generated by: projects/fpga-systems/Genesys2/fabric-benchmark/bin/gen_fabric_legs.py
// Source:       rtl/bridges/configs/bridge_fb_data.toml (+ _connectivity.csv)
// DO NOT EDIT -- regenerate.
//
// Module: fb_data_fabric  ({leg})
// The data fabric under test. Every leg defines this module with this exact
// port list; the leg's filelist picks the file. See PRD.md section 4.
"""


def bridge_xbar_id_width() -> int:
    """The bridge's slave-side ID width, from its generated package. Since
    bridge TASK-018 it is {master index, remap slot} and narrower than the
    wrapper's {slot, master id} whenever a master's ID is wider than a slot."""
    m = re.search(r"localparam int XBAR_ID_WIDTH\s*=\s*(\d+)", BRIDGE_PKG.read_text())
    if not m:
        sys.exit(f"gen_fabric_legs: no XBAR_ID_WIDTH in {BRIDGE_PKG}")
    return int(m.group(1))


def emit_bridge(masters: list[Port], slaves: list[Port], w: dict[str, int]) -> str:
    # Every leg presents the same slave-side ID width (sid). The bridge's own
    # is fiw <= sid: request IDs are zero-extended to sid, response IDs come
    # back as their low fiw bits (a slave echoes the request ID, so the upper
    # bits are the zeros put there). Explicit, so no port is width-mismatched.
    fiw = bridge_xbar_id_width()
    if fiw > w["sid"]:
        sys.exit(f"gen_fabric_legs: bridge XBAR_ID_WIDTH {fiw} exceeds the slave ID width {w['sid']}")
    nets, assigns = [], []
    conns = ["        .aclk(aclk)", "        .aresetn(aresetn)"]
    for p in masters + slaves:
        is_m = p in masters
        for n, k in (AW + W + B if p.wr else []) + (AR + R if p.rd else []):
            sig = p.prefix + n
            if is_m or k != "mid" or fiw == w["sid"]:
                conns.append(f"        .{sig}({sig})")
            elif n in ("awid", "arid"):
                nets.append(f"    logic [FIW-1:0] u_{sig};")
                assigns.append(f"    assign {sig} = {w['sid']}'(u_{sig});")
                conns.append(f"        .{sig}(u_{sig})")
            else:
                conns.append(f"        .{sig}({sig}[FIW-1:0])")
        hs = (["awvalid", "awready", "wvalid", "wready", "bvalid", "bready"] if p.wr else []) + \
             (["arvalid", "arready", "rvalid", "rready"] if p.rd else [])
        conns += [f"        .{p.prefix}{n}({p.prefix}{n})" for n in hs]
        # USER and REGION are not on the benchmark port set: tie inputs, leave outputs open.
        if is_m:
            conns += ([f"        .{p.prefix}awregion(4'b0)", f"        .{p.prefix}awuser(1'b0)",
                       f"        .{p.prefix}wuser(1'b0)", f"        .{p.prefix}buser()"] if p.wr else [])
            conns += ([f"        .{p.prefix}arregion(4'b0)", f"        .{p.prefix}aruser(1'b0)",
                       f"        .{p.prefix}ruser()"] if p.rd else [])
        else:
            conns += ([f"        .{p.prefix}awregion()", f"        .{p.prefix}awuser()",
                       f"        .{p.prefix}wuser()", f"        .{p.prefix}buser(1'b0)"] if p.wr else [])
            conns += ([f"        .{p.prefix}arregion()", f"        .{p.prefix}aruser()",
                       f"        .{p.prefix}ruser(1'b0)"] if p.rd else [])
    # The bridge's unmapped-address log (OOR contract) is not on the benchmark
    # port set: never clear it, read nothing from it. Unmapped accesses still
    # answer DECERR, which is what the fabric test checks.
    conns += ["        .unmapped_clear(1'b0)", "        .unmapped_irq()",
              "        .unmapped_addr()", "        .unmapped_count()"]
    body = ",\n".join(conns)
    return (HEADER.format(leg="leg A: bridge-generated crossbar")
            + "\n`timescale 1ns / 1ps\n\nmodule fb_data_fabric (\n"
            + "\n".join(port_list(masters, slaves, w))
            + "\n);\n\n"
            + (f"    // Bridge slave-side ID width ({{master index, remap slot}}), {fiw} of {w['sid']}\n"
               "    localparam int FIW = bridge_fb_data_pkg::XBAR_ID_WIDTH;\n"
               + "\n".join(nets) + "\n" + "\n".join(assigns) + "\n\n" if nets else "")
            + "    bridge_fb_data u_fabric (\n" + body + "\n    );\n\nendmodule : fb_data_fabric\n")


def hexv(values: list[int], bits: int) -> str:
    """Pack per-slot values, slot 0 in the LSBs, as one SV literal."""
    total = 0
    for i, v in enumerate(values):
        total |= v << (i * bits)
    return f"{bits * len(values)}'h{total:0{bits * len(values) // 4}X}"


def emit_xbar(masters: list[Port], slaves: list[Port], w: dict[str, int],
              conn: dict[str, set[str]]) -> str:
    ns, nm = len(masters), len(slaves)
    mid, sid, aw, dw, sw = w["mid"], w["sid"], w["aw"], w["dw"], w["sw"]
    rd_conn = [sum(1 << i for i, m in enumerate(masters) if m.rd and s.name in conn[m.name])
               for s in slaves]
    wr_conn = [sum(1 << i for i, m in enumerate(masters) if m.wr and s.name in conn[m.name])
               for s in slaves]
    params = [
        ('C_FAMILY', '"kintex7"'),
        ("C_NUM_SLAVE_SLOTS", str(ns)),
        ("C_NUM_MASTER_SLOTS", str(nm)),
        ("C_AXI_ID_WIDTH", str(sid)),
        ("C_AXI_ADDR_WIDTH", str(aw)),
        ("C_AXI_DATA_WIDTH", str(dw)),
        ("C_AXI_PROTOCOL", "0"),
        ("C_NUM_ADDR_RANGES", "1"),
        ("C_M_AXI_BASE_ADDR", hexv([s.base for s in slaves], 64)),
        ("C_M_AXI_ADDR_WIDTH", hexv([int(math.log2(s.size)) for s in slaves], 32)),
        ("C_S_AXI_BASE_ID", hexv([i << mid for i in range(ns)], 32)),
        ("C_S_AXI_THREAD_ID_WIDTH", hexv([mid] * ns, 32)),
        ("C_AXI_SUPPORTS_USER_SIGNALS", "0"),
        ("C_M_AXI_WRITE_CONNECTIVITY", hexv(wr_conn, 32)),
        ("C_M_AXI_READ_CONNECTIVITY", hexv(rd_conn, 32)),
        ("C_R_REGISTER", "0"),
        ("C_S_AXI_SINGLE_THREAD", hexv([0] * ns, 32)),
        ("C_S_AXI_WRITE_ACCEPTANCE", hexv([ACCEPTANCE if m.wr else 1 for m in masters], 32)),
        ("C_S_AXI_READ_ACCEPTANCE", hexv([ACCEPTANCE if m.rd else 1 for m in masters], 32)),
        ("C_M_AXI_WRITE_ISSUING", hexv([ISSUING if s.wr else 1 for s in slaves], 32)),
        ("C_M_AXI_READ_ISSUING", hexv([ISSUING if s.rd else 1 for s in slaves], 32)),
        ("C_S_AXI_ARB_PRIORITY", hexv([0] * ns, 32)),
        ("C_M_AXI_SECURE", hexv([0] * nm, 32)),
        ("C_CONNECTIVITY_MODE", "1"),
    ]

    def field_w(key: str | int, side_id: int) -> int:
        return side_id if key == "mid" else (w[key] if isinstance(key, str) else key)

    lines: list[str] = []
    # Flattened slot vectors, one per crossbar port, slot 0 in the LSBs.
    vec = {}
    for side, ports, n, idw in (("s", masters, ns, sid), ("m", slaves, nm, sid)):
        for name, key in AW + AR + W + R + B:
            vec[f"{side}_{name}"] = field_w(key, idw) * n
        for hs in ("awvalid", "awready", "wvalid", "wready", "bvalid", "bready",
                   "arvalid", "arready", "rvalid", "rready"):
            vec[f"{side}_{hs}"] = n
    for name, width in vec.items():
        lines.append(f"    logic [{width - 1}:0] w_{name};")
    lines.append("")

    def slot(side: str, name: str, i: int, width: int) -> str:
        return f"w_{side}_{name}[{i * width + width - 1}:{i * width}]" if width > 1 \
            else f"w_{side}_{name}[{i}]"

    # Masters (crossbar SI slots). Unused channels are tied idle.
    for i, m in enumerate(masters):
        p = m.prefix
        lines.append(f"    // SI {i}: {m.name} ({m.channels})")
        for ch_on, req, rsp, vld, rdy, rvld, rrdy in (
                (m.wr, AW + W, B, ("awvalid", "wvalid"), ("awready", "wready"), "bvalid", "bready"),
                (m.rd, AR, R, ("arvalid",), ("arready",), "rvalid", "rready")):
            for name, key in req:
                width = sid if key == "mid" else field_w(key, mid)
                if not ch_on:
                    lines.append(f"    assign {slot('s', name, i, width)} = '0;")
                elif key == "mid":
                    lines.append(f"    assign {slot('s', name, i, width)} = {{{sid - mid}'b0, {p}{name}}};")
                else:
                    lines.append(f"    assign {slot('s', name, i, width)} = {p}{name};")
            for v in vld:
                lines.append(f"    assign w_s_{v}[{i}] = {p + v if ch_on else TIE0};")
            for r in rdy:
                if ch_on:
                    lines.append(f"    assign {p}{r} = w_s_{r}[{i}];")
            lines.append(f"    assign w_s_{rrdy}[{i}] = {p + rrdy if ch_on else TIE1};")
            if ch_on:
                lines.append(f"    assign {p}{rvld} = w_s_{rvld}[{i}];")
                for name, key in rsp:
                    width = sid if key == "mid" else field_w(key, mid)
                    src = slot("s", name, i, width)
                    if key == "mid":  # strip the slot bits: low `mid` bits of this slot
                        src = f"w_s_{name}[{i * width + mid - 1}:{i * width}]"
                    lines.append(f"    assign {p}{name} = {src};")
        lines.append("")

    # Slaves (crossbar MI slots). Unused channels: responses tied idle.
    for i, s in enumerate(slaves):
        p = s.prefix
        lines.append(f"    // MI {i}: {s.name} ({s.channels})")
        for ch_on, req, rsp, vld, rdy, rvld, rrdy in (
                (s.wr, AW + W, B, ("awvalid", "wvalid"), ("awready", "wready"), "bvalid", "bready"),
                (s.rd, AR, R, ("arvalid",), ("arready",), "rvalid", "rready")):
            if ch_on:
                for name, key in req:
                    width = sid if key == "mid" else field_w(key, sid)
                    lines.append(f"    assign {p}{name} = {slot('m', name, i, width)};")
                for v in vld:
                    lines.append(f"    assign {p}{v} = w_m_{v}[{i}];")
                for r in rdy:
                    lines.append(f"    assign w_m_{r}[{i}] = {p}{r};")
                lines.append(f"    assign {p}{rrdy} = w_m_{rrdy}[{i}];")
                lines.append(f"    assign w_m_{rvld}[{i}] = {p}{rvld};")
                for name, key in rsp:
                    width = sid if key == "mid" else field_w(key, sid)
                    lines.append(f"    assign {slot('m', name, i, width)} = {p}{name};")
            else:
                for r in rdy:
                    lines.append(f"    assign w_m_{r}[{i}] = 1'b0;")
                lines.append(f"    assign w_m_{rvld}[{i}] = 1'b0;")
                for name, key in rsp:
                    width = sid if key == "mid" else field_w(key, sid)
                    lines.append(f"    assign {slot('m', name, i, width)} = '0;")
        lines.append("")

    pmap = ",\n".join(f"        .{k:<28}({v})" for k, v in params)
    conns = ["        .aclk(aclk)", "        .aresetn(aresetn)"]
    for side in ("s", "m"):
        for name, _ in AW + AR + W + R + B:
            conns.append(f"        .{side}_axi_{name}(w_{side}_{name})")
        for hs in ("awvalid", "awready", "wvalid", "wready", "bvalid", "bready",
                   "arvalid", "arready", "rvalid", "rready"):
            conns.append(f"        .{side}_axi_{hs}(w_{side}_{hs})")
    n = ns
    conns += [f"        .s_axi_wid({{{n}{{{sid}'b0}}}})",
              f"        .s_axi_awuser({n}'b0)", f"        .s_axi_wuser({n}'b0)",
              f"        .s_axi_aruser({n}'b0)", "        .s_axi_buser()", "        .s_axi_ruser()",
              "        .m_axi_awregion()", "        .m_axi_arregion()", "        .m_axi_wid()",
              "        .m_axi_awuser()", "        .m_axi_wuser()", "        .m_axi_aruser()",
              f"        .m_axi_buser({nm}'b0)", f"        .m_axi_ruser({nm}'b0)"]
    body = ",\n".join(conns)
    return (HEADER.format(leg="leg B1: Xilinx AXI Crossbar v2.1")
            + f"//\n// Matched to the bridge (gen_fabric_legs.py docstring): acceptance {ACCEPTANCE},\n"
            + f"// issuing {ISSUING}, no register slices, round-robin. Base IDs = slot << {mid}.\n"
            + "\n`timescale 1ns / 1ps\n\nmodule fb_data_fabric (\n"
            + "\n".join(port_list(masters, slaves, w))
            + "\n);\n\n" + "\n".join(lines)
            + f"\n    {XBAR} #(\n{pmap}\n    ) u_fabric (\n{body}\n    );\n\nendmodule : fb_data_fabric\n")


SC_WRAPPER = "fb_sc_wrapper"


def emit_sc(masters: list[Port], slaves: list[Port], w: dict[str, int]) -> str:
    """Leg B2: the SmartConnect block design's wrapper behind the common port set.

    BD interface ports are named after the TOML ports, so the wrapper's pins
    are <name>_<signal> -- the same names as this module's ports.
    """
    mid, sid = w["mid"], w["sid"]
    conns = ["        .aclk(aclk)", "        .aresetn(aresetn)"]
    lines: list[str] = []
    for slot, m in enumerate(masters):
        p, b = m.prefix, m.name + "_"
        for ch_on, req, rsp, hs_in, hs_out, user in (
                (m.wr, AW + W, B, ("awvalid", "wvalid", "bready"), ("awready", "wready", "bvalid"), "awuser"),
                (m.rd, AR, R, ("arvalid", "rready"), ("arready", "rvalid"), "aruser")):
            if not ch_on:
                continue
            conns += [f"        .{b}{n}({p}{n})" for n, _ in req + rsp]
            conns += [f"        .{b}{n}({p}{n})" for n in hs_in + hs_out]
    for s in slaves:
        p, b = s.prefix, s.name + "_"
        for ch_on, req, rsp, hs_out, hs_in, user, idf, rid in (
                (s.wr, AW + W, B, ("awvalid", "wvalid", "bready"), ("awready", "wready", "bvalid"), "awuser", "awid", "bid"),
                (s.rd, AR, R, ("arvalid", "rready"), ("arready", "rvalid"), "aruser", "arid", "rid")):
            if not ch_on:
                continue
            conns += [f"        .{b}{n}({p}{n})" for n, _ in req + rsp if n not in (idf, rid)]
            conns += [f"        .{b}{n}({p}{n})" for n in hs_out + hs_in]
            # MI ID width is 0: no ID reaches the slave, none comes back
            lines.append(f"    assign {p}{idf} = '0;")
            lines.append(f"    // {s.name}: {rid} has no SmartConnect pin (MI ID width 0)")
            lines.append(f"    wire unused_{s.name}_{rid} = ^{p}{rid};")
    body = ",\n".join(conns)
    return (HEADER.format(leg="leg B2: Xilinx SmartConnect (IP-integrator block design)")
            + "//\n// SmartConnect has no MI ID (width 0, read-only): every slave-side ID is 0.\n"
            + "// The endpoints select channels by address (fb_endpoints CH_SEL_ADDR=1).\n"
            + "// See the generator docstring. fb_sc_wrapper is made by fpga/tcl/vendor_ip.tcl.\n"
            + "\n`timescale 1ns / 1ps\n\nmodule fb_data_fabric (\n"
            + "\n".join(port_list(masters, slaves, w))
            + "\n);\n\n" + "\n".join(lines)
            + f"\n\n    {SC_WRAPPER} u_fabric (\n{body}\n    );\n\nendmodule : fb_data_fabric\n")


def emit_ip_cfg(masters: list[Port], slaves: list[Port], w: dict[str, int],
                conn: dict[str, set[str]]) -> str:
    """Tcl for vendor_ip.tcl: the IP-catalog crossbar CONFIG and the BD layout."""
    mid, sid = w["mid"], w["sid"]
    cfg = [("NUM_SI", len(masters)), ("NUM_MI", len(slaves)), ("PROTOCOL", "AXI4"),
           ("ADDR_WIDTH", w["aw"]), ("DATA_WIDTH", w["dw"]), ("ID_WIDTH", sid),
           ("CONNECTIVITY_MODE", "SAMD"), ("R_REGISTER", 0), ("ADDR_RANGES", 1)]
    for j, s in enumerate(slaves):
        cfg += [(f"M{j:02d}_A00_BASE_ADDR", f"0x{s.base:016X}"),
                (f"M{j:02d}_A00_ADDR_WIDTH", int(math.log2(s.size))),
                (f"M{j:02d}_READ_ISSUING", ISSUING if s.rd else 1),
                (f"M{j:02d}_WRITE_ISSUING", ISSUING if s.wr else 1),
                (f"M{j:02d}_SECURE", 0)]
        for i, m in enumerate(masters):
            cfg += [(f"M{j:02d}_S{i:02d}_READ_CONNECTIVITY", int(m.rd and s.name in conn[m.name])),
                    (f"M{j:02d}_S{i:02d}_WRITE_CONNECTIVITY", int(m.wr and s.name in conn[m.name]))]
    for i, m in enumerate(masters):
        cfg += [(f"S{i:02d}_BASE_ID", f"0x{i << mid:08X}"),
                (f"S{i:02d}_THREAD_ID_WIDTH", mid),
                (f"S{i:02d}_SINGLE_THREAD", 0),
                (f"S{i:02d}_READ_ACCEPTANCE", ACCEPTANCE if m.rd else 1),
                (f"S{i:02d}_WRITE_ACCEPTANCE", ACCEPTANCE if m.wr else 1),
                (f"S{i:02d}_ARB_PRIORITY", 0)]
    mode = {"rd": "READ_ONLY", "wr": "WRITE_ONLY", "rw": "READ_WRITE"}
    out = ["# Generated by bin/gen_fabric_legs.py from rtl/bridges/configs/bridge_fb_data.toml",
           "# (+ _connectivity.csv). DO NOT EDIT -- regenerate. Sourced by fpga/tcl/vendor_ip.tcl.",
           "",
           f"set FB_PART      xc7k325tffg900-2",
           f"set FB_FREQ_HZ   {100_000_000}",
           f"set FB_DW        {w['dw']}",
           f"set FB_AW        {w['aw']}",
           f"set FB_MID       {mid}",
           f"set FB_SID       {sid}",
           f"set FB_ACCEPT    {ACCEPTANCE}",
           "",
           "# leg B1, IP catalog: CONFIG.<key> for axi_crossbar (matches the HDL wrapper)",
           "set FB_XBAR_CONFIG [list \\"]
    out += [f"    CONFIG.{k} {{{v}}} \\" for k, v in cfg]
    out += ["]", "", "# leg B2, block design: {name rw_mode} per SI, slot order"]
    out.append("set FB_MASTERS [list " + " ".join(f"{{{m.name} {mode[m.channels]}}}" for m in masters) + "]")
    out.append("# {name rw_mode base range} per MI")
    out.append("set FB_SLAVES [list " + " ".join(
        f"{{{s.name} {mode[s.channels]} 0x{s.base:08X} 0x{s.size:X}}}" for s in slaves) + "]")
    out.append("# master -> slaves it reaches; every other pair is excluded (DECERR)")
    out.append("set FB_CONN [dict create " + " ".join(
        f"{m.name} {{{' '.join(s.name for s in slaves if s.name in conn[m.name])}}}" for m in masters) + "]")
    return "\n".join(out) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--config", type=Path, default=CONFIG)
    ap.add_argument("--out", type=Path, default=OUT)
    args = ap.parse_args()
    masters, slaves, conn = load(args.config)
    w = widths(masters, slaves)
    outputs = [(f"fb_data_fabric_{leg}", "fb_data_fabric.sv", text) for leg, text in (
        ("bridge", emit_bridge(masters, slaves, w)),
        ("xbar", emit_xbar(masters, slaves, w, conn)),
        ("sc", emit_sc(masters, slaves, w)))]
    outputs.append(("fb_vendor_ip_cfg", "fb_vendor_ip_cfg.tcl", emit_ip_cfg(masters, slaves, w, conn)))
    for sub, name, text in outputs:
        d = args.out / sub
        d.mkdir(parents=True, exist_ok=True)
        (d / name).write_text(text)
        print(f"[gen_fabric_legs] {d / name}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
