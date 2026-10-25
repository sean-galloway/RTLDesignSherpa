#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Generate the bridge stress harness for one DUT bridge TOML.

The harness is everything around the device under test: the UART host link
and configuration bridge, the control regblock, and one stress master per
DUT master port and one stress slave per DUT slave port, each the protocol
shell matching that port and each with its own regblock in its own clock.
It is generated, not hand-written, because it is a pure function of the
DUT's port list -- and the phase 2/3 builds (AXI3/AXI5, AXI-Lite, APB, WB4)
are new TOMLs through this same script, not new harnesses.

    python3 bin/gen_bs_harness.py rtl/bridges/configs/bridge_bs_axi4.toml

writes rtl/generated/bs_harness_<dut>/bs_harness_<dut>.sv and
rtl/generated/filelists/bs_harness_<dut>.f. Clock domains: a port with
`cdc = true` runs on cclk, everything else on aclk (the DUT's clock).

A port named in the TOML's `[harness] vendor` list gets no stress block: its
DUT pins become harness pins, for the board top to connect to third-party IP
(build-xil). Such a master counts as done and error-free in the roll-up; its
results are the host's to read. The configuration bridge's two AXI4-Lite
windows ext0 / ext1 then leave the harness too, for that IP's control ports,
and EXT_STS0..3 in the control block carry 128 bits of its status in; in a
build without vendor ports ext0 / ext1 answer SLVERR.

A DUT TOML whose `variants` holds "mon" is built as the bridge's monitored
variant (<dut>_mon, with `use_cfg_regblock` and the write-only
monbus_axil4_group_1wr): an Ocelus monitor on every port. Its cfg regblock
is the configuration bridge's window ext2; ext3 is the error window, a RAM
inside the harness the group's write master fills (the host's old drain
addressing, now memory-backed), and MON_ERR_REC_COUNT in the cfg regblock
says how many records have landed. Without it ext2 / ext3 answer SLVERR and
STATUS.HAS_MON reads 0.
"""
from __future__ import annotations

import argparse
import sys
import tomllib
from dataclasses import dataclass, field
from pathlib import Path
from types import SimpleNamespace
from typing import List

AREA = Path(__file__).resolve().parent.parent
REPO = AREA.parents[3]          # ./projects/fpga-systems/Genesys2/bridge-stress
# The AXI5 pin set of a bridge port and the fabric's ID layout come from the
# bridge generator itself, so the harness cannot drift from the DUT.
sys.path.insert(0, str(REPO / 'projects/components/fabric-gen-ip/bridge/bin'))
from bridge_pkg.components.axi4_timing_wrapper_component import axi5_exposed_ext_signals  # noqa: E402
from bridge_pkg.width_utils import fabric_local_id_width, id_prefix_width  # noqa: E402
MAX_PORTS = 8          # configuration windows bridge_bs_cfg carries per side
PROTO_CODE = {'axi4': 0, 'axi3': 1, 'axi5': 2, 'axil': 3, 'axil5': 4,
              'apb': 5, 'apb5': 6, 'wb4': 7}

AR = [('arid', 'IW'), ('araddr', '32'), ('arlen', '8'), ('arsize', '3'),
      ('arburst', '2'), ('arlock', '1'), ('arcache', '4'), ('arprot', '3'),
      ('arqos', '4'), ('arregion', '4'), ('aruser', 'UW'),
      ('arvalid', '1'), ('arready', '1')]
R = [('rid', 'IW'), ('rdata', 'DW'), ('rresp', '2'), ('rlast', '1'),
     ('ruser', 'UW'), ('rvalid', '1'), ('rready', '1')]
AW = [(n.replace('ar', 'aw', 1), w) for n, w in AR]
W = [('wdata', 'DW'), ('wstrb', 'SW'), ('wlast', '1'), ('wuser', 'UW'),
     ('wvalid', '1'), ('wready', '1')]
B = [('bid', 'IW'), ('bresp', '2'), ('buser', 'UW'), ('bvalid', '1'), ('bready', '1')]

# AXI3: 4-bit AxLEN, 2-bit AxLOCK, WID, no AxQOS / AxREGION
AR3 = [(n, {'arlen': '4', 'arlock': '2'}.get(n, w)) for n, w in AR
       if n not in ('arqos', 'arregion')]
AW3 = [(n.replace('ar', 'aw', 1), w) for n, w in AR3]
W3 = [('wid', 'IW')] + W

# AXI5: no AxREGION; the shells carry every AXI5 pin (a disabled feature's pin
# is tied off inside), the DUT port only those of its axi5_features.
AR5 = [(n, w) for n, w in AR if n != 'arregion']
AW5 = [(n.replace('ar', 'aw', 1), w) for n, w in AR5]
AW5_X = [('awatop', '6'), ('awnsaid', '4'), ('awtrace', '1'), ('awmpam', '11'),
         ('awmecid', '16'), ('awidunq', '1'), ('awtagop', '2'), ('awakeup', '1')]
W5_X = [('wpoison', '1'), ('wtag', 'TW'), ('wtagupdate', 'NT')]
B5_X = [('btrace', '1'), ('bidunq', '1'), ('btagmatch', '2')]
AR5_X = [('arnsaid', '4'), ('artrace', '1'), ('armpam', '11'), ('armecid', '16'),
         ('aridunq', '1'), ('archunken', '1'), ('artagop', '2')]
R5_X = [('rtrace', '1'), ('ridunq', '1'), ('rpoison', '1'), ('rchunkv', '1'),
        ('rchunknum', '4'), ('rchunkstrb', 'NT'), ('rtag', 'TW')]
# What the AXI5 stress shells model; any other feature on a DUT port is refused.
AXI5_STRESS_FEATURES = ('nsaid', 'trace', 'mpam', 'mecid', 'poison', 'unique', 'atomic', 'mte')

# The configuration bridge's AXI4-Lite windows for vendor IP control ports:
# (signal, width, driven by the bridge)
EXT_AXIL = [('awaddr', 32, 1), ('awprot', 3, 1), ('awvalid', 1, 1), ('awready', 1, 0),
            ('wdata', 32, 1), ('wstrb', 4, 1), ('wvalid', 1, 1), ('wready', 1, 0),
            ('bresp', 2, 0), ('bvalid', 1, 0), ('bready', 1, 1),
            ('araddr', 32, 1), ('arprot', 3, 1), ('arvalid', 1, 1), ('arready', 1, 0),
            ('rdata', 32, 0), ('rresp', 2, 0), ('rvalid', 1, 0), ('rready', 1, 1)]
EXT_WINDOWS = ('ext0', 'ext1')
# Its windows for the DUT's Ocelus monitors (mon variant), inside the harness:
# ext2 the cfg regblock (s_cfg_axil), ext3 the error-window RAM (read-only),
# filled by the write-only group's master. Each window is 64 KB; the DUT
# sees the offset inside it.
MON_WINDOWS = ('ext2', 'ext3')
MON_CFG, MON_DRAIN = MON_WINDOWS

# Single-beat protocols (phase 3): the DUT port's pins as (name, width, by),
# `by` the side that drives the pin -- 'q' the requester, 'c' the completer --
# so a DUT master port's inputs are the 'q' pins and a slave port's the 'c'
# pins. Names after the TOML prefix, exactly as the bridge generator emits them.
AXIL = [('awaddr', 'AW', 'q'), ('awprot', '3', 'q'), ('awvalid', '1', 'q'), ('awready', '1', 'c'),
        ('wdata', 'DW', 'q'), ('wstrb', 'SW', 'q'), ('wvalid', '1', 'q'), ('wready', '1', 'c'),
        ('bresp', '2', 'c'), ('bvalid', '1', 'c'), ('bready', '1', 'q'),
        ('araddr', 'AW', 'q'), ('arprot', '3', 'q'), ('arvalid', '1', 'q'), ('arready', '1', 'c'),
        ('rdata', 'DW', 'c'), ('rresp', '2', 'c'), ('rvalid', '1', 'c'), ('rready', '1', 'q')]
AXIL5 = AXIL + [('awid', 'IW', 'q'), ('awuser', 'UW', 'q'), ('awtrace', '1', 'q'),
                ('wuser', 'UW', 'q'), ('wpoison', 'PW', 'q'),
                ('bid', 'IW', 'c'), ('buser', 'UW', 'c'), ('btrace', '1', 'c'),
                ('arid', 'IW', 'q'), ('aruser', 'UW', 'q'), ('artrace', '1', 'q'),
                ('rid', 'IW', 'c'), ('ruser', 'UW', 'c'), ('rtrace', '1', 'c'), ('rpoison', 'PW', 'c')]
APB = [('PSEL', '1', 'q'), ('PENABLE', '1', 'q'), ('PADDR', 'AW', 'q'), ('PWRITE', '1', 'q'),
       ('PWDATA', 'DW', 'q'), ('PSTRB', 'SW', 'q'), ('PPROT', '3', 'q'),
       ('PRDATA', 'DW', 'c'), ('PREADY', '1', 'c'), ('PSLVERR', '1', 'c')]
APB5 = APB + [('PAUSER', 'UW', 'q'), ('PWUSER', 'UW', 'q'), ('PWAKEUP', '1', 'q'),
              ('PRUSER', 'UW', 'c'), ('PBUSER', 'UW', 'c')]
WB = [('CYC', '1', 'q'), ('STB', '1', 'q'), ('WE', '1', 'q'), ('ADR', 'AW', 'q'),
      ('DAT_W', 'DW', 'q'), ('SEL', 'SW', 'q'), ('CTI', '3', 'q'), ('BTE', '2', 'q'),
      ('STALL', '1', 'c'), ('ACK', '1', 'c'), ('ERR', '1', 'c'), ('RTY', '1', 'c'),
      ('DAT_R', 'DW', 'c')]
SINGLE = {'axil': AXIL, 'axil5': AXIL5, 'apb': APB, 'apb5': APB5, 'wb4': WB}
# A slave port is addr_width bits wide and sees the fabric address modulo
# 2^addr_width -- its window offset when narrower than 32 (an APB slave's
# usual case); the shells' address ports are 32 bits, zero-extended here, and
# bin/bstress.py runs such a slave in offset mode.
ADDR_PINS = ('awaddr', 'araddr', 'PADDR', 'ADR')
# protocol -> (shell module stem, the shell's pin stem: m_<stem>_ / s_<stem>_,
# the DUT pins the shell carries; the rest are tied 0 in or left open out)
_NOT_ON_SHELL = {'axil5': {'awuser', 'wuser', 'buser', 'aruser', 'ruser'},
                 'apb5': {'PAUSER', 'PWUSER', 'PRUSER', 'PBUSER'}, 'wb4': {'CTI', 'BTE'}}
SHELL = {pr: (mod, stem, {n for n, _, _ in SINGLE[pr]} - _NOT_ON_SHELL.get(pr, set()))
         for pr, mod, stem in (('axil', 'axil4', 'axil'), ('axil5', 'axil5', 'axil'),
                               ('apb', 'apb4', 'apb'), ('apb5', 'apb5', 'apb'),
                               ('wb4', 'wb4', 'wb'))}
# The cores issue IDs whatever the bus carries. A port whose protocol has no ID
# (AXI4-Lite, APB, APB5, WB4) gets this core ID width; bin/bstress.py applies
# the same rule, and the CSRs report it.
NOID = ('axil', 'apb', 'apb5', 'wb4')
NOID_IW = 4
# What the shells accept: AXI-Lite and WB4 32 or 64 bits, APB 32 bits.
SINGLE_DW = {'axil': (32, 64), 'axil5': (32, 64), 'apb': (32,), 'apb5': (32,), 'wb4': (32, 64)}

# protocol -> (AW, W, B, AR, R); the stress shells are <protocol>_{master,slave}_stress
CHANNELS = {'axi4': (AW, W, B, AR, R), 'axi3': (AW3, W3, B, AR3, R),
            'axi5': (AW5 + AW5_X, W + W5_X, B + B5_X, AR5 + AR5_X, R + R5_X)}


@dataclass
class Port:
    name: str
    prefix: str
    protocol: str
    channels: str
    dw: int
    iw: int
    uw: int
    cdc: bool
    base: int = 0
    size: int = 0
    features: List[str] = field(default_factory=list)   # axi5_features
    max_outstanding: int = 16
    vendor: bool = False       # [harness] vendor: pins out, no stress block
    aw: int = 32               # addr_width (single-beat ports: the address pins)

    @property
    def rd(self) -> bool:
        return self.channels in ('rd', 'rw')

    @property
    def wr(self) -> bool:
        return self.channels in ('wr', 'rw')

    @property
    def clk(self) -> str:
        return 'cclk' if self.cdc else 'aclk'

    @property
    def rst(self) -> str:
        return 'cresetn' if self.cdc else 'aresetn'

    @property
    def single(self) -> bool:
        return self.protocol in SINGLE

    @property
    def chans(self):
        return CHANNELS[self.protocol]

    def all_sigs(self) -> List[tuple]:
        aw, w, b, ar, r = self.chans
        return aw + w + b + ar + r

    def sigs(self) -> List[tuple]:
        """The DUT port's pins: for AXI5 the base set plus the pins of its
        axi5_features, exactly as the bridge generator declares them."""
        if self.single:
            # AXI-Lite splits by direction like AXI; APB and WB4 are one bus
            def keep(n):
                if self.protocol not in ('axil', 'axil5'):
                    return True
                return self.wr if n[0] in 'awb' else self.rd
            return [(n, w) for n, w, _ in SINGLE[self.protocol] if keep(n)]
        aw, w, b, ar, r = self.chans
        if self.protocol == 'axi5':
            def ext(ch):
                return [(n, str(wd)) for n, wd, _ in
                        axi5_exposed_ext_signals(ch, self.features, self.dw, self.channels)]
            aw, w, b, ar, r = (AW5 + ext('aw'), W + ext('w'), B + ext('b'),
                               AR5 + ext('ar'), R + ext('r'))
        out = []
        if self.wr:
            out += aw + w + b
        if self.rd:
            out += ar + r
        return out

    def en(self, feat: str) -> int:
        return int(self.protocol == 'axi5' and feat in self.features)

    def axi5_params(self) -> str:
        if self.protocol != 'axi5':
            return ''
        return (f", .EN_NSAID(1'b{self.en('nsaid')}), .EN_TRACE(1'b{self.en('trace')}),"
                f" .EN_MPAM(1'b{self.en('mpam')}), .EN_MECID(1'b{self.en('mecid')}),"
                f" .EN_POISON(1'b{self.en('poison')}), .EN_UNIQUE(1'b{self.en('unique')}),"
                f" .EN_ATOMIC(1'b{self.en('atomic')}), .EN_MTE(1'b{self.en('mte')})")


def has_mon(toml: Path) -> bool:
    """The DUT is built as its monitored variant (see the module docstring)."""
    variants = tomllib.loads(toml.read_text())['bridge'].get('variants', ['no'])
    if 'mon' in variants and len(variants) > 1:
        sys.exit(f'{toml.name}: a harness DUT is one variant; variants = {variants}')
    return 'mon' in variants


def load(toml: Path):
    doc = tomllib.loads(toml.read_text())
    cfg = doc['bridge']
    vendor = set(doc.get('harness', {}).get('vendor', []))
    ms, ss = [], []
    for m in cfg['masters']:
        ms.append(Port(m['name'], m['prefix'], m.get('protocol', 'axi4'),
                       m.get('channels', 'rw'), m['data_width'], m.get('id_width', 0),
                       max(1, m.get('user_width', 1)), bool(m.get('cdc', False)),
                       features=list(m.get('axi5_features', [])),
                       max_outstanding=int(m.get('max_outstanding', 16)),
                       vendor=m['name'] in vendor, aw=int(m.get('addr_width', 32))))
    for s in cfg['slaves']:
        ss.append(Port(s['name'], s['prefix'], s.get('protocol', 'axi4'),
                       s.get('channels', 'rw'), s['data_width'], s.get('id_width', 0),
                       max(1, s.get('user_width', 1)), bool(s.get('cdc', False)),
                       int(s['base_addr'], 0), int(s['addr_range'], 0),
                       features=list(s.get('axi5_features', [])),
                       vendor=s['name'] in vendor, aw=int(s.get('addr_width', 32))))
    for p in ms + ss:
        if p.protocol not in CHANNELS and p.protocol not in SINGLE:
            sys.exit(f'{p.name}: protocol {p.protocol!r} has no stress shell yet '
                     f'(have {sorted(CHANNELS) + sorted(SINGLE)})')
        if p.single:
            if p.dw not in SINGLE_DW[p.protocol]:
                sys.exit(f'{p.name}: {p.protocol} data_width {p.dw}; the stress shells take '
                         f'{SINGLE_DW[p.protocol]}')
            if p.protocol in NOID:
                p.iw = NOID_IW
            if p.vendor:
                sys.exit(f'{p.name}: [harness] vendor ports are AXI only')
        extra = set(p.features) - set(AXI5_STRESS_FEATURES)
        if extra:
            sys.exit(f'{p.name}: axi5_features {sorted(extra)} are not modelled by the '
                     f'stress shells yet (have {list(AXI5_STRESS_FEATURES)})')
    unknown = vendor - {p.name for p in ms + ss}
    if unknown:
        sys.exit(f'[harness] vendor names no port: {sorted(unknown)}')
    if len(ms) > MAX_PORTS or len(ss) > MAX_PORTS:
        sys.exit(f'at most {MAX_PORTS} masters and {MAX_PORTS} slaves')
    return cfg['name'], ms, ss


def single_shell(p: Port, side: str, i: int, head: str, extra: str = '') -> List[str]:
    """A single-beat stress shell (phase 3) on DUT port p: the instance, every
    DUT pin the shell drives tied to it, the DUT inputs it does not carry tied 0
    and its unused DUT outputs collected for lint. side: 'master' | 'slave'."""
    mod, stem, carried = SHELL[p.protocol]
    io = 'm' if side == 'master' else 's'
    # a DUT master port's inputs are the requester's pins, a slave port's the completer's
    dut_in = 'q' if side == 'master' else 'c'
    pins = {n: by for n, _, by in SINGLE[p.protocol]}
    have = [n for n, _ in p.sigs()]
    out: List[str] = []
    params = [f".EN_RD(1'b{int(p.rd)})", f".EN_WR(1'b{int(p.wr)})", '.DEPTH(16)']
    if side == 'master':
        params.append('.NWIN(8)')
    params += [f'.IW({p.iw})', f'.DW({p.dw})']
    if p.protocol == 'axil5':
        # the bridge ties AXI5-Lite TRACE / POISON to 0 (no AXI4 origin); the
        # shells check exactly that with every window's sb / poison off
        params += [".EN_TRACE(1'b1)", ".EN_POISON(1'b1)"]
    if p.protocol == 'wb4':
        params.append('.CLASSIC(0)')      # the bridge's Wishbone ports are pipelined
    out.append(f"    {mod}_{side}_stress #(")
    out.append(f"        {', '.join(params)}{extra}")
    out.append(f"    ) u_{io}{i} (")
    out.append(head)
    def net(n):
        # a narrow slave address reaches the shell's 32-bit port zero-extended
        return f"32'({p.prefix}{n})" if (n in ADDR_PINS and p.aw < 32) else f"{p.prefix}{n}"
    conns = [f"        .{io}_{stem}_{n:<9} ({net(n)})" for n in have if n in carried]
    out.append(",\n".join(conns))
    out.append("    );")
    tied = [n for n in have if n not in carried and pins[n] == dut_in]
    for n in tied:
        out.append(f"    assign {p.prefix}{n} = '0;          // not modelled by the stress shell")
    unused = [f'{p.prefix}{n}' for n in have if n not in carried and pins[n] != dut_in]
    if unused:
        out.append(f"    wire unused_{io}{i}_pins = ^{{{', '.join(unused)}}};")
    return out


def width(w: str, p: Port) -> str:
    nt = max(1, p.dw // 128)
    v = {'IW': p.iw, 'DW': p.dw, 'SW': p.dw // 8, 'UW': p.uw, 'NT': nt, 'TW': 4 * nt,
         'PW': max(1, p.dw // 64), 'AW': p.aw}.get(w)
    n = int(w) if v is None else v
    return '' if n == 1 else f'[{n - 1}:0]'


def xbar_id_width(dut: str, mon: bool) -> int:
    """The DUT bridge's slave-port ID width (its XBAR_ID_WIDTH), read from the
    generated package: a slave port's ID is always the fabric's, and the
    TOML's slave id_width only has to be at least that (bridge generator,
    _generate_slave_ports). A wider TOML id_width is the width of the IP on
    the far side; the harness connects the fabric's bits and drives the rest
    0 (no implicit truncation)."""
    import re
    name = f'{dut}_mon' if mon else dut
    pkg = AREA / 'rtl/bridges/generated' / name / f'{name}_pkg.sv'
    m = re.search(r'localparam int XBAR_ID_WIDTH\s*=\s*(\d+)', pkg.read_text())
    if not m:
        sys.exit(f'{pkg}: no XBAR_ID_WIDTH (regenerate the bridges first)')
    return int(m.group(1))


def cpuif_addr_msb(regblock: str) -> int:
    """MSB of a generated regblock's s_cpuif_addr: read from the regblock
    itself, because it grows with the register map (a hard-coded width
    silently aliases the registers past it onto the first ones)."""
    import re
    src = (AREA / 'rtl/regs/generated/rtl' / f'{regblock}.sv').read_text()
    m = re.search(r'input\s+wire\s+\[(\d+):0\]\s+s_cpuif_addr', src)
    if not m:
        sys.exit(f'{regblock}: no s_cpuif_addr port (regenerate the regblocks first)')
    return int(m.group(1))


def slverr_axil(x: str, wr: bool = True, rd: bool = True) -> str:
    """An AXI4-Lite window with nothing behind it: every access answers
    SLVERR (wr / rd: which directions). Readies come from state alone: the
    bridge's AXI4-Lite adapter may gate its VALIDs on them."""
    t = []
    if wr:
        t.append(f"""    logic r_{x}_aw, r_{x}_w, r_{x}_bv;
    assign {x}_axil_awready = !r_{x}_aw && !r_{x}_bv;
    assign {x}_axil_wready  = !r_{x}_w  && !r_{x}_bv;
    assign {x}_axil_bvalid  = r_{x}_bv;
    assign {x}_axil_bresp   = 2'b10;
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_{x}_aw <= 1'b0;
            r_{x}_w  <= 1'b0;
            r_{x}_bv <= 1'b0;
        end else begin
            if ({x}_axil_awvalid && {x}_axil_awready) r_{x}_aw <= 1'b1;
            if ({x}_axil_wvalid  && {x}_axil_wready)  r_{x}_w  <= 1'b1;
            if (r_{x}_aw && r_{x}_w) begin
                r_{x}_bv <= 1'b1;
                r_{x}_aw <= 1'b0;
                r_{x}_w  <= 1'b0;
            end else if (r_{x}_bv && {x}_axil_bready) begin
                r_{x}_bv <= 1'b0;
            end
        end
    end
    wire unused_{x}_wr = ^{{{x}_axil_awaddr, {x}_axil_awprot, {x}_axil_wdata, {x}_axil_wstrb}};
""")
    if rd:
        t.append(f"""    logic r_{x}_rv;
    assign {x}_axil_arready = !r_{x}_rv;
    assign {x}_axil_rvalid  = r_{x}_rv;
    assign {x}_axil_rresp   = 2'b10;
    assign {x}_axil_rdata   = 32'hDEAD_0000;
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn)                                  r_{x}_rv <= 1'b0;
        else if ({x}_axil_arvalid && {x}_axil_arready) r_{x}_rv <= 1'b1;
        else if ({x}_axil_rready)                      r_{x}_rv <= 1'b0;
    end
    wire unused_{x}_rd = ^{{{x}_axil_araddr, {x}_axil_arprot}};
""")
    return ''.join(t)


def gen(dut: str, ms: List[Port], ss: List[Port], variant: int, mon: bool = False) -> str:
    L: List[str] = []
    ctl_msb = cpuif_addr_msb('bstress_ctl_regs')
    has_vendor = any(p.vendor for p in ms + ss)
    vp: List[str] = []
    if has_vendor:
        vp.append('    // vendor IP control (AXI4-Lite out of the configuration bridge) and status')
        for x in EXT_WINDOWS:
            for n, wd, out in EXT_AXIL:
                rng = f'[{wd - 1}:0]' if wd > 1 else ''
                vp.append(f"    {'output' if out else 'input '} logic {rng:<7} {x}_axil_{n}")
        vp.append('    input  logic [127:0] i_ext_sts')
        for p in ms + ss:
            if not p.vendor:
                continue
            aw, w, b, ar, r = p.chans
            dut_in = {x for x, _ in aw + w + ar} | {'bready', 'rready'}
            dut_in -= {'awready', 'wready', 'arready'}
            if p in ss:     # a slave port's DUT inputs are the responses
                dut_in = {x for x, _ in p.sigs()} - dut_in
            vp.append(f'    // {p.name}: DUT {"master" if p in ms else "slave"} port, '
                      f'to vendor IP ({p.clk})')
            for n, wd in p.sigs():
                d = 'input ' if n in dut_in else 'output'
                vp.append(f'    {d} logic {width(wd, p):<7} {p.prefix}{n}')
    vendor_ports = (',\n' + ',\n'.join(vp)) if vp else ''
    a = L.append
    nm, ns = len(ms), len(ss)
    a(f"""// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Generated by: projects/fpga-systems/Genesys2/bridge-stress/bin/gen_bs_harness.py
// From:         rtl/bridges/configs/{dut}.toml
// DO NOT EDIT -- regenerate (bin/regen.sh).
//
// Module: bs_harness_{dut}
// Purpose: The bridge stress harness around {dut}: UART host link,
//          configuration bridge, control regblock, one stress master per DUT
//          master port and one stress slave per DUT slave port.
// Documentation: projects/fpga-systems/Genesys2/bridge-stress/PRD.md
//==============================================================================
// Clocks: aclk is the DUT's clock and the configuration clock; cclk is the
// clock of every port the TOML marks cdc. GO / STOP reach cclk through
// sync_pulse, the data seed (static while a run is live) through
// cdc_synchronizer, and the per-block done / error bits come back the same
// way. Each block's registers live in its own clock (bstress_*_csr).
//==============================================================================

`timescale 1ns / 1ps

module bs_harness_{dut}
    import axi_stress_pkg::*;
#(
    parameter int CLKS_PER_BIT = 868     // 100 MHz / 115200
) (
    input  logic aclk,
    input  logic aresetn,
    input  logic cclk,
    input  logic cresetn,

    input  logic i_uart_rx,
    output logic o_uart_tx,

    output logic o_all_done,
    output logic o_any_err,
    output logic o_busy{vendor_ports}
);

    localparam int NM = {nm};
    localparam int NS = {ns};
""")

    # ---------------------------------------------------------------- host
    a("""    // =========================================================================
    // Host link: UART -> AXI4-Lite -> bridge_bs_cfg -> one APB window per block
    // =========================================================================
    logic [31:0] host_axi_awaddr, host_axi_wdata, host_axi_araddr, host_axi_rdata;
    logic [2:0]  host_axi_awprot, host_axi_arprot;
    logic [3:0]  host_axi_wstrb;
    logic [1:0]  host_axi_bresp, host_axi_rresp;
    logic        host_axi_awvalid, host_axi_awready, host_axi_wvalid, host_axi_wready;
    logic        host_axi_bvalid, host_axi_bready, host_axi_arvalid, host_axi_arready;
    logic        host_axi_rvalid, host_axi_rready;

    uart_axil_bridge #(
        .AXIL_ADDR_WIDTH (32),
        .AXIL_DATA_WIDTH (32),
        .CLKS_PER_BIT    (CLKS_PER_BIT)
    ) u_uart (
        .aclk, .aresetn,
        .i_uart_rx, .o_uart_tx,
        .m_axil_awaddr(host_axi_awaddr), .m_axil_awprot(host_axi_awprot),
        .m_axil_awvalid(host_axi_awvalid), .m_axil_awready(host_axi_awready),
        .m_axil_wdata(host_axi_wdata), .m_axil_wstrb(host_axi_wstrb),
        .m_axil_wvalid(host_axi_wvalid), .m_axil_wready(host_axi_wready),
        .m_axil_bresp(host_axi_bresp), .m_axil_bvalid(host_axi_bvalid),
        .m_axil_bready(host_axi_bready),
        .m_axil_araddr(host_axi_araddr), .m_axil_arprot(host_axi_arprot),
        .m_axil_arvalid(host_axi_arvalid), .m_axil_arready(host_axi_arready),
        .m_axil_rdata(host_axi_rdata), .m_axil_rresp(host_axi_rresp),
        .m_axil_rvalid(host_axi_rvalid), .m_axil_rready(host_axi_rready)
    );
""")
    wins = ['ctl'] + [f'mst{i}' for i in range(MAX_PORTS)] + [f'slv{i}' for i in range(MAX_PORTS)]
    for w in wins:
        a(f"    logic        {w}_apb_PSEL, {w}_apb_PENABLE, {w}_apb_PWRITE, "
          f"{w}_apb_PREADY, {w}_apb_PSLVERR;")
        a(f"    logic [31:0] {w}_apb_PADDR, {w}_apb_PWDATA, {w}_apb_PRDATA;")
        a(f"    logic [3:0]  {w}_apb_PSTRB;")
        a(f"    logic [2:0]  {w}_apb_PPROT;")
    for x in (MON_WINDOWS if has_vendor else EXT_WINDOWS + MON_WINDOWS):
        for n, wd, _ in EXT_AXIL:
            rng = f'[{wd - 1}:0]' if wd > 1 else ''
            a(f"    logic {rng:<7} {x}_axil_{n};")
    a("    logic        cfg_unmapped_irq;")
    a("""
    bridge_bs_cfg u_cfg (
        .aclk, .aresetn,
        .host_axi_awaddr, .host_axi_awprot, .host_axi_awvalid, .host_axi_awready,
        .host_axi_wdata, .host_axi_wstrb, .host_axi_wvalid, .host_axi_wready,
        .host_axi_bresp, .host_axi_bvalid, .host_axi_bready,
        .host_axi_araddr, .host_axi_arprot, .host_axi_arvalid, .host_axi_arready,
        .host_axi_rdata, .host_axi_rresp, .host_axi_rvalid, .host_axi_rready,""")
    for w in wins:
        a(f"        .{w}_apb_PSEL, .{w}_apb_PADDR, .{w}_apb_PENABLE, .{w}_apb_PWRITE,")
        a(f"        .{w}_apb_PWDATA, .{w}_apb_PSTRB, .{w}_apb_PPROT,")
        a(f"        .{w}_apb_PRDATA, .{w}_apb_PREADY, .{w}_apb_PSLVERR,")
    for x in EXT_WINDOWS + MON_WINDOWS:
        a("        " + ", ".join(f".{x}_axil_{n}" for n, _, _ in EXT_AXIL) + ",")
    a("""        .unmapped_irq   (cfg_unmapped_irq),
        /* verilator lint_off PINCONNECTEMPTY */
        .unmapped_addr  (),
        .unmapped_count (),
        /* verilator lint_on PINCONNECTEMPTY */
        .unmapped_clear (1'b0)
    );
""")
    # unused windows
    used = {f'mst{i}' for i in range(nm)} | {f'slv{i}' for i in range(ns)} | {'ctl'}
    for w in wins:
        if w not in used:
            a(f"    // {w}: no block in this build -- every access answers PSLVERR")
            a(f"    assign {w}_apb_PREADY  = 1'b1;")
            a(f"    assign {w}_apb_PSLVERR = 1'b1;")
            a(f"    assign {w}_apb_PRDATA  = 32'hDEAD_0000;")
    a(f"    wire unused_cfg = ^{{cfg_unmapped_irq, " + ", ".join(
        f"{w}_apb_PSEL, {w}_apb_PADDR, {w}_apb_PENABLE, {w}_apb_PWRITE, "
        f"{w}_apb_PWDATA, {w}_apb_PSTRB, {w}_apb_PPROT" for w in wins if w not in used)
      + "};\n" if len(used) < len(wins) else "    wire unused_cfg = cfg_unmapped_irq;\n")

    if not has_vendor:
        for x in EXT_WINDOWS:
            a(f"    // {x}: no vendor IP in this build -- every access answers SLVERR")
            a(slverr_axil(x))
    if mon:
        a(f"    // {MON_DRAIN}: the error drain is read-only -- a write answers SLVERR")
        a(slverr_axil(MON_DRAIN, rd=False))
    else:
        for x in MON_WINDOWS:
            a(f"    // {x}: the DUT has no Ocelus monitors in this build -- SLVERR")
            a(slverr_axil(x))

    # ---------------------------------------------------------------- ctl
    a(f"""    // =========================================================================
    // Control regblock (aclk)
    // =========================================================================
    logic        ctl_req, ctl_req_is_wr, ctl_stall_wr, ctl_stall_rd;
    logic        ctl_rd_ack, ctl_rd_err, ctl_wr_ack, ctl_wr_err;
    logic [11:0] ctl_addr;
    logic [31:0] ctl_wr_data, ctl_wr_biten, ctl_rd_data;

    apb4_to_peakrdl #(.ADDR_WIDTH(12), .DATA_WIDTH(32), .PROT_WIDTH(3)) u_ctl_shim (
        .aclk, .aresetn, .pclk (aclk), .presetn (aresetn),
        .s_apb_PSEL (ctl_apb_PSEL), .s_apb_PENABLE (ctl_apb_PENABLE),
        .s_apb_PREADY (ctl_apb_PREADY), .s_apb_PADDR (ctl_apb_PADDR[11:0]),
        .s_apb_PWRITE (ctl_apb_PWRITE), .s_apb_PWDATA (ctl_apb_PWDATA),
        .s_apb_PSTRB (ctl_apb_PSTRB), .s_apb_PPROT (ctl_apb_PPROT),
        .s_apb_PRDATA (ctl_apb_PRDATA), .s_apb_PSLVERR (ctl_apb_PSLVERR),
        .cpuif_req (ctl_req), .cpuif_req_is_wr (ctl_req_is_wr), .cpuif_addr (ctl_addr),
        .cpuif_wr_data (ctl_wr_data), .cpuif_wr_biten (ctl_wr_biten),
        .cpuif_req_stall_wr (ctl_stall_wr), .cpuif_req_stall_rd (ctl_stall_rd),
        .cpuif_rd_ack (ctl_rd_ack), .cpuif_rd_err (ctl_rd_err), .cpuif_rd_data (ctl_rd_data),
        .cpuif_wr_ack (ctl_wr_ack), .cpuif_wr_err (ctl_wr_err)
    );

    bstress_ctl_regs_pkg::bstress_ctl_regs__in_t  ctl_hi;
    bstress_ctl_regs_pkg::bstress_ctl_regs__out_t ctl_ho;

    bstress_ctl_regs u_ctl (
        .clk (aclk), .rst (~aresetn),
        .s_cpuif_req (ctl_req), .s_cpuif_req_is_wr (ctl_req_is_wr),
        .s_cpuif_addr (ctl_addr[{ctl_msb}:0]),
        .s_cpuif_wr_data (ctl_wr_data), .s_cpuif_wr_biten (ctl_wr_biten),
        .s_cpuif_req_stall_wr (ctl_stall_wr), .s_cpuif_req_stall_rd (ctl_stall_rd),
        .s_cpuif_rd_ack (ctl_rd_ack), .s_cpuif_rd_err (ctl_rd_err),
        .s_cpuif_rd_data (ctl_rd_data),
        .s_cpuif_wr_ack (ctl_wr_ack), .s_cpuif_wr_err (ctl_wr_err),
        .hwif_in (ctl_hi), .hwif_out (ctl_ho)
    );
    wire unused_ctl = ^{{ctl_addr[11:{ctl_msb + 1}], ctl_apb_PADDR[31:12]}};

    // GO / STOP / seed in each domain. GO and STOP are the RISING EDGES of
    // their singlepulse fields: apb4_to_peakrdl holds the cpuif request until
    // the ack, so the regblock takes each write twice and a singlepulse is two
    // cycles wide -- which toggles sync_pulse twice, and cclk then sees two
    // GOs or none. The edge is one cycle whatever the field's width.
    logic        go_a, stop_a, go_c, stop_c, r_go_q, r_stop_q;
    logic [31:0] seed_a, seed_c;
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_go_q   <= 1'b0;
            r_stop_q <= 1'b0;
        end else begin
            r_go_q   <= ctl_ho.CTRL.GO.value;
            r_stop_q <= ctl_ho.CTRL.STOP.value;
        end
    end
    assign go_a   = ctl_ho.CTRL.GO.value && !r_go_q;
    assign stop_a = ctl_ho.CTRL.STOP.value && !r_stop_q;
    assign seed_a = ctl_ho.HASH_SEED.VALUE.value;

    sync_pulse u_go_c (
        .i_src_clk (aclk), .i_src_rst_n (aresetn), .i_pulse (go_a),
        .i_dst_clk (cclk), .i_dst_rst_n (cresetn), .o_pulse (go_c)
    );
    sync_pulse u_stop_c (
        .i_src_clk (aclk), .i_src_rst_n (aresetn), .i_pulse (stop_a),
        .i_dst_clk (cclk), .i_dst_rst_n (cresetn), .o_pulse (stop_c)
    );
    cdc_synchronizer #(.WIDTH(32)) u_seed_c (
        .clk (cclk), .rst_n (cresetn), .async_in (seed_a), .sync_out (seed_c)
    );

    // Per-block done / error, raw in the block's domain and synchronized to aclk
    logic [NM-1:0] mst_done_raw, mst_err_raw, mst_done, mst_err;
    logic [NS-1:0] slv_err_raw, slv_err;
""")

    # ---------------------------------------------------------------- masters
    for i, p in enumerate(ms):
        go, stop, seed = ('go_c', 'stop_c', 'seed_c') if p.cdc else ('go_a', 'stop_a', 'seed_a')
        if p.vendor:
            a(f"""    // Master {i}: {p.name} -- vendor IP on harness pins; done and error-free here
    assign mst_done_raw[{i}] = 1'b1;
    assign mst_err_raw[{i}]  = 1'b0;
""")
            continue
        a(f"""    // =========================================================================
    // Master {i}: {p.name} ({p.protocol}, {p.channels}, {p.dw}-bit, ID {p.iw}, {p.clk})
    // =========================================================================
    stress_mdir_cfg_t m{i}_cfg_rd, m{i}_cfg_wr;
    stress_mdir_sts_t m{i}_sts_rd, m{i}_sts_wr;
    stress_win_t      m{i}_win [8];
""")
        for n, w in p.sigs():
            a(f"    logic {width(w, p):<8} {p.prefix}{n};")
        a(f"""
    bstress_mst_csr #(
        .INDEX({i}), .PROTOCOL({PROTO_CODE[p.protocol]}), .DW({p.dw}), .IW({p.iw}),
        .DEPTH(16), .NWIN(8), .HAS_RD(1'b{int(p.rd)}), .HAS_WR(1'b{int(p.wr)})
    ) u_m{i}_csr (
        .aclk ({p.clk}), .aresetn ({p.rst}), .pclk (aclk), .presetn (aresetn),
        .s_apb_PSEL (mst{i}_apb_PSEL), .s_apb_PENABLE (mst{i}_apb_PENABLE),
        .s_apb_PREADY (mst{i}_apb_PREADY), .s_apb_PADDR (mst{i}_apb_PADDR[11:0]),
        .s_apb_PWRITE (mst{i}_apb_PWRITE), .s_apb_PWDATA (mst{i}_apb_PWDATA),
        .s_apb_PSTRB (mst{i}_apb_PSTRB), .s_apb_PPROT (mst{i}_apb_PPROT),
        .s_apb_PRDATA (mst{i}_apb_PRDATA), .s_apb_PSLVERR (mst{i}_apb_PSLVERR),
        .cfg_rd (m{i}_cfg_rd), .cfg_wr (m{i}_cfg_wr), .cfg_win (m{i}_win),
        .sts_rd (m{i}_sts_rd), .sts_wr (m{i}_sts_wr)
    );
    wire unused_m{i}_paddr = ^mst{i}_apb_PADDR[31:12];
""")
        head = (f"        .aclk ({p.clk}), .aresetn ({p.rst}), .go ({go}), .stop ({stop}),\n"
                f"        .cfg_rd (m{i}_cfg_rd), .cfg_wr (m{i}_cfg_wr), .cfg_win (m{i}_win),\n"
                f"        .cfg_hash_seed ({seed}),\n"
                f"        .sts_rd (m{i}_sts_rd), .sts_wr (m{i}_sts_wr),")
        if p.single:
            for ln in single_shell(p, 'master', i, head):
                a(ln)
            a(f"    assign mst_done_raw[{i}] = m{i}_sts_rd.done && m{i}_sts_wr.done;")
            a(f"    assign mst_err_raw[{i}]  = (|m{i}_sts_rd.err_mask) || (|m{i}_sts_wr.err_mask);\n")
            continue
        a(f"""    {p.protocol}_master_stress #(
        .EN_RD(1'b{int(p.rd)}), .EN_WR(1'b{int(p.wr)}), .DEPTH(16), .NWIN(8),
        .IW({p.iw}), .DW({p.dw}), .UW({p.uw}){p.axi5_params()}
    ) u_m{i} (
{head}""")
        conns = []
        have = {n for n, _ in p.sigs()}
        aw, w, b, ar, r = p.chans
        m_inputs = {x for x, _ in b + r} | {'awready', 'wready', 'arready'}
        m_inputs -= {'bready', 'rready'}
        for n, _ in p.all_sigs():
            tie = "'0" if n in m_inputs else ''
            conns.append(f"        .m_axi_{n:<9} ({p.prefix + n if n in have else tie})")
        a("        /* verilator lint_off PINCONNECTEMPTY */")
        a(",\n".join(conns))
        a("        /* verilator lint_on PINCONNECTEMPTY */")
        a("    );")
        a(f"    assign mst_done_raw[{i}] = m{i}_sts_rd.done && m{i}_sts_wr.done;")
        a(f"    assign mst_err_raw[{i}]  = (|m{i}_sts_rd.err_mask) || (|m{i}_sts_wr.err_mask);\n")

    # ---------------------------------------------------------------- slaves
    # The fabric ID a slave sees is {master index, master-local ID}; an AXI5
    # slave finds which master a request came from in that index field.
    spec = [SimpleNamespace(id_width=m.iw, max_outstanding=m.max_outstanding,
                            axi5_features=m.features, channels=m.channels) for m in ms]
    src_lsb, src_w = fabric_local_id_width(spec), id_prefix_width(spec)
    for i, p in enumerate(ss):
        go, seed = ('go_c', 'seed_c') if p.cdc else ('go_a', 'seed_a')
        if p.vendor:
            a(f"""    // Slave {i}: {p.name} -- vendor IP on harness pins
    //          window 0x{p.base:08X} + 0x{p.size:X}
    assign slv_err_raw[{i}] = 1'b0;
""")
            continue
        src_params = (f", .SRC_LSB({src_lsb}), .SRC_W({src_w})"
                      if p.protocol in ('axi5', 'axil5') else '')
        a(f"""    // =========================================================================
    // Slave {i}: {p.name} ({p.protocol}, {p.channels}, {p.dw}-bit, ID {p.iw}, {p.clk})
    //          window 0x{p.base:08X} + 0x{p.size:X}
    // =========================================================================
    stress_sdir_cfg_t s{i}_cfg_rd, s{i}_cfg_wr;
    stress_sdir_sts_t s{i}_sts_rd, s{i}_sts_wr;
""")
        for n, w in p.sigs():
            a(f"    logic {width(w, p):<8} {p.prefix}{n};")
        a(f"""
    bstress_slv_csr #(
        .INDEX({i}), .PROTOCOL({PROTO_CODE[p.protocol]}), .DW({p.dw}), .IW({p.iw}),
        .DEPTH(16), .HAS_RD(1'b{int(p.rd)}), .HAS_WR(1'b{int(p.wr)})
    ) u_s{i}_csr (
        .aclk ({p.clk}), .aresetn ({p.rst}), .pclk (aclk), .presetn (aresetn),
        .s_apb_PSEL (slv{i}_apb_PSEL), .s_apb_PENABLE (slv{i}_apb_PENABLE),
        .s_apb_PREADY (slv{i}_apb_PREADY), .s_apb_PADDR (slv{i}_apb_PADDR[11:0]),
        .s_apb_PWRITE (slv{i}_apb_PWRITE), .s_apb_PWDATA (slv{i}_apb_PWDATA),
        .s_apb_PSTRB (slv{i}_apb_PSTRB), .s_apb_PPROT (slv{i}_apb_PPROT),
        .s_apb_PRDATA (slv{i}_apb_PRDATA), .s_apb_PSLVERR (slv{i}_apb_PSLVERR),
        .cfg_rd (s{i}_cfg_rd), .cfg_wr (s{i}_cfg_wr),
        .sts_rd (s{i}_sts_rd), .sts_wr (s{i}_sts_wr)
    );
    wire unused_s{i}_paddr = ^slv{i}_apb_PADDR[31:12];
""")
        head = (f"        .aclk ({p.clk}), .aresetn ({p.rst}), .clear ({go}),\n"
                f"        .cfg_rd (s{i}_cfg_rd), .cfg_wr (s{i}_cfg_wr), .cfg_hash_seed ({seed}),\n"
                f"        .sts_rd (s{i}_sts_rd), .sts_wr (s{i}_sts_wr),")
        if p.single:
            for ln in single_shell(p, 'slave', i, head, src_params):
                a(ln)
            a(f"    assign slv_err_raw[{i}] = (|s{i}_sts_rd.err_mask) || (|s{i}_sts_wr.err_mask);\n")
            continue
        a(f"""    {p.protocol}_slave_stress #(
        .EN_RD(1'b{int(p.rd)}), .EN_WR(1'b{int(p.wr)}), .DEPTH(16),
        .IW({p.iw}), .DW({p.dw}), .UW({p.uw}){p.axi5_params()}{src_params}
    ) u_s{i} (
{head}""")
        conns = []
        have = {n for n, _ in p.sigs()}
        aw, w, _, ar, _ = p.chans
        for n, _ in p.all_sigs():
            tie = ''
            if n not in have:
                # inputs of a missing direction idle; outputs float
                inputs = {x for x, _ in aw + w + ar} | {'bready', 'rready'}
                tie = "'0" if n in inputs else ''
            conns.append(f"        .s_axi_{n:<9} ({p.prefix + n if n in have else tie})")
        a("        /* verilator lint_off PINCONNECTEMPTY */")
        a(",\n".join(conns))
        a("        /* verilator lint_on PINCONNECTEMPTY */")
        a("    );")
        a(f"    assign slv_err_raw[{i}] = (|s{i}_sts_rd.err_mask) || (|s{i}_sts_wr.err_mask);\n")

    # ---------------------------------------------------------------- DUT
    a(f"""    // =========================================================================
    // Device under test
    // =========================================================================
    logic        dut_unmapped_irq;
    logic [31:0] dut_unmapped_addr;
    logic [7:0]  dut_unmapped_count;
    logic        dut_mon_irq;
""")
    if mon:
        a(mon_glue())
    else:
        a("    assign dut_mon_irq = 1'b0;      // no Ocelus monitors in this build\n")
    a(f"""    {dut}{'_mon' if mon else ''} u_dut (
        .aclk, .aresetn,""")
    for p in ms + ss:
        if p.cdc:
            a(f"        .{p.name}_aclk (cclk), .{p.name}_aresetn (cresetn),")
    fw = xbar_id_width(dut, mon)
    wide = []                    # (net, msb) of slave ID outputs wider than the fabric's
    for p in ms + ss:
        for n, _ in p.sigs():
            if p in ss and p.iw > fw and n in ('awid', 'wid', 'arid', 'bid', 'rid'):
                a(f"        .{p.prefix}{n} ({p.prefix}{n}[{fw - 1}:0]),")
                if n in ('awid', 'wid', 'arid'):
                    wide.append((f'{p.prefix}{n}', p.iw - 1))
            else:
                a(f"        .{p.prefix}{n},")
    if mon:
        a(mon_ports())
    a("""        .unmapped_irq   (dut_unmapped_irq),
        .unmapped_addr  (dut_unmapped_addr),
        .unmapped_count (dut_unmapped_count),
        .unmapped_clear (ctl_ho.CTRL.UNMAPPED_CLEAR.value)
    );
""")
    if wide:
        a(f"    // slave IDs wider than the fabric's ({fw} bits): the high bits are 0 out, and")
        a("    // the slave echoes them on B / R, so they are 0 back too")
        for net, msb in wide:
            a(f"    assign {net}[{msb}:{fw}] = '0;")
        unused = [f"{p.prefix}{n}[{p.iw - 1}:{fw}]" for p in ss if p.iw > fw for n in ('bid', 'rid')
                  if n in dict(p.sigs())]
        if unused:
            a(f"    wire unused_wide_ids = ^{{{', '.join(unused)}}};")
        a("")

    # ---------------------------------------------------------------- roll-up
    cm = [i for i, p in enumerate(ms) if p.cdc]
    cs = [i for i, p in enumerate(ss) if p.cdc]
    a("    // ---- roll-up into aclk ----------------------------------------------------")
    for i, p in enumerate(ms):
        if p.cdc:
            a(f"    cdc_synchronizer #(.WIDTH(2)) u_m{i}_sync (.clk (aclk), .rst_n (aresetn),\n"
              f"        .async_in ({{mst_done_raw[{i}], mst_err_raw[{i}]}}), "
              f".sync_out ({{mst_done[{i}], mst_err[{i}]}}));")
        else:
            a(f"    assign mst_done[{i}] = mst_done_raw[{i}];")
            a(f"    assign mst_err[{i}]  = mst_err_raw[{i}];")
    for i, p in enumerate(ss):
        if p.cdc:
            a(f"    cdc_synchronizer #(.WIDTH(1)) u_s{i}_sync (.clk (aclk), .rst_n (aresetn),\n"
              f"        .async_in (slv_err_raw[{i}]), .sync_out (slv_err[{i}]));")
        else:
            a(f"    assign slv_err[{i}] = slv_err_raw[{i}];")
    a("    logic [127:0] w_ext_sts;      // vendor IP status (EXT_STS0..3)")
    a(f"    assign w_ext_sts = {'i_ext_sts' if has_vendor else "'0"};")
    a(f"""
    // Run timer: GO to ALL_DONE. ALL_DONE is ignored for the first 16 cycles
    // after GO -- the blocks' done flags, and the synchronized ones longer
    // still, show the previous run until GO reaches them.
    logic        r_busy;
    logic [4:0]  r_guard;
    logic [7:0]  r_go_count;
    logic [31:0] r_timer, r_cycles;
    logic        w_all_done, w_any_err;
    assign w_all_done = &mst_done;
    assign w_any_err  = (|mst_err) || (|slv_err);

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_busy   <= 1'b0;
            r_guard  <= '0;
            r_timer  <= '0;
            r_cycles <= '0;
            r_go_count <= '0;
        end else begin
            r_cycles <= r_cycles + 32'd1;
            if (go_a) r_go_count <= r_go_count + 8'd1;
            if (go_a) begin
                r_busy  <= 1'b1;
                r_guard <= 5'd16;
                r_timer <= '0;
            end else if (r_busy) begin
                r_timer <= r_timer + 32'd1;
                if (r_guard != '0)  r_guard <= r_guard - 5'd1;
                else if (w_all_done) r_busy <= 1'b0;
            end
        end
    end

    logic r_cresetn_a;
    cdc_synchronizer #(.WIDTH(1)) u_crst_sync (.clk (aclk), .rst_n (aresetn),
        .async_in (cresetn), .sync_out (r_cresetn_a));

    always_comb begin
        ctl_hi.ID.NUM_MASTERS.next = 4'(NM);
        ctl_hi.ID.NUM_SLAVES.next  = 4'(NS);
        ctl_hi.ID.VARIANT.next     = 8'd{variant};
        ctl_hi.ID.MAGIC.next       = 16'h4253;
        ctl_hi.STATUS.ALL_DONE.next  = w_all_done && !r_busy;
        ctl_hi.STATUS.ANY_ERR.next   = w_any_err;
        ctl_hi.STATUS.CLOCKS_OK.next = r_cresetn_a;
        ctl_hi.STATUS.UNMAPPED.next  = dut_unmapped_irq;
        ctl_hi.STATUS.MON_IRQ.next   = dut_mon_irq;
        ctl_hi.STATUS.HAS_MON.next   = 1'b{int(mon)};
        ctl_hi.STATUS.MST_DONE.next  = 8'(mst_done);
        ctl_hi.STATUS.MST_ERR.next   = 8'(mst_err);
        ctl_hi.STATUS.SLV_ERR.next   = 8'(slv_err);
        ctl_hi.TIMER.VALUE.next          = r_timer;
        ctl_hi.UNMAPPED_COUNT.COUNT.next = dut_unmapped_count;
        ctl_hi.UNMAPPED_ADDR.VALUE.next  = dut_unmapped_addr;
        ctl_hi.CYCLES.VALUE.next         = r_cycles;
        ctl_hi.GO_COUNT.VALUE.next       = r_go_count;
        ctl_hi.EXT_STS0.VALUE.next       = w_ext_sts[31:0];
        ctl_hi.EXT_STS1.VALUE.next       = w_ext_sts[63:32];
        ctl_hi.EXT_STS2.VALUE.next       = w_ext_sts[95:64];
        ctl_hi.EXT_STS3.VALUE.next       = w_ext_sts[127:96];
    end

    assign o_all_done = w_all_done && !r_busy;
    assign o_any_err  = w_any_err;
    assign o_busy     = r_busy;

endmodule : bs_harness_{dut}
""")
    return '\n'.join(L)


def mon_glue() -> str:
    """Nets between the configuration bridge and the DUT's Ocelus ports, and
    the error-window RAM on the group's write master (write-only group)."""
    c, d = MON_CFG, MON_DRAIN
    return f"""    // Ocelus (mon variant): cfg regblock on {c}, error window on {d}, both
    // addressed by the offset inside their 64 KB window. The write-only group
    // (monbus_axil4_group_1wr) has no drain port: error records are WRITTEN
    // through its master into a RAM here, the host reads them back through
    // {d} (same window, now memory-backed), and MON_ERR_REC_COUNT in the cfg
    // regblock says how many have landed.
    logic [31:0] w_mon_cfg_awaddr, w_mon_cfg_araddr;
    assign w_mon_cfg_awaddr   = {{16'd0, {c}_axil_awaddr[15:0]}};
    assign w_mon_cfg_araddr   = {{16'd0, {c}_axil_araddr[15:0]}};

    // Monitor record RAM: 8 KB, 64-bit words. The error window is
    // 0x0000..0x0FEF (170 whole 24-byte records; the group wraps past the
    // last whole record), the trace window 0x1000..0x1FFF (unused while the
    // host err-selects every AXI class, but a legal window so the trace
    // writer never stalls). Write side: the group's single-beat AXIL master
    // (one AW/W pair per beat). Read side: 32-bit reads on {d}, low word
    // first -- the host's old drain addressing, record k at offset k*24.
    logic [63:0] mon_ram [0:1023];
    logic [15:0] dut_err_rec_count;
    logic        m_mon_axil_awvalid, m_mon_axil_wvalid, m_mon_axil_bready, r_mon_bv;
    logic [31:0] m_mon_axil_awaddr;
    logic [2:0]  m_mon_axil_awprot;
    logic [63:0] m_mon_axil_wdata;
    logic [7:0]  m_mon_axil_wstrb;
    logic        r_mon_aw, r_mon_w;
    logic [31:0] r_mon_awaddr;
    logic [63:0] r_mon_wdata;
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_mon_aw <= 1'b0;
            r_mon_w  <= 1'b0;
            r_mon_bv <= 1'b0;
            r_mon_awaddr <= '0;
            r_mon_wdata  <= '0;
        end else begin
            // AXIL allows AW and W in either order; the RAM write happens
            // once both have arrived (single outstanding, like the old sink).
            if (m_mon_axil_awvalid && !r_mon_aw && !r_mon_bv) begin
                r_mon_aw     <= 1'b1;
                r_mon_awaddr <= m_mon_axil_awaddr;
            end
            if (m_mon_axil_wvalid && !r_mon_w && !r_mon_bv) begin
                r_mon_w     <= 1'b1;
                r_mon_wdata <= m_mon_axil_wdata;
            end
            if (r_mon_aw && r_mon_w) begin
                mon_ram[r_mon_awaddr[12:3]] <= r_mon_wdata;
                r_mon_bv <= 1'b1;
                r_mon_aw <= 1'b0;
                r_mon_w  <= 1'b0;
            end else if (r_mon_bv && m_mon_axil_bready) begin
                r_mon_bv <= 1'b0;
            end
        end
    end

    // {d} read port: one 32-bit word per beat, synchronous read so the RAM
    // infers block RAM on the board. Writes stay SLVERR (read-only window).
    logic        r_{d}_rv;
    logic [31:0] r_{d}_rdata;
    assign {d}_axil_arready = !r_{d}_rv;
    assign {d}_axil_rvalid  = r_{d}_rv;
    assign {d}_axil_rresp   = 2'b00;
    assign {d}_axil_rdata   = r_{d}_rdata;
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_{d}_rv    <= 1'b0;
            r_{d}_rdata <= '0;
        end else begin
            if ({d}_axil_arvalid && {d}_axil_arready) begin
                r_{d}_rv    <= 1'b1;
                r_{d}_rdata <= {d}_axil_araddr[2]
                               ? mon_ram[{d}_axil_araddr[12:3]][63:32]
                               : mon_ram[{d}_axil_araddr[12:3]][31:0];
            end else if ({d}_axil_rready) begin
                r_{d}_rv <= 1'b0;
            end
        end
    end
    wire unused_mon = ^{{m_mon_axil_awaddr[31:13], m_mon_axil_awaddr[2:0],
                        m_mon_axil_awprot, m_mon_axil_wstrb,
                        {c}_axil_awaddr[31:16], {c}_axil_araddr[31:16],
                        {d}_axil_araddr[31:13], dut_err_rec_count}};
"""


def mon_ports() -> str:
    """The DUT's Ocelus port connections (mon variant)."""
    c, d = MON_CFG, MON_DRAIN
    return f"""        // Ocelus: cfg regblock ({c}), error window RAM ({d}, in-harness), IRQ
        .s_cfg_axil_awvalid ({c}_axil_awvalid), .s_cfg_axil_awready ({c}_axil_awready),
        .s_cfg_axil_awaddr  (w_mon_cfg_awaddr), .s_cfg_axil_awprot  ({c}_axil_awprot),
        .s_cfg_axil_wvalid  ({c}_axil_wvalid),  .s_cfg_axil_wready  ({c}_axil_wready),
        .s_cfg_axil_wdata   ({c}_axil_wdata),   .s_cfg_axil_wstrb   ({c}_axil_wstrb),
        .s_cfg_axil_bvalid  ({c}_axil_bvalid),  .s_cfg_axil_bready  ({c}_axil_bready),
        .s_cfg_axil_bresp   ({c}_axil_bresp),
        .s_cfg_axil_arvalid ({c}_axil_arvalid), .s_cfg_axil_arready ({c}_axil_arready),
        .s_cfg_axil_araddr  (w_mon_cfg_araddr), .s_cfg_axil_arprot  ({c}_axil_arprot),
        .s_cfg_axil_rvalid  ({c}_axil_rvalid),  .s_cfg_axil_rready  ({c}_axil_rready),
        .s_cfg_axil_rdata   ({c}_axil_rdata),   .s_cfg_axil_rresp   ({c}_axil_rresp),
        .m_mon_axil_awvalid, .m_mon_axil_awready (!r_mon_aw && !r_mon_bv),
        .m_mon_axil_awaddr,  .m_mon_axil_awprot,
        .m_mon_axil_wvalid,  .m_mon_axil_wready  (!r_mon_w && !r_mon_bv),
        .m_mon_axil_wdata,   .m_mon_axil_wstrb,
        .m_mon_axil_bvalid  (r_mon_bv), .m_mon_axil_bready, .m_mon_axil_bresp (2'b00),
        .mon_irq_out        (dut_mon_irq),
        .mon_err_rec_count  (dut_err_rec_count),"""


def filelist(dut: str, rel: str, ms: List[Port], ss: List[Port], mon: bool = False) -> str:
    shells = ''.join(f'-f $REPO_ROOT/rtl/amba/filelists/{mod}_{side}_stress.f\n'
                     for side, ports in (('master', ms), ('slave', ss))
                     for mod in sorted({SHELL[p.protocol][0] if p.single else p.protocol
                                        for p in ports}))
    return f"""# Generated by bin/gen_bs_harness.py -- DO NOT EDIT
# Compile closure of bs_harness_{dut}.
+incdir+$REPO_ROOT/rtl/amba/includes
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
{shells}-f $REPO_ROOT/rtl/cdc/filelists/sync_pulse.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_synchronizer.f
-f $CONVERTERS_ROOT/rtl/filelists/uart_axil_bridge.f
-f $CONVERTERS_ROOT/rtl/filelists/apb4_to_peakrdl.f
-f $REPO_ROOT/{rel}/rtl/filelists/bstress_regs.f
-f $REPO_ROOT/{rel}/rtl/bridges/filelists/bridge_bs_cfg.f
-f $REPO_ROOT/{rel}/rtl/bridges/filelists/{dut}{'_mon' if mon else ''}.f
$REPO_ROOT/{rel}/rtl/bstress_mst_csr.sv
$REPO_ROOT/{rel}/rtl/bstress_slv_csr.sv
$REPO_ROOT/{rel}/rtl/generated/bs_harness_{dut}/bs_harness_{dut}.sv
"""


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('toml', type=Path)
    ap.add_argument('--variant', type=int, default=1, help='ID.VARIANT value')
    args = ap.parse_args()
    dut, ms, ss = load(args.toml)
    mon = has_mon(args.toml)
    out = AREA / 'rtl' / 'generated' / f'bs_harness_{dut}'
    out.mkdir(parents=True, exist_ok=True)
    (out / f'bs_harness_{dut}.sv').write_text(gen(dut, ms, ss, args.variant, mon))
    fl = AREA / 'rtl' / 'generated' / 'filelists'
    fl.mkdir(parents=True, exist_ok=True)
    repo = next(p for p in AREA.parents if (p / '.git').exists())
    (fl / f'bs_harness_{dut}.f').write_text(filelist(dut, str(AREA.relative_to(repo)), ms, ss, mon))
    print(f'[gen_bs_harness] {out}/bs_harness_{dut}.sv  ({len(ms)} masters, {len(ss)} slaves'
          f'{", Ocelus" if mon else ""})')
    return 0


if __name__ == '__main__':
    sys.exit(main())
