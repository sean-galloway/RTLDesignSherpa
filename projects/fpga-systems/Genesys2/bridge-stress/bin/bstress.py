# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Bridge stress model: the host library, shared by the board and the sim.

Everything a run needs is derived from the DUT bridge's TOML (the same file
the harness was generated from), and the bitstream is checked against it
before anything is programmed: a stress master or slave whose identity
register disagrees with the TOML stops the run.

    h = StressHarness(bridge, load_build(toml))
    h.identify()
    res = h.run(PROFILES['chaos'], seed=7, txns=2000)
    ok, why = h.verdict(res)

`bridge` is anything with read(addr) -> int and write(addr, value): the
board's UARTAxiBridge on a serial port, or the same class on the cocotb
UART channel in simulation (dv/tbclasses/bs_harness_tb.py).

Window plan, per master (8 windows):
  - one OKAY window per connected slave: the lower half of its range
  - one DECERR window in an address hole no slave owns
  - SLVERR windows (the profile's `errors`): the next quarter of a slave's
    range, which that slave is told to answer SLVERR -- as many as fit

AXI5 (bridge TASK-019 phase 2b): a slave is told which masters' requests
carry sideband natively (sb_native; its SB.SRC bitmap, by the fabric's
master index) and expects 0 from the rest. An IDUNQ master marks eligible
bursts unique; its port regenerates BIDUNQ / RIDUNQ, and each IDUNQ slave
checks the rule on the IDs it sees. An atomic master turns 1 write burst in
2^atom_lg2 on an atomic path (both ends enable atomic; the DECERR hole too,
which answers DECERR on B and R) into a one-beat atomic on an ID with the MSB
set, so its read and write IDs are kept below the MSB. The bridge holds at
most 8 read-return atomics in flight per slave port (bridge TASK-020) and
stalls the ninth; that only slows the run. A trace-capable master port echoes
the request's TRACE on BTRACE / RTRACE at the bridge boundary whatever the
slave (bridge BUG-010), so every window of such a master, the DECERR hole
included, expects the echo (window SB). A poison path (both ends enable
poison) poisons 1 beat in 2^poison_lg2 in both directions.

Vendor ports (the TOML's [harness] vendor, build-xil): no stress block and no
registers. A vendor slave is a real memory, so every stress master addresses
it as a mem window (axi_stress_pkg f_maddr): tag MEM_TAG, hashed modulo
2^MEM_LG2, its lowest 2^MEM_LG2 bytes at most. Each run starts with a fill
GO (one stress master sweeps each memory) so the image is known before the
run's GO reads it. Vendor masters are driven by bstress_xil.
"""
from __future__ import annotations

import os
import sys
import time
import tomllib
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Callable, Dict, List, Optional, Tuple

AREA = Path(__file__).resolve().parent.parent


def _repo_root() -> Path:
    env = os.environ.get('REPO_ROOT')
    if env and (Path(env) / 'projects/fpga-systems/bin/uart_link.py').is_file():
        return Path(env)
    for p in AREA.parents:
        if (p / 'projects/fpga-systems/bin/uart_link.py').is_file():
            return p
    raise RuntimeError('repo root not found (no projects/fpga-systems/bin/uart_link.py above)')


REPO = _repo_root()
for _p in (REPO / 'bin', REPO / 'projects/fpga-systems/bin'):
    if str(_p) not in sys.path:
        sys.path.insert(0, str(_p))

from TBClasses.harness.device import Device  # noqa: E402
from TBClasses.amba import axi_stress_model as M  # noqa: E402

REGMAPS = AREA / 'rtl/regs/generated'
CTL_BASE = 0x0000_0000
MST_BASE = 0x0001_0000
SLV_BASE = 0x0002_0000
WIN_STRIDE = 0x1000
NWIN = 8
PROTO_CODE = {'axi4': 0, 'axi3': 1, 'axi5': 2, 'axil': 3, 'axil5': 4,
              'apb': 5, 'apb5': 6, 'wb4': 7}
TAG0 = 0x10                         # slave i's tag = TAG0 + i
MEM_TAG = 0x6D                      # every mem window: one image across memories
MEM_LG2 = 20                        # mem windows hash modulo 1 MB (cfg mem_lg2)


# =============================================================================
# The build, from its TOML
# =============================================================================

@dataclass(frozen=True)
class Port:
    index: int
    name: str
    protocol: str
    channels: str
    dw: int
    iw: int
    cdc: bool
    base: int = 0
    size: int = 0
    ooo: bool = False
    features: Tuple[str, ...] = ()           # axi5_features
    vendor: bool = False                     # [harness] vendor: third-party IP

    @property
    def rd(self) -> bool:
        return self.channels in ('rd', 'rw')

    @property
    def wr(self) -> bool:
        return self.channels in ('wr', 'rw')

    @property
    def size_lg2(self) -> int:
        return self.size.bit_length() - 1

    @property
    def mem_lg2(self) -> int:
        """A vendor slave's mem window: its lowest 2^n bytes."""
        return min(self.size_lg2, MEM_LG2)


@dataclass(frozen=True)
class Build:
    name: str
    masters: Tuple[Port, ...]
    slaves: Tuple[Port, ...]
    conn: Dict[str, Tuple[str, ...]]          # master name -> slave names

    def slaves_of(self, m: Port) -> List[Port]:
        return [s for s in self.slaves if s.name in self.conn[m.name]]

    def masters_of(self, s: Port) -> List[Port]:
        return [m for m in self.masters if s.name in self.conn[m.name]]

    @property
    def stress_masters(self) -> Tuple[Port, ...]:
        return tuple(m for m in self.masters if not m.vendor)

    @property
    def stress_slaves(self) -> Tuple[Port, ...]:
        return tuple(s for s in self.slaves if not s.vendor)

    @property
    def memories(self) -> Tuple[Port, ...]:
        return tuple(s for s in self.slaves if s.vendor)


def load_build(toml: Path) -> Build:
    toml = Path(toml)
    doc = tomllib.loads(toml.read_text())
    cfg = doc['bridge']
    vendor = set(doc.get('harness', {}).get('vendor', []))
    ms = tuple(Port(i, m['name'], m.get('protocol', 'axi4'), m.get('channels', 'rw'),
                    m['data_width'], m.get('id_width', 0), bool(m.get('cdc', False)),
                    features=tuple(m.get('axi5_features', ())), vendor=m['name'] in vendor)
               for i, m in enumerate(cfg['masters']))
    ss = tuple(Port(i, s['name'], s.get('protocol', 'axi4'), s.get('channels', 'rw'),
                    s['data_width'], s.get('id_width', 0), bool(s.get('cdc', False)),
                    int(s['base_addr'], 0), int(s['addr_range'], 0),
                    bool(s.get('enable_ooo', False)),
                    features=tuple(s.get('axi5_features', ())), vendor=s['name'] in vendor)
               for i, s in enumerate(cfg['slaves']))
    conn_file = toml.with_name(f"{cfg['name']}_connectivity.csv")
    conn: Dict[str, Tuple[str, ...]] = {}
    lines = [l.strip() for l in conn_file.read_text().splitlines() if l.strip()]
    cols = lines[0].split(',')[1:]
    for l in lines[1:]:
        row = l.split(',')
        conn[row[0]] = tuple(c for c, v in zip(cols, row[1:]) if v.strip() == '1')
    build = Build(cfg['name'], ms, ss, conn)
    for m in ms:
        for sl in build.slaves_of(m):
            a, b = sb_feats(m), sb_feats(sl)
            if a and b and a != b and m.dw == sl.dw:
                raise ValueError(f'{m.name} -> {sl.name}: AXI5 sideband features differ '
                                 f'({sorted(a)} vs {sorted(b)}); the stress model checks a '
                                 f'path as all-or-nothing')
    return build


SB_FEATURES = frozenset(('nsaid', 'trace', 'mpam', 'mecid'))


def sb_feats(p: Port) -> frozenset:
    return frozenset(p.features) & SB_FEATURES if p.protocol == 'axi5' else frozenset()


def sb_native(m: Port, s: Port) -> bool:
    """The bridge carries the AXI5 request / response sideband from m to s
    unchanged: both ends AXI5 with the same sideband features, one width (a
    width converter drops sideband) and neither end across a clock (the CDC
    crossing carries the AXI4 set). Anywhere else the far end sees 0."""
    return (bool(sb_feats(m)) and sb_feats(m) == sb_feats(s) and m.dw == s.dw
            and not m.cdc and not s.cdc)


def sweep_bursts(m: Port, s: Port) -> int:
    """Bursts m's fill takes to sweep memory s once. A fill burst is the
    master's longest (its shell's LEN_MASK): 16 beats on an AXI3 port, 256
    otherwise -- so an AXI3 sweep takes 16x the bursts of an AXI4 one."""
    return M.fill_bursts(s.mem_lg2, (m.dw // 8).bit_length() - 1,
                         len_mask=0x0F if m.protocol == 'axi3' else 0xFF)


def is_atomic(p: Port) -> bool:
    return p.protocol == 'axi5' and 'atomic' in p.features


def atomic_path(m: Port, s: Port) -> bool:
    """Both ends enable atomic (the validator then guarantees AXI5 both
    ends, rw and one width)."""
    return is_atomic(m) and is_atomic(s)


def is_mte(p: Port) -> bool:
    return p.protocol == 'axi5' and 'mte' in p.features


def poison_path(m: Port, s: Port) -> bool:
    """Both ends enable poison (the bridge validator then guarantees the
    path carries it natively)."""
    return all(p.protocol == 'axi5' and 'poison' in p.features for p in (m, s))


def find_hole(build: Build, size_lg2: int = 24) -> Optional[int]:
    """The lowest size-aligned block no slave range touches."""
    blk = 1 << size_lg2
    for base in range(0, 1 << 32, blk):
        if all(base + blk <= s.base or base >= s.base + s.size for s in build.slaves):
            return base
    return None


# =============================================================================
# Profiles
# =============================================================================

@dataclass(frozen=True)
class Profile:
    """The knobs of one run. Every field applies to every master / slave."""
    name: str
    rd: bool = True
    wr: bool = True
    errors: bool = False          # SLVERR and DECERR windows
    narrow: bool = False          # sizes below the bus width
    unaligned: bool = False
    strb_rand: bool = False
    bursts: int = 0b111           # [0] FIXED [1] INCR [2] WRAP
    len_mask: int = 0xFF
    single_id: bool = False
    max_out: int = 0              # 0 = as built
    gap_mask: int = 0
    m_resp_throttle: int = 0
    m_data_throttle: int = 0
    s_req_throttle: int = 0
    s_data_throttle: int = 0
    s_lat_min: int = 0
    s_lat_mask: int = 0
    interleave: bool = False
    qos_rand: bool = False
    timeout_lg2: int = 20
    poison_lg2: int = 3           # AXI5 poison paths: 1 beat in 8 poisoned
    atom_lg2: int = 3             # AXI5 atomic masters: 1 write burst in 8 an atomic
    full_axi: bool = False        # no-op since bridge BUG-018/019: path_caps lifts nothing
    s_w_first: bool = False       # stress slaves take AW only while WVALID is up (A3.3.1)


PROFILES: Dict[str, Profile] = {p.name: p for p in (
    Profile('clean', bursts=0b010),
    Profile('bursts'),
    Profile('backpressure', m_resp_throttle=8, m_data_throttle=6,
            s_req_throttle=8, s_data_throttle=8, gap_mask=0x07),
    Profile('reorder', s_lat_mask=0x7F, interleave=True),
    Profile('narrow', narrow=True, unaligned=True, strb_rand=True),
    Profile('single_id', single_id=True, s_lat_mask=0x3F, interleave=True),
    Profile('errors', errors=True, s_lat_mask=0x1F),
    Profile('short', len_mask=0x03, s_lat_mask=0x0F, interleave=True),
    Profile('chaos', errors=True, narrow=True, unaligned=True, strb_rand=True,
            m_resp_throttle=5, m_data_throttle=4, s_req_throttle=5, s_data_throttle=5,
            s_lat_mask=0x3F, interleave=True, qos_rand=True, gap_mask=0x03),
    # slaves that wait for write data before they take the address, as AXI
    # A3.3.1 allows (an AXI CDMA register slave does): bridge BUG-020's gate
    Profile('w_first', s_w_first=True, m_data_throttle=4, s_lat_mask=0x0F),
)}


# =============================================================================
# The harness over a bridge
# =============================================================================

def path_caps(m: Port, s: Port) -> Dict[str, int]:
    """What the bridge can carry from master m to slave s, as window limits.

    None: every path carries the full AXI4 burst set. A path whose data widths
    differ goes through axi4_dwidth_converter_{rd,wr}, which until bridge
    BUG-018/019 emitted illegal AXI for narrow, FIXED, WRAP and unaligned
    bursts (measured by this model on bridge_bs_axi4), so this used to limit
    converted paths to aligned full-width INCR. The converters now handle all
    of them (converters MAS 2.5/2.6), so the limit is gone; Profile.full_axi
    is kept for the CLI and the report column and no longer changes anything.
    """
    return {}


class BuildMismatch(RuntimeError):
    """The bitstream is not the build the TOML describes."""


class StressHarness:
    def __init__(self, bridge, build: Build, log: Callable[[str], None] = print):
        self.bridge = bridge
        self.build = build
        self.log = log
        self.ctl = Device(bridge, 'ctl', regs_base=CTL_BASE,
                          regmap_file=str(REGMAPS / 'bstress_ctl_regs_regmap.py'))
        # one register block per STRESS port, in build.stress_* order
        self.mst = [Device(bridge, f'mst{m.index}', regs_base=MST_BASE + m.index * WIN_STRIDE,
                           regmap_file=str(REGMAPS / 'bstress_mst_regs_regmap.py'))
                    for m in build.stress_masters]
        self.slv = [Device(bridge, f'slv{s.index}', regs_base=SLV_BASE + s.index * WIN_STRIDE,
                           regmap_file=str(REGMAPS / 'bstress_slv_regs_regmap.py'))
                    for s in build.stress_slaves]
        self.vendor = None          # bstress_xil.XilVendors on a build with vendor masters
        self.ocelus = None          # bstress_ocelus.Ocelus when the DUT is its mon variant
        self.hole = find_hole(build)
        self.plan: Dict[int, List[M.Window]] = {}

    # ---- identity ------------------------------------------------------------
    def identify(self) -> None:
        b = self.build
        cid = self.ctl.read('ID')
        if (cid >> 16) != 0x4253:
            raise BuildMismatch(f'control ID {cid:#010x}: no stress harness answers')
        nm, ns = cid & 0xF, (cid >> 4) & 0xF
        if (nm, ns) != (len(b.masters), len(b.slaves)):
            raise BuildMismatch(f'bitstream has {nm} masters / {ns} slaves, '
                                f'{b.name} has {len(b.masters)} / {len(b.slaves)}')
        for dev, ports, magic in ((self.mst, b.stress_masters, 0x5354),
                                  (self.slv, b.stress_slaves, 0x5353)):
            for d, p in zip(dev, ports):
                v = d.read('ID')
                want = (magic << 16) | (PROTO_CODE[p.protocol] << 13) | (p.iw << 8) | (p.dw // 8)
                if v != want:
                    raise BuildMismatch(f'{d.name} ({p.name}): ID {v:#010x}, TOML says {want:#010x}')
        # Ocelus: the bitstream says whether its DUT is the monitored variant
        if self.ctl.field('STATUS', 'HAS_MON'):
            from bstress_ocelus import Ocelus
            self.ocelus = Ocelus(self, Ocelus.regmap_for(AREA, b.name), log=self.log)

    # ---- configuration -------------------------------------------------------
    def windows(self, m: Port, prof: Profile) -> List[M.Window]:
        size_max = (m.dw // 8).bit_length() - 1
        size_min = 0 if prof.narrow else size_max
        common = dict(sb=int(m.protocol == 'axi5' and 'trace' in m.features),
                      atomic=int(is_atomic(m)),
                      len_mask=prof.len_mask, size_min=size_min, size_max=size_max,
                      burst_mask=prof.bursts, unaligned=int(prof.unaligned),
                      strb_rand=int(prof.strb_rand), rd_en=int(m.rd and prof.rd),
                      wr_en=int(m.wr and prof.wr))
        slaves = self.build.slaves_of(m)

        def limited(s: Port) -> dict:
            c = dict(common, poison_lg2=prof.poison_lg2 if poison_path(m, s) else 0,
                     atomic=int(atomic_path(m, s)), mte=int(is_mte(m) and is_mte(s)))
            caps = {} if prof.full_axi else path_caps(m, s)
            if 'bursts' in caps:
                c['burst_mask'] = c['burst_mask'] & caps['bursts'] or caps['bursts']
            if 'size_min' in caps:
                c['size_min'] = max(c['size_min'], caps['size_min'])
            if 'unaligned' in caps:
                c['unaligned'] = c['unaligned'] & caps['unaligned']
            return c

        wins = [M.Window(s.base, s.mem_lg2, MEM_TAG, M.OKAY, mem=1, **limited(s))
                if s.vendor else
                M.Window(s.base, s.size_lg2 - 1, TAG0 + s.index, M.OKAY, **limited(s))
                for s in slaves]
        slaves = [s for s in slaves if not s.vendor]   # SLVERR windows: stress slaves only
        if prof.errors:
            if self.hole is not None:
                wins.append(M.Window(self.hole, 24, 0, M.DECERR, **common))
            k = m.index           # rotate which slaves get an error window
            for j in range(len(slaves)):
                if len(wins) >= NWIN or not slaves:
                    break
                s = slaves[(j + k) % len(slaves)]
                wins.append(M.Window(s.base + (s.size >> 1), s.size_lg2 - 2,
                                     TAG0 + s.index, M.SLVERR, **limited(s)))
        return wins[:NWIN]

    def configure(self, prof: Profile, seed: int, txns: int) -> None:
        b = self.build
        self.plan = {}
        for m, d in zip(b.stress_masters, self.mst):
            wins = self.windows(m, prof)
            self.plan[m.index] = wins
            for i in range(NWIN):
                w = wins[i] if i < len(wins) else None
                if w is None:
                    d.write(f'WIN{i}_CFG1', rd_en=0, wr_en=0)
                    continue
                d.write_word(f'WIN{i}_BASE', w.base)
                d.write(f'WIN{i}_CFG0', size_lg2=w.size_lg2, resp=w.resp, tag=w.tag,
                        len_mask=w.len_mask)
                d.write(f'WIN{i}_CFG1', size_min=w.size_min, size_max=w.size_max,
                        burst_mask=w.burst_mask, unaligned=w.unaligned,
                        strb_rand=w.strb_rand, rd_en=w.rd_en, wr_en=w.wr_en,
                        sb=w.sb, poison_lg2=w.poison_lg2, atomic=w.atomic, mte=w.mte,
                        **({'mem': w.mem} if b.memories else {}))
            # an atomic master's upper ID half belongs to its atomics
            id_bits = m.iw - 1 if is_atomic(m) else m.iw
            id_mask = 0 if prof.single_id else (1 << id_bits) - 1
            for dr, en in (('RD', m.rd and prof.rd), ('WR', m.wr and prof.wr)):
                d.write(f'{dr}_CTRL', enable=int(en), qos_rand=int(prof.qos_rand),
                        idunq=int(m.protocol == 'axi5' and 'unique' in m.features),
                        timeout_lg2=prof.timeout_lg2, resp_throttle=prof.m_resp_throttle,
                        data_throttle=prof.m_data_throttle, gap_mask=prof.gap_mask,
                        max_out=prof.max_out)
                d.write_word(f'{dr}_TXN_COUNT', txns)
                d.write_word(f'{dr}_SEED', (seed * 0x9E37_79B1 + m.index * 0x101 +
                                            (0 if dr == 'RD' else 0x5555)) & M.M32 or 1)
                d.write(f'{dr}_ID_CFG', base=(0xA5 & ((1 << id_bits) - 1)) if prof.single_id else 0,
                        mask=id_mask)
            if any(p.protocol == 'axi5' for p in b.masters + b.slaves):
                d.write('WR_ATOM', lg2=prof.atom_lg2 if is_atomic(m) else 0)
            if b.memories:   # MEM is new with build-xil; older bitstreams lack it
                for dr in ('RD', 'WR'):
                    d.write(f'{dr}_MEM', fill=0, mem_lg2=MEM_LG2)
        axi5 = any(p.protocol == 'axi5' for p in b.masters + b.slaves)
        for s, d in zip(b.stress_slaves, self.slv):
            inorder = len(b.masters_of(s)) <= 1 and not s.ooo
            sb_src = sum(1 << m.index for m in b.masters_of(s) if sb_native(m, s))
            plg2 = prof.poison_lg2 if (s.protocol == 'axi5' and 'poison' in s.features) else 0
            for dr in ('RD', 'WR'):
                if axi5:     # SB is new with AXI5; an older bitstream has no such register
                    d.write(f'{dr}_SB', src=sb_src, poison_lg2=plg2)
                d.write_word(f'{dr}_BASE', s.base)
                d.write(f'{dr}_CTRL', size_lg2=s.size_lg2, offset_mode=0, err_en=1,
                        tag=TAG0 + s.index, inorder=int(inorder),
                        interleave=int(prof.interleave and dr == 'RD'),
                        req_throttle=prof.s_req_throttle, data_throttle=prof.s_data_throttle,
                        w_first=int(prof.s_w_first and dr == 'WR'))
                d.write_word(f'{dr}_ERR_BASE', s.base + (s.size >> 1))
                d.write_word(f'{dr}_ERR_MASK', (~((s.size >> 2) - 1)) & M.M32)
                d.write(f'{dr}_TIMING', lat_min=prof.s_lat_min, lat_mask=prof.s_lat_mask,
                        max_out=0)
                d.write_word(f'{dr}_SEED', (seed * 0x85EB_CA6B + s.index) & M.M32 or 1)

    # ---- run -----------------------------------------------------------------
    def go(self) -> None:
        # The bridge's unmapped-access status is sticky; clear it with GO so a
        # run's DECERR count is that run's.
        self.ctl.write('CTRL', unmapped_clear=1)
        self.ctl.write('CTRL', go=1)

    def stop(self) -> None:
        self.ctl.write('CTRL', stop=1)

    def wait_done(self, timeout_s: float = 60.0, poll_s: float = 0.05,
                  sleep: Callable[[float], None] = time.sleep) -> bool:
        t0 = time.monotonic()
        while time.monotonic() - t0 < timeout_s:
            if self.ctl.field('STATUS', 'ALL_DONE'):
                return True
            if self.vendor is not None:
                self.vendor.tick()      # keep the vendor masters busy meanwhile
            sleep(poll_s)
        return False

    def collect(self) -> dict:
        b = self.build
        out = {'ctl': {r: self.ctl.read(r) for r in
                       ('STATUS', 'TIMER', 'UNMAPPED_COUNT', 'UNMAPPED_ADDR', 'GO_COUNT')}}
        for m, d in zip(b.stress_masters, self.mst):
            for dr in ('RD', 'WR'):
                st = d.read(f'{dr}_STATUS')
                err = d.read(f'{dr}_ERR')
                out[f'{m.name}.{dr.lower()}'] = dict(
                    busy=st & 1, done=(st >> 1) & 1, fe_valid=(st >> 2) & 1,
                    fe_kind=(st >> 4) & 0xF, runs=(st >> 8) & 0xFF, out_max=(st >> 24) & 0xFF,
                    issued=d.read(f'{dr}_ISSUED'), completed=d.read(f'{dr}_COMPLETED'),
                    beats=d.read(f'{dr}_BEATS'), err_mask=err & 0xFFFF, err_cnt=err >> 16,
                    fe_id=d.read(f'{dr}_FE_ID'), fe_addr=d.read(f'{dr}_FE_ADDR'),
                    fe_exp=d.read(f'{dr}_FE_EXP'), fe_act=d.read(f'{dr}_FE_ACT'),
                    lat_max=d.read(f'{dr}_LAT_MAX'), lat_sum=d.read(f'{dr}_LAT_SUM'))
        for s, d in zip(b.stress_slaves, self.slv):
            for dr in ('RD', 'WR'):
                err = d.read(f'{dr}_ERR')
                fe = d.read(f'{dr}_FE')
                o = d.read(f'{dr}_OUT')
                out[f'{s.name}.{dr.lower()}'] = dict(
                    bursts=d.read(f'{dr}_BURSTS'), beats=d.read(f'{dr}_BEATS'),
                    err_mask=err & 0xFFFF, err_cnt=err >> 16,
                    fe_valid=fe & 1, fe_kind=(fe >> 4) & 0xF, fe_id=fe >> 16,
                    fe_addr=d.read(f'{dr}_FE_ADDR'), fe_exp=d.read(f'{dr}_FE_EXP'),
                    fe_act=d.read(f'{dr}_FE_ACT'), out_max=(o >> 8) & 0xFF,
                    runs=(o >> 16) & 0xFF)
        return out

    def run(self, prof: Profile, seed: int, txns: int, timeout_s: float = 60.0,
            sleep: Callable[[float], None] = time.sleep) -> dict:
        if txns <= 0:
            raise ValueError('a verdict needs a budget: txns >= 1')
        if self.ocelus is not None:     # before the fill: it is part of the run
            self.ocelus.configure(prof)
        fill_why = self.sweep('WR', timeout_s, sleep) if self.build.memories else []
        self.configure(prof, seed, txns)
        if self.vendor is not None:
            self.vendor.start(prof, seed)
        self.go()
        finished = self.wait_done(timeout_s, sleep=sleep)
        if not finished:
            self.stop()
        vendor_why = self.vendor.finish(sleep) if self.vendor is not None else []
        res = self.collect()
        if self.build.memories:   # after collect: the sweep is a GO of its own
            vendor_why += self.sweep('RD', timeout_s, sleep)
        res['meta'] = dict(profile=prof.name, seed=seed, txns=txns, finished=finished)
        res['prof'] = prof
        res['vendor'] = fill_why + vendor_why
        if self.ocelus is not None:
            res['ocelus'] = [self.ocelus.describe(p) for p in self.ocelus.drain()]
        return res

    # ---- real memories -------------------------------------------------------
    def sweep(self, dr: str, timeout_s: float = 60.0,
              sleep: Callable[[float], None] = time.sleep) -> List[str]:
        """One GO in which, for every memory, the first connected stress
        master sweeps its mem window (cfg fill) in full-width bursts:
        dr 'WR' writes the image (before a run), 'RD' reads every byte back
        against it (after one, so a byte any master -- the vendor masters
        included -- left wrong is caught). Returns what went wrong."""
        b, why = self.build, []
        owner: Dict[int, Port] = {}
        for s in b.memories:
            free = [m for m in b.stress_masters if s in b.slaves_of(m)
                    and (m.wr if dr == 'WR' else m.rd) and m.index not in owner]
            if not free:
                why.append(f'{s.name}: no free stress master can sweep it')
                continue
            owner[free[0].index] = s
        for m, d in zip(b.stress_masters, self.mst):
            s = owner.get(m.index)
            for i in range(NWIN):
                d.write(f'WIN{i}_CFG1', rd_en=0, wr_en=0)
            for x in ('RD', 'WR'):
                d.write(f'{x}_CTRL', enable=int(s is not None and x == dr), timeout_lg2=20)
                d.write(f'{x}_MEM', fill=int(s is not None and x == dr), mem_lg2=MEM_LG2)
            if s is None:
                continue
            full = (m.dw // 8).bit_length() - 1
            d.write_word('WIN0_BASE', s.base)
            d.write('WIN0_CFG0', size_lg2=s.mem_lg2, resp=M.OKAY, tag=MEM_TAG, len_mask=0xFF)
            # sb as in windows(): the bridge's AXI5 trace port echoes the
            # request's trace on B / R (bridge BUG-010) on every path
            d.write('WIN0_CFG1', size_min=full, size_max=full, burst_mask=0b010,
                    unaligned=0, strb_rand=0, rd_en=int(dr == 'RD'), wr_en=int(dr == 'WR'),
                    sb=int(m.protocol == 'axi5' and 'trace' in m.features), mem=1)
            d.write_word(f'{dr}_TXN_COUNT', sweep_bursts(m, s))
            d.write(f'{dr}_ID_CFG', base=0, mask=0)
        self.go()
        if not self.wait_done(timeout_s, sleep=sleep):
            self.stop()
            why.append(f'{dr.lower()} sweep: timed out before ALL_DONE')
        for m, d in zip(b.stress_masters, self.mst):
            if m.index not in owner:
                continue
            s = owner[m.index]
            err = d.read(f'{dr}_ERR') & 0xFFFF
            n = d.read(f'{dr}_COMPLETED')
            want = sweep_bursts(m, s)
            if err or n != want:
                fe = ''
                if err:
                    fe = (f" first at {d.read(f'{dr}_FE_ADDR'):#010x} exp "
                          f"{d.read(f'{dr}_FE_EXP'):#010x} act {d.read(f'{dr}_FE_ACT'):#010x}")
                why.append(f'{dr.lower()} sweep of {s.name} by {m.name}: '
                           f'{M.err_list(err)}, {n} of {want} bursts{fe}')
        return why

    # ---- verdict -------------------------------------------------------------
    def verdict(self, res: dict) -> Tuple[bool, List[str]]:
        b, prof, why = self.build, res['prof'], []
        n = res['meta']['txns']
        if not res['meta']['finished']:
            why.append('timed out before ALL_DONE')
        # Every block must have taken THIS run's GO; one that missed it still
        # shows the previous run's status, which can look like a pass.
        gos = res['ctl']['GO_COUNT'] & 0xFF
        for m in b.stress_masters:
            for dr, built in (('rd', m.rd), ('wr', m.wr)):
                if built and res[f'{m.name}.{dr}']['runs'] != gos:
                    why.append(f"{m.name}.{dr}: took {res[f'{m.name}.{dr}']['runs']} GOs, "
                               f"control issued {gos}")
        for s in b.stress_slaves:
            for dr, built in (('rd', s.rd), ('wr', s.wr)):
                if built and res[f'{s.name}.{dr}']['runs'] != gos:
                    why.append(f"{s.name}.{dr}: took {res[f'{s.name}.{dr}']['runs']} GOs, "
                               f"control issued {gos}")
        for m in b.stress_masters:
            for dr, en in (('rd', m.rd and prof.rd), ('wr', m.wr and prof.wr)):
                r = res[f'{m.name}.{dr}']
                if r['err_mask']:
                    why.append(f'{m.name}.{dr}: {M.err_list(r["err_mask"])} x{r["err_cnt"]}'
                               + self._fe(r))
                if en and (r['issued'] != n or r['completed'] != n):
                    why.append(f'{m.name}.{dr}: issued {r["issued"]} completed '
                               f'{r["completed"]} of {n}')
        for s in b.stress_slaves:
            for dr in ('rd', 'wr'):
                r = res[f'{s.name}.{dr}']
                if r['err_mask']:
                    why.append(f'{s.name}.{dr}: {M.err_list(r["err_mask"])} x{r["err_cnt"]}'
                               + self._fe(r))
            reached = res[f'{s.name}.rd']['beats'] + res[f'{s.name}.wr']['beats']
            if [m for m in b.masters_of(s) if not m.vendor] and reached == 0:
                why.append(f'{s.name}: no traffic reached it')
        why += res.get('vendor', [])
        # every Ocelus record is a finding: timeouts always, errors when the
        # profile injects none (bstress_ocelus.Ocelus.configure)
        why += [f'ocelus: {r}' for r in res.get('ocelus', [])]
        unm = res['ctl']['UNMAPPED_COUNT'] & 0xFF
        if prof.errors and self.hole is not None and unm == 0:
            why.append('DECERR windows planned but the bridge saw no unmapped access')
        if not prof.errors and unm:
            why.append(f'{unm} unmapped accesses with no DECERR window planned')
        return (not why), why

    @staticmethod
    def _fe(r: dict) -> str:
        if not r['fe_valid']:
            return ''
        return (f' (first {M.ERR_NAMES.get(r["fe_kind"], r["fe_kind"])} id={r["fe_id"]:#x} '
                f'addr={r["fe_addr"]:#010x} exp={r["fe_exp"]:#010x} act={r["fe_act"]:#010x})')

    def summary(self, res: dict, hz: float) -> str:
        b = self.build
        t = res['ctl']['TIMER'] or 1
        lines = [f"{res['meta']['profile']} seed={res['meta']['seed']} "
                 f"txns={res['meta']['txns']}: {t} cycles ({t / hz * 1e3:.2f} ms)"]
        for m in b.stress_masters:
            for dr in ('rd', 'wr'):
                r = res[f'{m.name}.{dr}']
                if not r['issued']:
                    continue
                mb = r['beats'] * (m.dw // 8) / (t / hz) / 1e6
                lat = r['lat_sum'] / max(1, r['completed'])
                lines.append(f"  {m.name:>6}.{dr} {r['completed']:>7} bursts {r['beats']:>8} beats "
                             f"{mb:8.1f} MB/s  lat mean {lat:8.1f} max {r['lat_max']:>9}  "
                             f"out max {r['out_max']}")
        for s in b.stress_slaves:
            rd, wr = res[f'{s.name}.rd'], res[f'{s.name}.wr']
            lines.append(f"  {s.name:>6}    rd {rd['bursts']:>7} bursts {rd['beats']:>8} beats   "
                         f"wr {wr['bursts']:>7} bursts {wr['beats']:>8} beats")
        lines.append(f"  unmapped {res['ctl']['UNMAPPED_COUNT'] & 0xFF}")
        return '\n'.join(lines)
