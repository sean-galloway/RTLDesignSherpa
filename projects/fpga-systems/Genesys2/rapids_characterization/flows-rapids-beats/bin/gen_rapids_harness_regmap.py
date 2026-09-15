#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Generate the RAPIDS characterization HARNESS register maps (top_block dicts)
from a compact table mirroring rapids_char_top.sv's documented address map.

The rapids char harness has two HAND-ROLLED register regions (no PeakRDL RDL --
they are decoded directly in rapids_char_top.sv), so -- exactly like the STREAM
char harness (stream_char_framework/bin/gen_harness_regmap.py) -- their regmaps
are hand-maintained here to mirror the RTL:

  * DESC-LOAD  (host region 1, base 0x1_0000): the 256-bit descriptor holding
    registers + the kick/status. -> rapids_harness_desc_regmap.py
  * HARNESS CSR (host region 2, base 0x2_0000): gen/chk/mem/mon control + status
    + per-channel CRC readbacks. -> rapids_harness_csr_regmap.py

Offsets are relative to the region base; the host Device/RegisterMap is given the
region start_address. Output format matches TBClasses.apb.register_map.RegisterMap
(the same `top_block` schema the STREAM harness + DUT regmaps use).

Run:  REPO_ROOT=<repo> python3 gen_rapids_harness_regmap.py
"""
import os
import pprint

# (offset, NAME, sw, [(FIELD, msb, lsb, fsw), ...] or None for a plain 32-bit word)
# sw: 'r' read-only, 'w' write-only (modeled 'rw'), 'rw' read-write.


def _build(regs):
    top = {}
    for off, name, sw, fields in regs:
        d = {'address': hex(off), 'default': '0x00000000', 'name': name,
             'offset': hex(off), 'size': 4, 'sw': sw, 'type': 'reg'}
        if fields:
            for fn, msb, lsb, fsw in fields:
                d[fn] = {'default': '0x0', 'offset': f'{msb}:{lsb}',
                         'sw': fsw, 'type': 'field'}
            top_used_msb = max(m for _, m, _, _ in fields)
            if top_used_msb < 31:
                d['RSVD'] = {'default': '0x0', 'offset': f'31:{top_used_msb + 1}',
                             'sw': 'r', 'type': 'field'}
        else:
            d['VALUE'] = {'default': '0x0', 'offset': '31:0', 'sw': sw, 'type': 'field'}
        top[name] = d
    return top


# ---------------------------------------------------------------------------
# DESC-LOAD region (host region 1). rapids_char_top.sv DESC_* offsets.
# ---------------------------------------------------------------------------
DESC = []
for i in range(8):                       # DESC_WORD[0..7] @ 0x000..0x01C
    DESC.append((0x000 + 4 * i, f'DESC_WORD{i}', 'rw', None))
DESC += [
    (0x020, 'DESC_ADDR',   'rw', None),                        # target byte addr
    (0x024, 'DESC_KICK',   'w',  [('HALF', 0, 0, 'w')]),       # data[0]=half (0=SRC,1=SNK)
    (0x028, 'DESC_STATUS', 'r',  [('OK', 0, 0, 'r')]),         # last-write BRESP OK
]

# ---------------------------------------------------------------------------
# HARNESS CSR region (host region 2). rapids_char_top.sv CSR_* localparams.
# Field bits verified against the RTL write-decode (r_wdata[..] assignments).
# ---------------------------------------------------------------------------
CSR = [
    # ---- writable control ----
    (0x000, 'CTRL',        'w',  [('CAM_CLEAR', 0, 0, 'w')]),          # 1-cycle pulse
    (0x010, 'GEN_CTRL',    'w',  [('GEN_START', 0, 0, 'w')]),         # cfg_gen_start pulse
    (0x014, 'GEN_SEED',    'rw', None),
    (0x018, 'GEN_NBEATS',  'rw', None),
    (0x01C, 'GEN_BPP',     'rw', None),
    (0x020, 'GEN_CHMASK',  'rw', None),
    (0x024, 'GEN_TDEST',   'rw', None),
    (0x030, 'CHK_CTRL',    'rw', [('CHK_START', 0, 0, 'w'),           # pulse
                                  ('CHK_READY_EN', 1, 1, 'rw')]),     # level
    (0x034, 'CHK_SEED',    'rw', None),
    (0x040, 'MEM_CTRL',    'w',  [('RD_CRC_LFSR_RESET', 0, 0, 'w'),   # pulse
                                  ('WR_CRC_RESET', 1, 1, 'w')]),      # pulse
    (0x050, 'MON_BASE',    'rw', None),
    (0x054, 'MON_LIMIT',   'rw', None),
    (0x058, 'MON_FLUSHWM', 'rw', None),
    (0x060, 'CH_SEL',      'rw', None),                               # indexed-read selector
    (0x0C0, 'OBS_CTRL',    'w',  [('ARM', 0, 0, 'w')]),               # bus-meter re-arm pulse
    # ---- readable status ----  (CSR_ID aliases 0x000 on the read path)
    (0x080, 'STATUS',      'r',  [('MON_IRQ', 0, 0, 'r'), ('SRC_IDLE', 1, 1, 'r'),
                                  ('SNK_IDLE', 2, 2, 'r'), ('GEN_BUSY', 3, 3, 'r'),
                                  ('GEN_DONE', 4, 4, 'r'), ('DATA_ERROR', 5, 5, 'r'),
                                  ('RD_MEM_BUSY', 6, 6, 'r'), ('WR_MEM_BUSY', 7, 7, 'r')]),
    (0x084, 'GEN_BEATS_T', 'r', None),
    (0x088, 'CHK_BEATS_T', 'r', None),
    (0x08C, 'PKT_CNT',     'r', None),
    (0x090, 'RD_BEATS_T',  'r', None),
    (0x094, 'WR_BEATS_T',  'r', None),
    (0x098, 'SRC_SCHERR',  'r', None),
    (0x09C, 'SNK_SCHERR',  'r', None),
    # per-channel readbacks, indexed by CH_SEL (0x060)
    (0x0A0, 'GEN_EXP_CRC', 'r', None),
    (0x0A4, 'CHK_ACT_CRC', 'r', None),
    (0x0A8, 'RD_CRC',      'r', None),
    (0x0AC, 'WR_CRC',      'r', None),
    (0x0B0, 'GEN_EXP_VLD', 'r', None),
    (0x0B4, 'CHK_ACT_VLD', 'r', None),
    (0x0B8, 'RD_CRC_VLD',  'r', None),
    (0x0BC, 'WR_CRC_VLD',  'r', None),
    # per-direction AXI bus-meter buckets (axi_bus_meter, frozen window)
    (0x100, 'OBS_RD_PROD', 'r', None),
    (0x104, 'OBS_RD_BP',   'r', None),
    (0x108, 'OBS_RD_STARV','r', None),
    (0x10C, 'OBS_RD_IDLE', 'r', None),
    (0x110, 'OBS_WR_PROD', 'r', None),
    (0x114, 'OBS_WR_BP',   'r', None),
    (0x118, 'OBS_WR_STARV','r', None),
    (0x11C, 'OBS_WR_IDLE', 'r', None),
    (0x120, 'OBS_SIN_PROD', 'r', None),   # AXIS sink ingress (s_axis)
    (0x124, 'OBS_SIN_BP',   'r', None),
    (0x128, 'OBS_SIN_STARV','r', None),
    (0x12C, 'OBS_SIN_IDLE', 'r', None),
    (0x130, 'OBS_SOUT_PROD', 'r', None),  # AXIS source egress (m_axis)
    (0x134, 'OBS_SOUT_BP',   'r', None),
    (0x138, 'OBS_SOUT_STARV','r', None),
    (0x13C, 'OBS_SOUT_IDLE', 'r', None),
    # AXIS-native throughput (axis_bus_meter): exact bytes (64b LO/HI) + packets
    (0x140, 'OBS_SIN_BYTES_LO', 'r', None),
    (0x144, 'OBS_SIN_BYTES_HI', 'r', None),
    (0x148, 'OBS_SIN_PKTS',     'r', None),
    (0x14C, 'OBS_SOUT_BYTES_LO','r', None),
    (0x150, 'OBS_SOUT_BYTES_HI','r', None),
    (0x154, 'OBS_SOUT_PKTS',    'r', None),
]

_HDR = '''# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Register map for the RAPIDS characterization HARNESS {region} region.
# SEPARATE from rapids_regmap.py (the RAPIDS DUT registers) -- this is the char
# harness's OWN hand-rolled register block, decoded directly in rapids_char_top.sv
# (not PeakRDL). Hand-maintained to mirror that RTL; regenerate with
# bin/gen_rapids_harness_regmap.py. Offsets are relative to the region base
# (host region {region_num}); the Device/RegisterMap is given start_address.
#
# Accessed BY NAME so the harness code never hardcodes an offset/bitmask:
#   regs.write("{example_reg}", {example_field}=..)   /   regs.field("STATUS", "GEN_DONE")

"""RAPIDS Characterization Harness {region} Register Map."""

'''


def _write(path, top, region, region_num, example_reg, example_field):
    with open(path, 'w') as f:
        f.write(_HDR.format(region=region, region_num=region_num,
                            example_reg=example_reg, example_field=example_field))
        f.write('top_block = ' + pprint.pformat(top, width=100, sort_dicts=True) + '\n')
    return len(top)


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rtl = os.path.join(here, '..', 'rtl')
    n_csr = _write(os.path.join(rtl, 'rapids_harness_csr_regmap.py'),
                   _build(CSR), 'CSR', 2, 'GEN_CTRL', 'GEN_START')
    n_desc = _write(os.path.join(rtl, 'rapids_harness_desc_regmap.py'),
                    _build(DESC), 'DESC-LOAD', 1, 'DESC_KICK', 'HALF')
    print(f'generated rapids_harness_csr_regmap.py ({n_csr} regs) + '
          f'rapids_harness_desc_regmap.py ({n_desc} regs)')


if __name__ == '__main__':
    main()
