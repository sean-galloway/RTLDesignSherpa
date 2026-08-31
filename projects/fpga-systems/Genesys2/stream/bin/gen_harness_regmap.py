#!/usr/bin/env python3
"""Generate harness_csr_regmap.py (top_block) from a compact table mirroring
harness_csr.sv's documented address map. Offsets are relative to the harness
CSR base (0x0001_0000); UartRegisterMap adds start_address."""
import pprint

# (offset, NAME, [(FIELD, msb, lsb, sw), ...] or None for a plain 32-bit RO word, sw)
# sw: 'r' read-only, 'w' write-only (modeled 'rw'), 'rw' read-write.
R = []
def reg(off, name, sw='r', fields=None):
    R.append((off, name, sw, fields))

reg(0x00, 'CTRL', 'rw', [('START',0,0,'w'),('CLEAR_STATS',1,1,'w'),
    ('FREEZE_TRACE',2,2,'rw'),('SOFT_RESET',3,3,'w'),('CAM_CLEAR',4,4,'w')])
reg(0x04, 'STATUS', 'r', [('STREAM_IRQ',0,0,'r'),('ANY_ERROR',1,1,'r'),
    ('TRACE_OVERFLOW',2,2,'r'),('CLEAR_BUSY',3,3,'r')])
reg(0x08, 'DBG_WR_PTR'); reg(0x0C, 'DBG_OVERFLOW')
reg(0x10, 'CRC_RD_EXPECTED'); reg(0x14, 'CRC_WR_EXPECTED')
reg(0x18, 'CRC_WR_COMPUTED')
reg(0x1C, 'CRC_MATCH', 'r', [('MATCH',0,0,'r'),('VALID',1,1,'r')])
reg(0x20, 'SCRATCH', 'rw'); reg(0x24, 'BUILD_ID')
reg(0x28, 'TIMER_CTRL', 'rw', [('CLEAR',0,0,'w')])
reg(0x2C, 'TIMER_STATUS', 'r', [('DONE',0,0,'r'),('RUNNING',1,1,'r'),('PASS',2,2,'r')])
reg(0x30, 'TIMER_CYCLES_LO'); reg(0x34, 'TIMER_CYCLES_HI')
reg(0x38, 'TIMER_EXPECTED_BEATS', 'rw')
reg(0x3C, 'RESP_DELAY', 'rw', [('RD_DELAY',15,0,'rw'),('WR_DELAY',31,16,'rw')])
reg(0x40, 'TIMER_R_FIRST_LO'); reg(0x44, 'TIMER_R_FIRST_HI')
reg(0x48, 'TIMER_R_LAST_LO');  reg(0x4C, 'TIMER_R_LAST_HI')
reg(0x50, 'TIMER_W_FIRST_LO'); reg(0x54, 'TIMER_W_FIRST_HI')
reg(0x58, 'TIMER_W_LAST_LO');  reg(0x5C, 'TIMER_W_LAST_HI')
for ch in range(8): reg(0x60 + 4*ch, f'CRC_RD_PER_CH{ch}')
for ch in range(8): reg(0x80 + 4*ch, f'CRC_WR_PER_CH{ch}')
reg(0xA0, 'CRC_VALID_MASK'); reg(0xA4, 'CRC_MATCH_MASK')
# 0xB0-0xD0 were the kick-burst shadow addresses + KICK_GO. Retired: the launch
# is now STREAM's own CHx_CTRL_{LOW,HIGH} + KICK_ENABLE, so the harness no
# longer shadows descriptor addresses or pulses kick lines. The slots are left
# unallocated rather than reused, so an old host writing 0xC0 reads/writes a
# hole instead of silently hitting some new register.
reg(0xD4, 'DESC_SRAM_AR_HS'); reg(0xD8, 'DESC_SRAM_R_HS')
reg(0xE0, 'DESC_AR_HS'); reg(0xE4, 'DESC_AR_STALL')
reg(0xE8, 'DESC_R_HS');  reg(0xEC, 'DESC_R_STALL')
reg(0xF0, 'DESC_AW_HS'); reg(0xF4, 'DESC_W_HS')
reg(0xF8, 'DESC_B_HS');  reg(0xFC, 'DESC_VR_LIVE')
# The observer's flat telemetry window at 0x100..0x11C, and the histogram
# readback pair at 0x124/0x128, are GONE. They are not declared here, and must
# not come back.
#
# The observer grew its own regblock and took its telemetry with it: address a
# counter by writing OBS_STAT_SEL, read OBS_STAT_DATA, both in the observer's
# own window (see bin/obs_addrs.py). harness_csr.sv kept only 0x120, the legacy
# selector, and decodes nothing else in that range.
#
# This generator kept emitting all eleven. Nothing failed -- H() answered with a
# plausible address, the bridge answered, the decoder returned its default of 0,
# and bus_meters, ext_char and everything importing their readers printed clean,
# complete, entirely zero measurements of a DMA moving 1.5 GB/s. Found on
# silicon 2026-08-31.
#
# bin/tests/test_harness_regmap.py::test_every_regmap_register_is_actually_decoded
# now asserts every register here has a case label in harness_csr.sv, so a
# register that the RTL does not implement cannot be declared again.
# OBS_HIST_SEL is SIX bits in hardware, not 32. harness_csr.sv:295 declares
# `output logic [5:0] o_obs_hist_sel`, the write takes int_wdata[5:0] (line 586)
# and the read zero-extends (line 737), with the encoding documented at line 291:
#     {bin[5:2], metric[1], bus[0]}
# Declared without fields it inherited the generator's blanket VALUE[31:0] rw,
# which claims 26 writable bits that do not exist. A host selecting histogram
# bin 0x40 would silently select bin 0. Found by RegisterMap.walk on the board:
# wrote 0xFFFFFFFF, read 0x0000003F.
reg(0x120, 'OBS_HIST_SEL', 'rw', fields=[
    ('BUS',    0, 0, 'rw'),      # which bus: 0=read, 1=write
    ('METRIC', 1, 1, 'rw'),      # which metric
    ('BIN',    5, 2, 'rw'),      # histogram bin index 0..15
])
# 0x124 / 0x128 (OBS_HIST_DATA / OBS_HIST_TOTAL): retired with the above.
# Build identity: what BITSTREAM this is, not just which harness family.
# These are read-only elaboration constants; without them in the regmap a host
# has to reach them by computed offset, which is exactly the hardcoding the
# by-name rule exists to stop.
reg(0x1D0, 'BUILD_VERSION')
reg(0x1D4, 'BUILD_CONFIG', 'r', [('NUM_CHANNELS',4,0,'r'), ('ERROR_FLAVOR',5,5,'r'),
                                 ('USE_MONITORS',6,6,'r'), ('GEN_MON',7,7,'r'),
                                 # DATA_WIDTH_B occupies 15:8. MAIN_CONES sits at
                                 # 16 (previously reserved) so the fields below it
                                 # keep their positions. ERROR_FLAVOR + MAIN_CONES
                                 # together describe the cone set: 0/1 = the legacy
                                 # halves, both = the union build.
                                 ('DATA_WIDTH_B',15,8,'r'), ('MAIN_CONES',16,16,'r')])
reg(0x1D8, 'BUILD_N_PROFILE')
# Harness clock in Hz -- the host reads this instead of assuming 100 MHz.
reg(0x1DC, 'BUILD_CLK_HZ')
# Monbus-compression observer readback
for i,n in enumerate(['COMP_TIER1_A','COMP_TIER1_B','COMP_TIER1_C','COMP_TIER0',
                      'COMP_CAM_MISS','COMP_DELTA_TS_OVF','COMP_EVENT_DATA_OVF','COMP_ED_DELTA_OVF']):
    reg(0x1E0 + 4*i, n)

top = {}
for off, name, sw, fields in R:
    d = {'address': hex(off), 'default': '0x00000000', 'name': name,
         'offset': hex(off), 'size': 4, 'sw': sw, 'type': 'reg'}
    if fields:
        used = 0
        for fn, msb, lsb, fsw in fields:
            d[fn] = {'default': '0x0', 'offset': f'{msb}:{lsb}', 'sw': fsw, 'type': 'field'}
            used |= ((1 << (msb - lsb + 1)) - 1) << lsb
        # add RSVD for the remaining bits so the field model is complete
        # (single contiguous top RSVD is sufficient for by-name access)
        top_used_msb = max(m for _, m, _, _ in fields)
        if top_used_msb < 31:
            d['RSVD'] = {'default': '0x0', 'offset': f'31:{top_used_msb+1}', 'sw': 'r', 'type': 'field'}
    else:
        d['VALUE'] = {'default': '0x0', 'offset': '31:0', 'sw': sw, 'type': 'field'}
    top[name] = d

hdr = '''# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Register map for the STREAM characterization HARNESS CSRs (harness_csr.sv).
# SEPARATE from stream_regmap.py (the STREAM IP registers) -- this is the char
# harness's own control/status/timer/observer/kick block at base 0x0001_0000.
# Fed to the harness code as its own device so harness registers are accessed by
# name: harness.write("RUN_CTRL", ...) / harness.read("TIMER_CYCLES_LO") /
# harness.field("TIMER_STATUS", "DONE"), exactly like the STREAM device.
#
# Hand-maintained to mirror harness_csr.sv's documented address map (the harness
# CSRs are hand-coded RTL, not PeakRDL). Offsets are relative to the base; the
# UartRegisterMap/Device is given start_address=0x0001_0000.
#
# Usage:
#   from TBClasses.harness.uart_register_map import UartRegisterMap
#   regs = UartRegisterMap(bridge, start_address=0x0001_0000,
#                          regmap_file=".../harness_csr_regmap.py")

"""STREAM Characterization Harness CSR Register Map (base 0x0001_0000)."""

'''
# Write next to THIS script's component, not to a path hardcoded from the
# pre-migration tree -- a generator that names an absolute path silently keeps
# updating the old copy after the component moves, so the new tree's regmap
# quietly goes stale (see [[flow-migration]] on anchoring, never counting).
import os as _os
_OUT = _os.path.join(_os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))),
                     'rtl', 'harness_csr_regmap.py')
with open(_OUT, 'w') as f:
    f.write(hdr)
    f.write('top_block = ' + pprint.pformat(top, width=100, sort_dicts=True) + '\n')
print(f'generated {len(top)} registers')
