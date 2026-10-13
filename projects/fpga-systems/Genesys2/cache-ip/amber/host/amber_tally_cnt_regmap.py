# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Hand-authored register map for monbus_tally_axil count readback aperture.
# monbus_tally_axil stores 33 entries: bins 0..31 are the legal-set profile
# bins; bin 32 is the UNEXPECTED catch-all. The amber bridge exposes each as
# a 64-bit entry, but the host 32-bit read path returns the lower 32 bits.

"""
Register map dictionary for amber_tally_cnt

Compatible with bin/TBClasses/apb/register_map.py and the UART-aware
TBClasses.harness.uart_register_map.UartRegisterMap wrapper.
"""

top_block = {}

for i in range(32):
    off = i * 8
    name = f"COUNT{i}"
    top_block[name] = {
        'address': f'0x{off:03X}',
        'default': '0x00000000',
        'name': name,
        'offset': f'0x{off:03X}',
        'size': 4,
        'sw': 'r',
        'type': 'reg',
        'value': {'default': '0x00000000', 'offset': '31:0', 'sw': 'r', 'type': 'field'},
    }

top_block['UNEXPECTED'] = {
    'address': '0x100',
    'default': '0x00000000',
    'name': 'UNEXPECTED',
    'offset': '0x100',
    'size': 4,
    'sw': 'r',
    'type': 'reg',
    'value': {'default': '0x00000000', 'offset': '31:0', 'sw': 'r', 'type': 'field'},
}
