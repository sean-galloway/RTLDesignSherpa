# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Hand-authored register map for amber_pair_harness's harness_csr aperture.
# Matches the amber_harness_csr SV implementation in amber_pair_harness.sv.

"""
Register map dictionary for amber_harness_csr

Compatible with bin/TBClasses/apb/register_map.py and the UART-aware
TBClasses.harness.uart_register_map.UartRegisterMap wrapper.
"""

top_block = {
    'CTRL': {
        'address': '0x000',
        'default': '0x00000000',
        'name': 'CTRL',
        'offset': '0x000',
        'size': 4,
        'sw': 'rw',
        'type': 'reg',
        'value': {'default': '0x00000000', 'offset': '31:0', 'sw': 'rw', 'type': 'field'},
    },
    'STATUS': {
        'address': '0x004',
        'ci0_done': {'default': '0x0', 'offset': '0', 'sw': 'r', 'type': 'field'},
        'ci1_done': {'default': '0x0', 'offset': '1', 'sw': 'r', 'type': 'field'},
        'ci0_busy': {'default': '0x0', 'offset': '2', 'sw': 'r', 'type': 'field'},
        'ci1_busy': {'default': '0x0', 'offset': '3', 'sw': 'r', 'type': 'field'},
        'ci0_err': {'default': '0x0', 'offset': '4', 'sw': 'r', 'type': 'field'},
        'ci1_err': {'default': '0x0', 'offset': '5', 'sw': 'r', 'type': 'field'},
        'default': '0x00000000',
        'name': 'STATUS',
        'offset': '0x004',
        'size': 4,
        'sw': 'rw',
        'type': 'reg',
    },
    'CYCLE_LO': {
        'address': '0x008',
        'default': '0x00000000',
        'name': 'CYCLE_LO',
        'offset': '0x008',
        'size': 4,
        'sw': 'r',
        'type': 'reg',
        'value': {'default': '0x00000000', 'offset': '31:0', 'sw': 'r', 'type': 'field'},
    },
    'CYCLE_HI': {
        'address': '0x00C',
        'default': '0x00000000',
        'name': 'CYCLE_HI',
        'offset': '0x00C',
        'size': 4,
        'sw': 'r',
        'type': 'reg',
        'value': {'default': '0x00000000', 'offset': '31:0', 'sw': 'r', 'type': 'field'},
    },
    'FABRIC_DBG': {
        'address': '0x010',
        'default': '0x00000000',
        'name': 'FABRIC_DBG',
        'offset': '0x010',
        'size': 4,
        'sw': 'r',
        'type': 'reg',
        'value': {'default': '0x00000000', 'offset': '3:0', 'sw': 'r', 'type': 'field'},
    },
}
