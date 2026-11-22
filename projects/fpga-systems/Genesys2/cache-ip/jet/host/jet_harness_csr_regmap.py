# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Hand-authored register map for jet_pair_harness's harness_csr aperture.
# Matches the jet_harness_csr SV implementation in jet_pair_harness.sv.

"""
Register map dictionary for jet_harness_csr

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
        'tally_clear': {'default': '0x0', 'offset': '0', 'sw': 'rw', 'type': 'field'},
        # tally_clear is write-1-pulse in the RTL: a write with bit 0 set
        # produces a one-cycle tally_clear strobe and the bit self-clears
        # (always reads 0). tally_freeze is a plain level bit.
        'tally_freeze': {'default': '0x0', 'offset': '1', 'sw': 'rw', 'type': 'field'},
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
    'ONYX_CNT_TXN': {
        # onyx TASK-001 (reference rig REF_CACHE_SEL 4/5 only; the jet rig and
        # the other selections read 0): transactions granted; cleared by CTRL[0], held by CTRL[1]
        'address': '0x020',
        'default': '0x00000000',
        'name': 'ONYX_CNT_TXN',
        'offset': '0x020',
        'size': 4,
        'sw': 'r',
        'type': 'reg',
        'value': {'default': '0x00000000', 'offset': '31:0', 'sw': 'r', 'type': 'field'},
    },
    'ONYX_CNT_SUPPLIED': {
        # onyx TASK-001 (reference rig REF_CACHE_SEL 4/5 only; the jet rig and
        # the other selections read 0): lines a peer supplied; cleared by CTRL[0], held by CTRL[1]
        'address': '0x024',
        'default': '0x00000000',
        'name': 'ONYX_CNT_SUPPLIED',
        'offset': '0x024',
        'size': 4,
        'sw': 'r',
        'type': 'reg',
        'value': {'default': '0x00000000', 'offset': '31:0', 'sw': 'r', 'type': 'field'},
    },
    'ONYX_CNT_MEM_READ': {
        # onyx TASK-001 (reference rig REF_CACHE_SEL 4/5 only; the jet rig and
        # the other selections read 0): memory reads issued; cleared by CTRL[0], held by CTRL[1]
        'address': '0x028',
        'default': '0x00000000',
        'name': 'ONYX_CNT_MEM_READ',
        'offset': '0x028',
        'size': 4,
        'sw': 'r',
        'type': 'reg',
        'value': {'default': '0x00000000', 'offset': '31:0', 'sw': 'r', 'type': 'field'},
    },
    'ONYX_CNT_READ_WASTED': {
        # onyx TASK-001 (reference rig REF_CACHE_SEL 4/5 only; the jet rig and
        # the other selections read 0): reads issued then the line supplied (beats dropped); cleared by CTRL[0], held by CTRL[1]
        'address': '0x02C',
        'default': '0x00000000',
        'name': 'ONYX_CNT_READ_WASTED',
        'offset': '0x02C',
        'size': 4,
        'sw': 'r',
        'type': 'reg',
        'value': {'default': '0x00000000', 'offset': '31:0', 'sw': 'r', 'type': 'field'},
    },
    'ONYX_CNT_ABSORB': {
        # onyx TASK-001 (reference rig REF_CACHE_SEL 4/5 only; the jet rig and
        # the other selections read 0): PassDirty lines absorbed into memory; cleared by CTRL[0], held by CTRL[1]
        'address': '0x030',
        'default': '0x00000000',
        'name': 'ONYX_CNT_ABSORB',
        'offset': '0x030',
        'size': 4,
        'sw': 'r',
        'type': 'reg',
        'value': {'default': '0x00000000', 'offset': '31:0', 'sw': 'r', 'type': 'field'},
    },
    'ONYX_CNT_WB': {
        # onyx TASK-001 (reference rig REF_CACHE_SEL 4/5 only; the jet rig and
        # the other selections read 0): cache write-backs taken; cleared by CTRL[0], held by CTRL[1]
        'address': '0x034',
        'default': '0x00000000',
        'name': 'ONYX_CNT_WB',
        'offset': '0x034',
        'size': 4,
        'sw': 'r',
        'type': 'reg',
        'value': {'default': '0x00000000', 'offset': '31:0', 'sw': 'r', 'type': 'field'},
    },
}
