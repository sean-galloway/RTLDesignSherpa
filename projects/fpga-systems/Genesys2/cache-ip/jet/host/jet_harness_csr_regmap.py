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
    'ONYX_MON_CTRL': {
        # onyx's observer, the ocelus mask layers (reference rig REF_CACHE_SEL
        # 4/5; the CSR exists in every selection). Enables are 1 = on, masks
        # bit set = drop. perf_mask bit = event code[3:0]: 0 TXN_START, 2
        # GATHER_DONE, 3 MEM_READ, 4 READ_WASTED, 5 ABSORB, 6 WRITEBACK, 7
        # LOCK_WAIT. Reset 0x007D0007: everything enabled, the six
        # per-transaction classes masked, LOCK_WAIT open -- the MonBus is a
        # low-bandwidth event channel; the host opens what it wants to see.
        'address': '0x038',
        'default': '0x007D0007',
        'name': 'ONYX_MON_CTRL',
        'offset': '0x038',
        'size': 4,
        'sw': 'rw',
        'type': 'reg',
        'mon_enable': {'default': '0x1', 'offset': '0', 'sw': 'rw', 'type': 'field'},
        'error_enable': {'default': '0x1', 'offset': '1', 'sw': 'rw', 'type': 'field'},
        'perf_enable': {'default': '0x1', 'offset': '2', 'sw': 'rw', 'type': 'field'},
        # addr_win_enable: the content filter -- transmit only the events of
        # the transactions inside ONYX_MON_WIN_LOW..HIGH (inclusive)
        'addr_win_enable': {'default': '0x0', 'offset': '3', 'sw': 'rw', 'type': 'field'},
        # port_mask bit p drops the events of requester p: 0 / 1 the caches,
        # 2 the ACE-Lite IO port (onyx TASK-001 step 7); bit 3 unused at N = 2
        'port_mask': {'default': '0x0', 'offset': '7:4', 'sw': 'rw', 'type': 'field'},
        'perf_mask': {'default': '0x007D', 'offset': '31:16', 'sw': 'rw', 'type': 'field'},
    },
    'ONYX_MON_WIN_LOW': {
        # the observer's address window, inclusive low bound (CTRL.addr_win_enable)
        'address': '0x014',
        'default': '0x00000000',
        'name': 'ONYX_MON_WIN_LOW',
        'offset': '0x014',
        'size': 4,
        'sw': 'rw',
        'type': 'reg',
        'value': {'default': '0x00000000', 'offset': '31:0', 'sw': 'rw', 'type': 'field'},
    },
    'ONYX_MON_WIN_HIGH': {
        # the observer's address window, inclusive high bound
        'address': '0x018',
        'default': '0x00000000',
        'name': 'ONYX_MON_WIN_HIGH',
        'offset': '0x018',
        'size': 4,
        'sw': 'rw',
        'type': 'reg',
        'value': {'default': '0x00000000', 'offset': '31:0', 'sw': 'rw', 'type': 'field'},
    },
    'ONYX_MON_MASK': {
        # pkt_mask bit = packet type (4 Perf, 0 Error); error_mask bit = error
        # code[3:0] (9 = the drop report). Reset 0: nothing masked here.
        'address': '0x03C',
        'default': '0x00000000',
        'name': 'ONYX_MON_MASK',
        'offset': '0x03C',
        'size': 4,
        'sw': 'rw',
        'type': 'reg',
        'pkt_mask': {'default': '0x0000', 'offset': '15:0', 'sw': 'rw', 'type': 'field'},
        'error_mask': {'default': '0x0000', 'offset': '31:16', 'sw': 'rw', 'type': 'field'},
    },
    # ------------------------------------------------------------------
    # The IO doorbell (onyx TASK-001 step 7, D1): one single-beat read or
    # write on onyx's ACE-Lite IO port per IO_CTRL.go (REF_CACHE_SEL 4 / 5;
    # IO_STATUS.absent reads 1 elsewhere and nothing moves).  Write IO_ADDR,
    # IO_WDATA_LO/HI, then IO_CTRL with go=1 and the kind; poll IO_STATUS.done;
    # read IO_RDATA_LO/HI.  shareable=1 is ReadOnce / WriteUnique (the caches
    # are snooped), 0 is ReadNoSnoop / WriteNoSnoop (straight to memory).
    # ------------------------------------------------------------------
    'IO_ADDR': {
        'address': '0x040', 'default': '0x00000000', 'name': 'IO_ADDR', 'offset': '0x040',
        'size': 4, 'sw': 'rw', 'type': 'reg',
        'value': {'default': '0x00000000', 'offset': '31:0', 'sw': 'rw', 'type': 'field'},
    },
    'IO_WDATA_LO': {
        'address': '0x044', 'default': '0x00000000', 'name': 'IO_WDATA_LO', 'offset': '0x044',
        'size': 4, 'sw': 'rw', 'type': 'reg',
        'value': {'default': '0x00000000', 'offset': '31:0', 'sw': 'rw', 'type': 'field'},
    },
    'IO_WDATA_HI': {
        'address': '0x048', 'default': '0x00000000', 'name': 'IO_WDATA_HI', 'offset': '0x048',
        'size': 4, 'sw': 'rw', 'type': 'reg',
        'value': {'default': '0x00000000', 'offset': '31:0', 'sw': 'rw', 'type': 'field'},
    },
    'IO_CTRL': {
        # go is write-1-pulse (reads 0); write / shareable / wstrb are levels
        # the doorbell latches at the go
        'address': '0x04C', 'default': '0x00000000', 'name': 'IO_CTRL', 'offset': '0x04C',
        'size': 4, 'sw': 'rw', 'type': 'reg',
        'go': {'default': '0x0', 'offset': '0', 'sw': 'rw', 'type': 'field'},
        'write': {'default': '0x0', 'offset': '1', 'sw': 'rw', 'type': 'field'},
        'shareable': {'default': '0x0', 'offset': '2', 'sw': 'rw', 'type': 'field'},
        'wstrb': {'default': '0x0', 'offset': '15:8', 'sw': 'rw', 'type': 'field'},
    },
    'IO_STATUS': {
        'address': '0x050', 'default': '0x00000000', 'name': 'IO_STATUS', 'offset': '0x050',
        'size': 4, 'sw': 'r', 'type': 'reg',
        'busy': {'default': '0x0', 'offset': '0', 'sw': 'r', 'type': 'field'},
        'done': {'default': '0x0', 'offset': '1', 'sw': 'r', 'type': 'field'},
        'resp': {'default': '0x0', 'offset': '3:2', 'sw': 'r', 'type': 'field'},
        'absent': {'default': '0x0', 'offset': '31', 'sw': 'r', 'type': 'field'},
    },
    'IO_RDATA_LO': {
        'address': '0x054', 'default': '0x00000000', 'name': 'IO_RDATA_LO', 'offset': '0x054',
        'size': 4, 'sw': 'r', 'type': 'reg',
        'value': {'default': '0x00000000', 'offset': '31:0', 'sw': 'r', 'type': 'field'},
    },
    'IO_RDATA_HI': {
        'address': '0x058', 'default': '0x00000000', 'name': 'IO_RDATA_HI', 'offset': '0x058',
        'size': 4, 'sw': 'r', 'type': 'reg',
        'value': {'default': '0x00000000', 'offset': '31:0', 'sw': 'r', 'type': 'field'},
    },
    'ONYX_CNT_CU_DT': {
        # onyx BUG-001's corner (reference rig REF_CACHE_SEL 4/5 only): CleanUnique
        # slots whose gather ended with data -- a killed upgrade's peer passed the
        # line dirty; cleared by CTRL[0], held by CTRL[1]
        'address': '0x05C', 'default': '0x00000000', 'name': 'ONYX_CNT_CU_DT', 'offset': '0x05C',
        'size': 4, 'sw': 'r', 'type': 'reg',
        'value': {'default': '0x00000000', 'offset': '31:0', 'sw': 'r', 'type': 'field'},
    },
    'ONYX_CNT_OLD_WB': {
        # onyx BUG-003's / jet-prime BUG-002's corner (REF_CACHE_SEL 4/5 only): cache
        # writes first presented on a line a slot still gathers (a victim drain a
        # snoop passed on); cleared by CTRL[0], held by CTRL[1]
        'address': '0x060', 'default': '0x00000000', 'name': 'ONYX_CNT_OLD_WB', 'offset': '0x060',
        'size': 4, 'sw': 'r', 'type': 'reg',
        'value': {'default': '0x00000000', 'offset': '31:0', 'sw': 'r', 'type': 'field'},
    },
    'GO': {
        # write-only launch: bit k pulses injector k's start for one cycle,
        # so ONE write starts both injectors in the same harness cycle.  Two
        # CTRL.run writes over the UART bridge land >= 16 ms apart, longer
        # than a whole run (cache-ip common-ip BUG-001).  Reads 0.
        'address': '0x064', 'default': '0x00000000', 'name': 'GO', 'offset': '0x064',
        'size': 4, 'sw': 'w', 'type': 'reg',
        'ci0': {'default': '0x0', 'offset': '0', 'sw': 'w', 'type': 'field'},
        'ci1': {'default': '0x0', 'offset': '1', 'sw': 'w', 'type': 'field'},
    },
}
