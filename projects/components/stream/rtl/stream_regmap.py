# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Complete register map for STREAM DMA engine
# Matches stream_regs.rdl + apbtodescr channel kick-off registers
# Compatible with: bin/CocoTBFramework/tbclasses/apb/register_map.py

"""
STREAM DMA Engine Register Map

Complete register definitions for stream_top testbench configuration.
This file matches the PeakRDL-generated registers from stream_regs.rdl,
plus the channel kick-off registers handled by apbtodescr.sv.

Format follows HPET register map pattern for compatibility with
CocoTBFramework RegisterMap class.

Address Space:
  0x000-0x03F: Channel kick-off registers (apbtodescr.sv)
  0x100-0x2BF: Configuration and status (stream_regs.rdl)

Usage:
    from stream_regmap import top_block
    reg_map = RegisterMap('stream_regmap.py', apb_data_width=32,
                          apb_addr_width=12, start_address=0x0, log=logger)
"""

top_block = {
    # =========================================================================
    # Channel Kick-off Registers (0x000 - 0x03F)
    # These are handled by apbtodescr.sv, not PeakRDL
    # 8 channels x 2 registers (LOW/HIGH) = 16 registers
    # =========================================================================

    'CH0_CTRL_LOW': {
        'address': '0x000',
        'default': '0x00000000',
        'type': 'reg',
        'size': 4,
        'sw': 'wo',
        'name': 'CH0_CTRL_LOW',
        'DESC_ADDR_LOW': {'offset': '31:0', 'default': '0x0', 'sw': 'wo', 'type': 'field'}
    },
    'CH0_CTRL_HIGH': {
        'address': '0x004',
        'default': '0x00000000',
        'type': 'reg',
        'size': 4,
        'sw': 'wo',
        'name': 'CH0_CTRL_HIGH',
        'DESC_ADDR_HIGH': {'offset': '31:0', 'default': '0x0', 'sw': 'wo', 'type': 'field'}
    },
    'CH1_CTRL_LOW': {
        'address': '0x008',
        'default': '0x00000000',
        'type': 'reg',
        'size': 4,
        'sw': 'wo',
        'name': 'CH1_CTRL_LOW',
        'DESC_ADDR_LOW': {'offset': '31:0', 'default': '0x0', 'sw': 'wo', 'type': 'field'}
    },
    'CH1_CTRL_HIGH': {
        'address': '0x00C',
        'default': '0x00000000',
        'type': 'reg',
        'size': 4,
        'sw': 'wo',
        'name': 'CH1_CTRL_HIGH',
        'DESC_ADDR_HIGH': {'offset': '31:0', 'default': '0x0', 'sw': 'wo', 'type': 'field'}
    },
    'CH2_CTRL_LOW': {
        'address': '0x010',
        'default': '0x00000000',
        'type': 'reg',
        'size': 4,
        'sw': 'wo',
        'name': 'CH2_CTRL_LOW',
        'DESC_ADDR_LOW': {'offset': '31:0', 'default': '0x0', 'sw': 'wo', 'type': 'field'}
    },
    'CH2_CTRL_HIGH': {
        'address': '0x014',
        'default': '0x00000000',
        'type': 'reg',
        'size': 4,
        'sw': 'wo',
        'name': 'CH2_CTRL_HIGH',
        'DESC_ADDR_HIGH': {'offset': '31:0', 'default': '0x0', 'sw': 'wo', 'type': 'field'}
    },
    'CH3_CTRL_LOW': {
        'address': '0x018',
        'default': '0x00000000',
        'type': 'reg',
        'size': 4,
        'sw': 'wo',
        'name': 'CH3_CTRL_LOW',
        'DESC_ADDR_LOW': {'offset': '31:0', 'default': '0x0', 'sw': 'wo', 'type': 'field'}
    },
    'CH3_CTRL_HIGH': {
        'address': '0x01C',
        'default': '0x00000000',
        'type': 'reg',
        'size': 4,
        'sw': 'wo',
        'name': 'CH3_CTRL_HIGH',
        'DESC_ADDR_HIGH': {'offset': '31:0', 'default': '0x0', 'sw': 'wo', 'type': 'field'}
    },
    'CH4_CTRL_LOW': {
        'address': '0x020',
        'default': '0x00000000',
        'type': 'reg',
        'size': 4,
        'sw': 'wo',
        'name': 'CH4_CTRL_LOW',
        'DESC_ADDR_LOW': {'offset': '31:0', 'default': '0x0', 'sw': 'wo', 'type': 'field'}
    },
    'CH4_CTRL_HIGH': {
        'address': '0x024',
        'default': '0x00000000',
        'type': 'reg',
        'size': 4,
        'sw': 'wo',
        'name': 'CH4_CTRL_HIGH',
        'DESC_ADDR_HIGH': {'offset': '31:0', 'default': '0x0', 'sw': 'wo', 'type': 'field'}
    },
    'CH5_CTRL_LOW': {
        'address': '0x028',
        'default': '0x00000000',
        'type': 'reg',
        'size': 4,
        'sw': 'wo',
        'name': 'CH5_CTRL_LOW',
        'DESC_ADDR_LOW': {'offset': '31:0', 'default': '0x0', 'sw': 'wo', 'type': 'field'}
    },
    'CH5_CTRL_HIGH': {
        'address': '0x02C',
        'default': '0x00000000',
        'type': 'reg',
        'size': 4,
        'sw': 'wo',
        'name': 'CH5_CTRL_HIGH',
        'DESC_ADDR_HIGH': {'offset': '31:0', 'default': '0x0', 'sw': 'wo', 'type': 'field'}
    },
    'CH6_CTRL_LOW': {
        'address': '0x030',
        'default': '0x00000000',
        'type': 'reg',
        'size': 4,
        'sw': 'wo',
        'name': 'CH6_CTRL_LOW',
        'DESC_ADDR_LOW': {'offset': '31:0', 'default': '0x0', 'sw': 'wo', 'type': 'field'}
    },
    'CH6_CTRL_HIGH': {
        'address': '0x034',
        'default': '0x00000000',
        'type': 'reg',
        'size': 4,
        'sw': 'wo',
        'name': 'CH6_CTRL_HIGH',
        'DESC_ADDR_HIGH': {'offset': '31:0', 'default': '0x0', 'sw': 'wo', 'type': 'field'}
    },
    'CH7_CTRL_LOW': {
        'address': '0x038',
        'default': '0x00000000',
        'type': 'reg',
        'size': 4,
        'sw': 'wo',
        'name': 'CH7_CTRL_LOW',
        'DESC_ADDR_LOW': {'offset': '31:0', 'default': '0x0', 'sw': 'wo', 'type': 'field'}
    },
    'CH7_CTRL_HIGH': {
        'address': '0x03C',
        'default': '0x00000000',
        'type': 'reg',
        'size': 4,
        'sw': 'wo',
        'name': 'CH7_CTRL_HIGH',
        'DESC_ADDR_HIGH': {'offset': '31:0', 'default': '0x0', 'sw': 'wo', 'type': 'field'}
    },

    # =========================================================================
    # Global Control and Status (0x100 - 0x11F)
    # =========================================================================

    'GLOBAL_CTRL': {
        'address': '0x100',
        'default': '0x00000000',
        'type': 'reg',
        'size': 4,
        'sw': 'rw',
        'name': 'GLOBAL_CTRL',
        'GLOBAL_EN': {'offset': '0', 'default': '0x0', 'sw': 'rw', 'type': 'field'},
        'GLOBAL_RST': {'offset': '1', 'default': '0x0', 'sw': 'rw', 'type': 'field'}
    },
    'GLOBAL_STATUS': {
        'address': '0x104',
        'default': '0x00000000',
        'type': 'reg',
        'size': 4,
        'sw': 'r',
        'name': 'GLOBAL_STATUS',
        'SYSTEM_IDLE': {'offset': '0', 'default': '0x0', 'sw': 'r', 'type': 'field'}
    },
    'VERSION': {
        'address': '0x108',
        'default': '0x0008005A',
        'type': 'reg',
        'size': 4,
        'sw': 'r',
        'name': 'VERSION',
        'MINOR': {'offset': '7:0', 'default': '0x5A', 'sw': 'r', 'type': 'field'},
        'MAJOR': {'offset': '15:8', 'default': '0x00', 'sw': 'r', 'type': 'field'},
        'NUM_CHANNELS': {'offset': '23:16', 'default': '0x08', 'sw': 'r', 'type': 'field'}
    },

    # =========================================================================
    # Per-Channel Control (0x120 - 0x13F)
    # =========================================================================

    'CHANNEL_ENABLE': {
        'address': '0x120',
        'default': '0x00000000',
        'type': 'reg',
        'size': 4,
        'sw': 'rw',
        'name': 'CHANNEL_ENABLE',
        'CH_EN': {'offset': '7:0', 'default': '0x00', 'sw': 'rw', 'type': 'field'}
    },
    'CHANNEL_RESET': {
        'address': '0x124',
        'default': '0x00000000',
        'type': 'reg',
        'size': 4,
        'sw': 'rw',
        'name': 'CHANNEL_RESET',
        'CH_RST': {'offset': '7:0', 'default': '0x00', 'sw': 'rw', 'type': 'field'}
    },

    # =========================================================================
    # Per-Channel Status (0x140 - 0x17F)
    # =========================================================================

    'CHANNEL_IDLE': {
        'address': '0x140',
        'default': '0x00000000',
        'type': 'reg',
        'size': 4,
        'sw': 'r',
        'name': 'CHANNEL_IDLE',
        'CH_IDLE': {'offset': '7:0', 'default': '0x00', 'sw': 'r', 'type': 'field'}
    },
    'DESC_ENGINE_IDLE': {
        'address': '0x144',
        'default': '0x00000000',
        'type': 'reg',
        'size': 4,
        'sw': 'r',
        'name': 'DESC_ENGINE_IDLE',
        'DESC_IDLE': {'offset': '7:0', 'default': '0x00', 'sw': 'r', 'type': 'field'}
    },
    'SCHEDULER_IDLE': {
        'address': '0x148',
        'default': '0x00000000',
        'type': 'reg',
        'size': 4,
        'sw': 'r',
        'name': 'SCHEDULER_IDLE',
        'SCHED_IDLE': {'offset': '7:0', 'default': '0x00', 'sw': 'r', 'type': 'field'}
    },

    # Per-channel state registers (0x150-0x16F)
    'CH0_STATE': {'address': '0x150', 'default': '0x00000000', 'type': 'reg', 'size': 4, 'sw': 'r', 'name': 'CH0_STATE', 'array_index': 0, 'array_name': 'CH_STATE', 'STATE': {'offset': '6:0', 'default': '0x00', 'sw': 'r', 'type': 'field'}},
    'CH1_STATE': {'address': '0x154', 'default': '0x00000000', 'type': 'reg', 'size': 4, 'sw': 'r', 'name': 'CH1_STATE', 'array_index': 1, 'array_name': 'CH_STATE', 'STATE': {'offset': '6:0', 'default': '0x00', 'sw': 'r', 'type': 'field'}},
    'CH2_STATE': {'address': '0x158', 'default': '0x00000000', 'type': 'reg', 'size': 4, 'sw': 'r', 'name': 'CH2_STATE', 'array_index': 2, 'array_name': 'CH_STATE', 'STATE': {'offset': '6:0', 'default': '0x00', 'sw': 'r', 'type': 'field'}},
    'CH3_STATE': {'address': '0x15C', 'default': '0x00000000', 'type': 'reg', 'size': 4, 'sw': 'r', 'name': 'CH3_STATE', 'array_index': 3, 'array_name': 'CH_STATE', 'STATE': {'offset': '6:0', 'default': '0x00', 'sw': 'r', 'type': 'field'}},
    'CH4_STATE': {'address': '0x160', 'default': '0x00000000', 'type': 'reg', 'size': 4, 'sw': 'r', 'name': 'CH4_STATE', 'array_index': 4, 'array_name': 'CH_STATE', 'STATE': {'offset': '6:0', 'default': '0x00', 'sw': 'r', 'type': 'field'}},
    'CH5_STATE': {'address': '0x164', 'default': '0x00000000', 'type': 'reg', 'size': 4, 'sw': 'r', 'name': 'CH5_STATE', 'array_index': 5, 'array_name': 'CH_STATE', 'STATE': {'offset': '6:0', 'default': '0x00', 'sw': 'r', 'type': 'field'}},
    'CH6_STATE': {'address': '0x168', 'default': '0x00000000', 'type': 'reg', 'size': 4, 'sw': 'r', 'name': 'CH6_STATE', 'array_index': 6, 'array_name': 'CH_STATE', 'STATE': {'offset': '6:0', 'default': '0x00', 'sw': 'r', 'type': 'field'}},
    'CH7_STATE': {'address': '0x16C', 'default': '0x00000000', 'type': 'reg', 'size': 4, 'sw': 'r', 'name': 'CH7_STATE', 'array_index': 7, 'array_name': 'CH_STATE', 'STATE': {'offset': '6:0', 'default': '0x00', 'sw': 'r', 'type': 'field'}},

    # =========================================================================
    # Engine Completion and Error Status (0x170 - 0x17F)
    # =========================================================================

    'SCHED_ERROR': {
        'address': '0x170',
        'default': '0x00000000',
        'type': 'reg',
        'size': 4,
        'sw': 'r',
        'name': 'SCHED_ERROR',
        'SCHED_ERR': {'offset': '7:0', 'default': '0x00', 'sw': 'r', 'type': 'field'}
    },
    'AXI_RD_COMPLETE': {
        'address': '0x174',
        'default': '0x00000000',
        'type': 'reg',
        'size': 4,
        'sw': 'r',
        'name': 'AXI_RD_COMPLETE',
        'RD_COMPLETE': {'offset': '7:0', 'default': '0x00', 'sw': 'r', 'type': 'field'}
    },
    'AXI_WR_COMPLETE': {
        'address': '0x178',
        'default': '0x00000000',
        'type': 'reg',
        'size': 4,
        'sw': 'r',
        'name': 'AXI_WR_COMPLETE',
        'WR_COMPLETE': {'offset': '7:0', 'default': '0x00', 'sw': 'r', 'type': 'field'}
    },

    # =========================================================================
    # Monitor FIFO Status (0x180 - 0x18F)
    # =========================================================================

    'MON_FIFO_STATUS': {
        'address': '0x180',
        'default': '0x00000000',
        'type': 'reg',
        'size': 4,
        'sw': 'r',
        'name': 'MON_FIFO_STATUS',
        'MON_FIFO_FULL': {'offset': '0', 'default': '0x0', 'sw': 'r', 'type': 'field'},
        'MON_FIFO_EMPTY': {'offset': '1', 'default': '0x0', 'sw': 'r', 'type': 'field'},
        'MON_FIFO_OVFL': {'offset': '2', 'default': '0x0', 'sw': 'r', 'type': 'field'},
        'MON_FIFO_UNFL': {'offset': '3', 'default': '0x0', 'sw': 'r', 'type': 'field'}
    },
    'MON_FIFO_COUNT': {
        'address': '0x184',
        'default': '0x00000000',
        'type': 'reg',
        'size': 4,
        'sw': 'r',
        'name': 'MON_FIFO_COUNT',
        'FIFO_COUNT': {'offset': '15:0', 'default': '0x0000', 'sw': 'r', 'type': 'field'}
    },

    # =========================================================================
    # Scheduler Configuration (0x200 - 0x21F)
    # =========================================================================

    'SCHED_TIMEOUT_CYCLES': {
        'address': '0x200',
        'default': '0x000003E8',
        'type': 'reg',
        'size': 4,
        'sw': 'rw',
        'name': 'SCHED_TIMEOUT_CYCLES',
        'TIMEOUT_CYCLES': {'offset': '15:0', 'default': '0x03E8', 'sw': 'rw', 'type': 'field'}
    },
    'SCHED_CONFIG': {
        'address': '0x204',
        'default': '0x0000000F',
        'type': 'reg',
        'size': 4,
        'sw': 'rw',
        'name': 'SCHED_CONFIG',
        'SCHED_EN': {'offset': '0', 'default': '0x1', 'sw': 'rw', 'type': 'field'},
        'TIMEOUT_EN': {'offset': '1', 'default': '0x1', 'sw': 'rw', 'type': 'field'},
        'ERR_EN': {'offset': '2', 'default': '0x1', 'sw': 'rw', 'type': 'field'},
        'COMPL_EN': {'offset': '3', 'default': '0x1', 'sw': 'rw', 'type': 'field'},
        'PERF_EN': {'offset': '4', 'default': '0x0', 'sw': 'rw', 'type': 'field'}
    },

    # =========================================================================
    # Descriptor Engine Configuration (0x220 - 0x23F)
    # =========================================================================

    'DESCENG_CONFIG': {
        'address': '0x220',
        'default': '0x00000021',
        'type': 'reg',
        'size': 4,
        'sw': 'rw',
        'name': 'DESCENG_CONFIG',
        'DESCENG_EN': {'offset': '0', 'default': '0x1', 'sw': 'rw', 'type': 'field'},
        'PREFETCH_EN': {'offset': '1', 'default': '0x0', 'sw': 'rw', 'type': 'field'},
        'FIFO_THRESH': {'offset': '5:2', 'default': '0x8', 'sw': 'rw', 'type': 'field'}
    },
    'DESCENG_ADDR0_BASE': {
        'address': '0x224',
        'default': '0x00000000',
        'type': 'reg',
        'size': 4,
        'sw': 'rw',
        'name': 'DESCENG_ADDR0_BASE',
        'ADDR0_BASE': {'offset': '31:0', 'default': '0x00000000', 'sw': 'rw', 'type': 'field'}
    },
    'DESCENG_ADDR0_LIMIT': {
        'address': '0x228',
        'default': '0xFFFFFFFF',
        'type': 'reg',
        'size': 4,
        'sw': 'rw',
        'name': 'DESCENG_ADDR0_LIMIT',
        'ADDR0_LIMIT': {'offset': '31:0', 'default': '0xFFFFFFFF', 'sw': 'rw', 'type': 'field'}
    },
    'DESCENG_ADDR1_BASE': {
        'address': '0x22C',
        'default': '0x00000000',
        'type': 'reg',
        'size': 4,
        'sw': 'rw',
        'name': 'DESCENG_ADDR1_BASE',
        'ADDR1_BASE': {'offset': '31:0', 'default': '0x00000000', 'sw': 'rw', 'type': 'field'}
    },
    'DESCENG_ADDR1_LIMIT': {
        'address': '0x230',
        'default': '0xFFFFFFFF',
        'type': 'reg',
        'size': 4,
        'sw': 'rw',
        'name': 'DESCENG_ADDR1_LIMIT',
        'ADDR1_LIMIT': {'offset': '31:0', 'default': '0xFFFFFFFF', 'sw': 'rw', 'type': 'field'}
    },

    # =========================================================================
    # AXI Transfer Configuration (0x2A0 - 0x2AF)
    # =========================================================================

    'AXI_XFER_CONFIG': {
        'address': '0x2A0',
        'default': '0x00000F0F',
        'type': 'reg',
        'size': 4,
        'sw': 'rw',
        'name': 'AXI_XFER_CONFIG',
        'RD_XFER_BEATS': {'offset': '7:0', 'default': '0x0F', 'sw': 'rw', 'type': 'field'},
        'WR_XFER_BEATS': {'offset': '15:8', 'default': '0x0F', 'sw': 'rw', 'type': 'field'}
    },

    # =========================================================================
    # Performance Profiler Configuration (0x2B0 - 0x2BF)
    # =========================================================================

    'PERF_CONFIG': {
        'address': '0x2B0',
        'default': '0x00000000',
        'type': 'reg',
        'size': 4,
        'sw': 'rw',
        'name': 'PERF_CONFIG',
        'PERF_EN': {'offset': '0', 'default': '0x0', 'sw': 'rw', 'type': 'field'},
        'PERF_MODE': {'offset': '1', 'default': '0x0', 'sw': 'rw', 'type': 'field'},
        'PERF_CLEAR': {'offset': '2', 'default': '0x0', 'sw': 'rw', 'type': 'field'}
    },
}


# =========================================================================
# Helper Functions (for compatibility with existing code)
# =========================================================================

def get_ch_ctrl_low_addr(channel: int) -> int:
    """Get channel control low register address (kick-off)."""
    return 0x000 + (channel * 0x008)


def get_ch_ctrl_high_addr(channel: int) -> int:
    """Get channel control high register address (kick-off)."""
    return 0x004 + (channel * 0x008)


def get_ch_state_addr(channel: int) -> int:
    """Get channel state register address."""
    return 0x150 + (channel * 0x004)


# Address constants (for direct use)
ADDR_GLOBAL_CTRL = 0x100
ADDR_GLOBAL_STATUS = 0x104
ADDR_VERSION = 0x108
ADDR_CHANNEL_ENABLE = 0x120
ADDR_CHANNEL_RESET = 0x124
ADDR_CHANNEL_IDLE = 0x140
ADDR_DESC_ENGINE_IDLE = 0x144
ADDR_SCHEDULER_IDLE = 0x148
ADDR_SCHED_ERROR = 0x170
ADDR_AXI_RD_COMPLETE = 0x174
ADDR_AXI_WR_COMPLETE = 0x178
ADDR_SCHED_TIMEOUT_CYCLES = 0x200
ADDR_SCHED_CONFIG = 0x204
ADDR_DESCENG_CONFIG = 0x220
ADDR_DESCENG_ADDR0_BASE = 0x224
ADDR_DESCENG_ADDR0_LIMIT = 0x228
ADDR_DESCENG_ADDR1_BASE = 0x22C
ADDR_DESCENG_ADDR1_LIMIT = 0x230
ADDR_MON_FIFO_STATUS = 0x180
ADDR_MON_FIFO_COUNT = 0x184
ADDR_AXI_XFER_CONFIG = 0x2A0
ADDR_PERF_CONFIG = 0x2B0
