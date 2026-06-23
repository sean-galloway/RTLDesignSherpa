# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Test-bench helpers for the DDR2/LPDDR2 APB CSR slave.

Mirrors stream's StreamRegisterMap + write_apb_register / read_apb_register
pattern. Register offsets match rtl/macro/ddr2_lpddr2_csr.rdl and
docs/.../03_csr_map.md.
"""

from __future__ import annotations

from cocotb.triggers import RisingEdge


class DDR2LPDDR2RegisterMap:
    """Named offsets + symbolic field accessors for the CSR map."""

    # Control / Status
    CTRL                  = 0x000
    STATUS                = 0x004
    STATUS_HISTORY        = 0x008

    # Timings
    TIMINGS_RC_RCD_RP_RAS = 0x010
    TIMINGS_RFC_REFI      = 0x014
    TIMINGS_RRD_FAW_WTR_CCD = 0x018
    TIMINGS_CL_CWL_WR     = 0x01C

    # Mode registers
    MR0                   = 0x020
    MR1                   = 0x024
    MR2                   = 0x028
    MR3                   = 0x02C

    # LPDDR2
    PASR_BANK_MASK_RANK0  = 0x030
    PASR_SEG_MASK_RANK0   = 0x034
    TEMP_DERATE_RANK0     = 0x038

    # Tuning
    SCHED_TUNING          = 0x040
    PAGE_PRED_TUNING      = 0x044
    REFRESH_TUNING        = 0x048
    ADDR_MAP_TUNING       = 0x04C
    INIT_TUNING           = 0x050

    # Per-bank obs (rank 0, NUM_BANKS=8)
    OBS_ROW_HIT_BASE      = 0x080
    OBS_REF_LATENCY_BASE  = 0x0C0

    # System obs
    OBS_TXN_QUEUE_DEPTH_MAX  = 0x100
    OBS_TXN_QUEUE_DEPTH_AVG  = 0x104
    OBS_REFRESH_PENDING_MAX  = 0x108
    OBS_REFRESH_DEFER_HIST_0 = 0x10C
    OBS_REFRESH_DEFER_HIST_1 = 0x110
    OBS_REFRESH_DEFER_HIST_2 = 0x114
    OBS_REFRESH_DEFER_HIST_3 = 0x118
    OBS_PAGE_PRED_ACCURACY   = 0x120
    OBS_AXI_R_LATENCY_AVG    = 0x130
    OBS_AXI_R_LATENCY_P99    = 0x134
    OBS_AXI_W_LATENCY_AVG    = 0x138

    # obs_* harvest words (#127 — 9 RO words)
    OBS_WORDS_BASE        = 0x1C0

    # Module ID
    ID                    = 0xFF0
    BUILD                 = 0xFF4

    @classmethod
    def obs_row_hit(cls, bank: int) -> int:
        if not 0 <= bank < 8:
            raise ValueError(f"bank {bank} out of range")
        return cls.OBS_ROW_HIT_BASE + bank * 4

    @classmethod
    def obs_ref_latency(cls, bank: int) -> int:
        if not 0 <= bank < 8:
            raise ValueError(f"bank {bank} out of range")
        return cls.OBS_REF_LATENCY_BASE + bank * 4

    @classmethod
    def obs_word(cls, idx: int) -> int:
        if not 0 <= idx < 9:
            raise ValueError(f"obs_word idx {idx} out of range")
        return cls.OBS_WORDS_BASE + idx * 4

    _NAMED = {
        0x000: "CTRL",
        0x004: "STATUS",
        0x008: "STATUS_HISTORY",
        0x010: "TIMINGS_RC_RCD_RP_RAS",
        0x014: "TIMINGS_RFC_REFI",
        0x018: "TIMINGS_RRD_FAW_WTR_CCD",
        0x01C: "TIMINGS_CL_CWL_WR",
        0x020: "MR0", 0x024: "MR1", 0x028: "MR2", 0x02C: "MR3",
        0x030: "PASR_BANK_MASK_RANK0",
        0x034: "PASR_SEG_MASK_RANK0",
        0x038: "TEMP_DERATE_RANK0",
        0x040: "SCHED_TUNING",
        0x044: "PAGE_PRED_TUNING",
        0x048: "REFRESH_TUNING",
        0x04C: "ADDR_MAP_TUNING",
        0x050: "INIT_TUNING",
        0xFF0: "ID", 0xFF4: "BUILD",
    }

    @classmethod
    def name(cls, addr: int) -> str:
        if addr in cls._NAMED:
            return cls._NAMED[addr]
        if cls.OBS_ROW_HIT_BASE <= addr < cls.OBS_ROW_HIT_BASE + 32:
            return f"OBS_ROW_HIT_BANK{(addr - cls.OBS_ROW_HIT_BASE) // 4}"
        if cls.OBS_REF_LATENCY_BASE <= addr < cls.OBS_REF_LATENCY_BASE + 32:
            return f"OBS_REF_LATENCY_BANK{(addr - cls.OBS_REF_LATENCY_BASE) // 4}"
        if cls.OBS_WORDS_BASE <= addr < cls.OBS_WORDS_BASE + 36:
            return f"OBS_WORD{(addr - cls.OBS_WORDS_BASE) // 4}"
        return f"UNKNOWN_0x{addr:03X}"


# Convenience field encoders / decoders for packed timing / tuning regs.

def encode_sched_tuning(lookahead: int = 0, force_inorder: bool = False,
                        happy_enable: bool = True, age_max_runtime: int = 0,
                        txn_queue_high_water: int = 0) -> int:
    """Pack the SCHED_TUNING register fields."""
    return (
        (lookahead & 0xF) |
        ((1 if force_inorder else 0) << 4) |
        ((1 if happy_enable else 0) << 5) |
        ((age_max_runtime & 0xFF) << 8) |
        ((txn_queue_high_water & 0xFF) << 16)
    )


def encode_refresh_tuning(refpb_policy_or: int = 0, page_policy_or: int = 0,
                          refresh_defer_active: int = 1,
                          zqcs_freq_hz: int = 1) -> int:
    """Pack the REFRESH_TUNING register fields."""
    return (
        (refpb_policy_or & 0x3) |
        ((page_policy_or & 0x3) << 2) |
        ((refresh_defer_active & 0xF) << 4) |
        ((zqcs_freq_hz & 0xFFFF) << 16)
    )


async def apb_write(dut, clock, addr: int, data: int, *,
                    strb: int = 0xF) -> None:
    """One APB write transaction (no BFM — raw signal sequence)."""
    await RisingEdge(clock)
    dut.s_apb_PSEL.value    = 1
    dut.s_apb_PENABLE.value = 0
    dut.s_apb_PADDR.value   = addr
    dut.s_apb_PWRITE.value  = 1
    dut.s_apb_PWDATA.value  = data
    dut.s_apb_PSTRB.value   = strb
    dut.s_apb_PPROT.value   = 0
    await RisingEdge(clock)
    dut.s_apb_PENABLE.value = 1
    for _ in range(400):
        await RisingEdge(clock)
        if int(dut.s_apb_PREADY.value) == 1:
            dut.s_apb_PSEL.value    = 0
            dut.s_apb_PENABLE.value = 0
            return
    raise AssertionError(f"APB write to 0x{addr:03X} timed out")


async def apb_read(dut, clock, addr: int) -> tuple[int, int]:
    """One APB read transaction. Returns (prdata, pslverr)."""
    await RisingEdge(clock)
    dut.s_apb_PSEL.value    = 1
    dut.s_apb_PENABLE.value = 0
    dut.s_apb_PADDR.value   = addr
    dut.s_apb_PWRITE.value  = 0
    dut.s_apb_PSTRB.value   = 0
    dut.s_apb_PPROT.value   = 0
    await RisingEdge(clock)
    dut.s_apb_PENABLE.value = 1
    for _ in range(400):
        await RisingEdge(clock)
        if int(dut.s_apb_PREADY.value) == 1:
            rdata = int(dut.s_apb_PRDATA.value)
            err   = int(dut.s_apb_PSLVERR.value)
            dut.s_apb_PSEL.value    = 0
            dut.s_apb_PENABLE.value = 0
            return rdata, err
    raise AssertionError(f"APB read from 0x{addr:03X} timed out")
