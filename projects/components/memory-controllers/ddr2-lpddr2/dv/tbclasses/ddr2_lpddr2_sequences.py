# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Shared AXI4Sequence builders for the ddr2-lpddr2 envs.

Every test that pipelines AXI traffic at the core_macro or top level
should build its sequences here, not inline. The point of the
sequence API is reuse — bad patterns spread across files defeat it.

Builders return (wr_seq, rd_seq, expected) triples. The caller hands
each sequence to `run_axi4_sequence(...)` with the appropriate master.
`expected` is the per-burst list of expected beat values; compare the
read results' "data" field against it.

NEVER bypass these helpers by firing N parallel
cocotb.start_soon(read_transaction) tasks. The BFM's sequence path
dispatches ARs back-to-back as arready allows; concurrent tasks
create per-id deque contention and are not how engine RTL traffic
looks on the bus.
"""

from __future__ import annotations

from typing import Callable, List, Optional, Sequence, Tuple

from CocoTBFramework.components.axi4.axi4_sequence import (
    AXI4Sequence,
)


def _default_payload(bi: int, ki: int) -> int:
    """burst<<16 | beat — uniquely diagnosable if a beat lands at the
    wrong burst index."""
    return ((bi & 0xFFFF) << 16) | (ki & 0xFFFF)


def build_b2b_wr_rd_sequences(
    *,
    n_bursts: int,
    burst_len: int,
    base_addr: int,
    data_width: int,
    wr_axid_fn: Callable[[int], int] = lambda bi: 0,
    rd_axid_fn: Optional[Callable[[int], int]] = None,
    rd_axid: int = 0,
    payload_fn: Optional[Callable[[int, int], int]] = None,
    name: str = "b2b",
) -> Tuple[AXI4Sequence, AXI4Sequence, List[List[int]]]:
    """Standard pipelined-AW + pipelined-AR pattern.

    Writes burst N to addr base+N*stride with `burst_len` beats of
    payload_fn(N, k). Then reads the same addresses back. AR/AW
    pacing is whatever the BFM's randomizer profile is set to.

    Defaults model the engine-mirror behavior: all writes use the
    same id (= wr_axid_fn(bi) returning 0 by default), all reads use
    id=0. Override `wr_axid_fn` to e.g. `lambda bi: bi & 0xF` for the
    mixed-id "truly pipelined" pattern.

    Args:
        n_bursts:    number of AXI bursts per direction.
        burst_len:   beats per burst (= AXI4 burst length, max 256).
        base_addr:   address of burst 0.
        data_width:  AXI data bus width in bits (e.g. 64).
        wr_axid_fn:  AWID picker per burst index. Default: all id=0.
        rd_axid_fn:  ARID picker per burst index. Overrides rd_axid.
        rd_axid:     ARID for every read (used iff rd_axid_fn is None).
        payload_fn:  beat-value picker (bi, ki) -> int. Default:
                     bi<<16 | ki — uniquely diagnosable.
        name:        sequence name prefix for log lines.

    Returns:
        (wr_seq, rd_seq, expected) — caller does:
            await run_axi4_sequence(wr_seq, master_wr=tb.axi_master_wr)
            # wait for B drain
            rd_dicts = await run_axi4_sequence(
                rd_seq, master_rd=tb.axi_master_rd)
            results = [d["data"] for d in rd_dicts]
            assert results == expected
    """
    if payload_fn is None:
        payload_fn = _default_payload

    stride = burst_len * (data_width // 8)

    wr_seq = AXI4Sequence(f"{name}_wr", data_width=data_width)
    for bi in range(n_bursts):
        wr_seq.add_write(
            base_addr + bi * stride,
            data=[payload_fn(bi, ki) for ki in range(burst_len)],
            axid=wr_axid_fn(bi),
        )

    rd_seq = AXI4Sequence(f"{name}_rd", data_width=data_width)
    rd_pick = rd_axid_fn if rd_axid_fn is not None else (lambda bi: rd_axid)
    for bi in range(n_bursts):
        rd_seq.add_read(
            base_addr + bi * stride,
            length=burst_len,
            axid=rd_pick(bi),
        )

    expected: List[List[int]] = [
        [payload_fn(bi, ki) for ki in range(burst_len)]
        for bi in range(n_bursts)
    ]
    return wr_seq, rd_seq, expected


def build_rd_only_sequence(
    *,
    n_bursts: int,
    burst_len: int,
    base_addr: int,
    data_width: int,
    rd_axid_fn: Optional[Callable[[int], int]] = None,
    rd_axid: int = 0,
    payload_fn: Optional[Callable[[int, int], int]] = None,
    name: str = "rd_only",
) -> Tuple[AXI4Sequence, List[List[int]]]:
    """Read-only variant of build_b2b_wr_rd_sequences.

    For scenarios that preload memory directly (e.g.
    `tb.preload_memory(...)` against the DFI slave PHY's MemoryModel)
    so the AXI write path is skipped. Returns (rd_seq, expected) — the
    expected payload table assumes the same `payload_fn(bi, ki)` was
    used when preloading.
    """
    if payload_fn is None:
        payload_fn = _default_payload

    stride = burst_len * (data_width // 8)
    rd_seq = AXI4Sequence(f"{name}_rd", data_width=data_width)
    rd_pick = rd_axid_fn if rd_axid_fn is not None else (lambda bi: rd_axid)
    for bi in range(n_bursts):
        rd_seq.add_read(
            base_addr + bi * stride,
            length=burst_len,
            axid=rd_pick(bi),
        )
    expected: List[List[int]] = [
        [payload_fn(bi, ki) for ki in range(burst_len)]
        for bi in range(n_bursts)
    ]
    return rd_seq, expected


def build_addr_pattern_sequences(
    *,
    burst_len: int,
    data_width: int,
    addresses: List[int],
    wr_axid_fn: Callable[[int], int] = lambda bi: 0,
    rd_axid_fn: Optional[Callable[[int], int]] = None,
    rd_axid: int = 0,
    payload_fn: Optional[Callable[[int, int], int]] = None,
    name: str = "addr_pattern",
) -> Tuple[AXI4Sequence, AXI4Sequence, List[List[int]]]:
    """Like build_b2b_wr_rd_sequences, but takes an explicit per-burst
    address list instead of `base + bi * stride`. Lets pathological
    scenarios drive same-bank / same-row / cross-bank / hit-then-miss
    address patterns that a fixed stride can't express.

    ROW_MAJOR mapping (default) for 64-bit data / 8 banks / 14 row bits:
      * bank stride = 0x2000  (8 KB)
      * row stride  = 0x10000 (64 KB)

    So addresses [0x10000, 0x20000, 0x30000, ...] hit bank 0 at
    sequential rows (same-bank different-row hazard). Addresses
    [0x10000, 0x12000, 0x14000, ...] hit sequential banks at same
    row 1 (bank-parallel-friendly).
    """
    if payload_fn is None:
        payload_fn = _default_payload

    wr_seq = AXI4Sequence(f"{name}_wr", data_width=data_width)
    for bi, addr in enumerate(addresses):
        wr_seq.add_write(
            addr,
            data=[payload_fn(bi, ki) for ki in range(burst_len)],
            axid=wr_axid_fn(bi),
        )

    rd_seq = AXI4Sequence(f"{name}_rd", data_width=data_width)
    rd_pick = rd_axid_fn if rd_axid_fn is not None else (lambda bi: rd_axid)
    for bi, addr in enumerate(addresses):
        rd_seq.add_read(addr, length=burst_len, axid=rd_pick(bi))

    expected: List[List[int]] = [
        [payload_fn(bi, ki) for ki in range(burst_len)]
        for bi in range(len(addresses))
    ]
    return wr_seq, rd_seq, expected


def build_patho_addresses(
    kind: str, *, burst_len: int, base_addr: int = 0x10000
) -> List[int]:
    """Address-list constructor for the D-2 pathological patterns.

    Shared between core_macro and the macro top env so the scenarios
    exercise the same stress. Row-major mapping (default for both
    envs) with 64-bit data / 8 banks / 14 row bits / 10 col bits:
      * byte offset [2:0]
      * col         [12:3]  → col stride  = 0x8      (8 B)
      * bank        [15:13] → bank stride = 0x2000   (8 KB)
      * row         [29:16] → row stride  = 0x10000  (64 KB)

    Kinds:
      bank_hazard          — 16 bursts, all bank 0, sequential rows.
      page_miss_sustained  — 24 bursts ping-ponging 3 rows on bank 0.
      page_close_boundary  — miss + 5 rapid same-row hits × 4 clusters.
      hit_miss_oscillation — 5 hits → 3 misses × 4 cycles. Induces
                             internal burst-pause behavior in the
                             scheduler / bank timers even when AXI
                             is backtoback (novel stress class).
    """
    ROW_STRIDE = 0x10000
    if kind == "bank_hazard":
        return [base_addr + bi * ROW_STRIDE for bi in range(16)]
    if kind == "page_miss_sustained":
        rows = [1, 2, 3]
        return [base_addr + rows[bi % 3] * ROW_STRIDE for bi in range(24)]
    if kind == "page_close_boundary":
        addresses: List[int] = []
        row = 1
        for _cluster in range(4):
            row_base = base_addr + row * ROW_STRIDE
            # 1 miss (opens row), 5 hits (same row, walking columns).
            addresses.append(row_base)
            for hit_i in range(5):
                addresses.append(row_base + (hit_i + 1) * burst_len * 8)
            row += 1
        return addresses
    if kind == "hit_miss_oscillation":
        addresses = []
        row = 1
        for _cycle in range(4):
            # 5 hits on `row`
            row_base = base_addr + row * ROW_STRIDE
            for h in range(5):
                addresses.append(row_base + h * burst_len * 8)
            # 3 misses: fresh rows
            for _m in range(3):
                row += 1
                addresses.append(base_addr + row * ROW_STRIDE)
            row += 1
        return addresses
    raise ValueError(f"Unknown patho kind: {kind}")


def diff_results(
    expected: List[List[int]],
    results: Sequence[Sequence[int]],
) -> Optional[Tuple[int, int, int, int]]:
    """Compare per-burst beat lists. Returns first mismatch as
    (burst_idx, beat_idx, expected_val, actual_val) or None if all
    match. Caller assert-formats."""
    for bi, exp_beats in enumerate(expected):
        if bi >= len(results):
            return (bi, 0, exp_beats[0], -1)
        for ki, exp in enumerate(exp_beats):
            if ki >= len(results[bi]):
                return (bi, ki, exp, -1)
            if results[bi][ki] != exp:
                return (bi, ki, exp, results[bi][ki])
    return None
