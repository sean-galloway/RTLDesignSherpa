# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""The monbus tally (monbus_tally_axil): CAM programming and dense-bin readout.

Register-based CAM load, bus-width independent: CAM_CLEAR invalidates every
entry, CAM_KEY holds the next key, CAM_LOAD = {valid<<31 | index} loads it.
Dense bins read back on the count port at BIN_STRIDE (one 32-bit count per
64-bit word); a packet whose tuple is in no entry lands in the UNEXPECTED bin,
whose index equals the CAM depth.

Offsets are resolved from tally_regs (projects/components/misc/rtl/tally_regs.rdl),
the block that generates the decode -- they were literals in seven host
programs and localparams in the RTL. The CAM depth is read from HARDWARE:
build-obs ships a 32-entry CAM while every host constant said 64, so the
"unexpected" figure was read from a bin that does not exist.

Runs INSIDE the board's program: `program_cam` belongs in the `pre_kick` hook
of `CharacterizationRunner.run_config`, because the tally sits on the
unit_aresetn line the runner's reset_stream() pulses and a CAM loaded before
that is gone by the time the DMA runs.
"""
from __future__ import annotations

import contextlib
import io
import logging
import os
from typing import Dict, Iterable, List, Sequence, Tuple

from TBClasses.apb.register_map import RegisterMap

import stream_env  # noqa: F401  (path setup; repo_root())

_REGMAP_REL = "projects/components/misc/rtl/regs/generated/tally_regs_top_regmap.py"
_REGS = None


def _regs() -> RegisterMap:
    global _REGS
    if _REGS is None:
        path = os.path.join(stream_env.repo_root(), _REGMAP_REL)
        log = logging.getLogger("tally_regs")
        log.addHandler(logging.NullHandler())
        with contextlib.redirect_stdout(io.StringIO()):   # RegisterMap prints its map
            _REGS = RegisterMap(path, apb_data_width=32, apb_addr_width=32,
                                start_address=0, log=log)
    return _REGS


def _off(name: str) -> int:
    r = _regs()
    return r.reg_address(r.registers[name])


# The tally's ID/sizing word: {N_PROFILE[31:16], TALLY_ADDR_BITS[15:0]}. It is
# the block's self-description, published by monbus_tally_axil itself rather
# than an RDL register, so it has no regmap name to resolve.
SIZING_OFF = 0x08
BIN_STRIDE = 8


def cam_key(agent: int, proto: int, ptype: int, evc: int) -> int:
    """Legal-set key: {agent[15:0], proto[3:0], type[3:0], event[7:0]}."""
    return (((agent & 0xFFFF) << 16) | ((proto & 0xF) << 12)
            | ((ptype & 0xF) << 8) | (evc & 0xFF))


def program_cam(bridge, cfg_base: int, legal: Iterable[Sequence]) -> int:
    """CLEAR, then per entry {KEY, LOAD(valid|index)}. Entries are tuples whose
    first four fields are (agent, proto, ptype, evc); a label may follow.
    Returns the number of entries loaded."""
    clear, key, load = _off("CAM_CLEAR"), _off("CAM_KEY"), _off("CAM_LOAD")
    bridge.write(cfg_base + clear, 0)
    n = 0
    for i, t in enumerate(legal):
        bridge.write(cfg_base + key, cam_key(*t[:4]))
        bridge.write(cfg_base + load, (1 << 31) | i)
        n += 1
    return n


def depth(bridge, cfg_base: int, fallback: int) -> int:
    """CAM depth as BUILT (== the UNEXPECTED bin index). `fallback` when the
    sizing word reads 0 (a bitstream that predates it)."""
    sizing = bridge.read(cfg_base + SIZING_OFF) or 0
    hw = (sizing >> 16) & 0xFFFF
    return hw if hw else fallback


def check_capacity(bridge, cfg_base: int, legal: Sequence, fallback: int) -> int:
    """The CAM depth, or SystemExit when `legal` cannot fit the built CAM."""
    n = depth(bridge, cfg_base, fallback)
    if len(legal) > n:
        raise SystemExit(f"ABORT: {len(legal)} legal tuples exceed the {n}-entry "
                         f"tally CAM built into this bitstream")
    return n


def snapshot(bridge, rd_base: int, n_legal: int, unexpected: int) -> List[int]:
    """Every dense bin 0..n_legal-1 plus UNEXPECTED, as a list (for deltas)."""
    return [bridge.read(rd_base + b * BIN_STRIDE) or 0
            for b in list(range(n_legal)) + [unexpected]]


def sweep_dense(bridge, rd_base: int, n_legal: int, unexpected: int) -> Dict[int, int]:
    """Non-zero dense bins {bin: count}; UNEXPECTED keyed by its own index."""
    counts: Dict[int, int] = {}
    for b in list(range(n_legal)) + [unexpected]:
        v = bridge.read(rd_base + b * BIN_STRIDE) or 0
        if v:
            counts[b] = v
    return counts


def delta(before: List[int], after: List[int]) -> List[int]:
    return [max(0, a - b) for b, a in zip(before, after)]


def labels(legal: Sequence, unexpected: int) -> Dict[int, str]:
    out = {i: (t[4] if len(t) > 4 else f"bin{i}") for i, t in enumerate(legal)}
    out[unexpected] = "UNEXPECTED"
    return out


def format_counts(counts: Dict[int, int], lab: Dict[int, str]) -> str:
    return " ".join(f"{lab.get(b, b)}={c}" for b, c in sorted(counts.items())) or "(no packets)"


def windows(bridge_name: str = "mon") -> Tuple[Dict[str, int], Dict[str, int]]:
    """({tally: count base}, {tally: cfg base}) for the two tallies, by name."""
    from bridge_windows import W
    rd = {"stream": W("stream_tally", bridge_name)[0], "slave": W("slave_tally", bridge_name)[0]}
    cfg = {"stream": W("stream_tally_cfg", bridge_name)[0], "slave": W("slave_tally_cfg", bridge_name)[0]}
    return rd, cfg
