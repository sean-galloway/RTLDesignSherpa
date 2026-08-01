# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Board registry -- the one place board facts live.

    from boards import get_board, list_boards
    b = get_board("nexys_a7_100t")     # or get_board() to honour $FPGA_BOARD

Adding a board is one file here plus one `register()` call; nothing else in the
tree should ever name a JTAG serial or an FPGA part again.
"""

from __future__ import annotations

import os
from typing import Dict, List, Optional, Type

from board import Board, BoardSpec

_REGISTRY: Dict[str, Type[Board]] = {}

# Boards that are really the same target under another name.
_ALIASES: Dict[str, str] = {
    "nexys": "nexys_a7_100t",
    "nexysa7": "nexys_a7_100t",
    "nexys_a7": "nexys_a7_100t",
    "genesys": "genesys2",
    "genesys_2": "genesys2",
}

DEFAULT_BOARD = "nexys_a7_100t"


def register(cls: Type[Board]) -> Type[Board]:
    """Class decorator adding a Board subclass to the registry."""
    _REGISTRY[cls.SPEC.name] = cls
    return cls


def list_boards() -> List[str]:
    _load_all()
    return sorted(_REGISTRY)


def get_board(name: Optional[str] = None) -> Board:
    """Instantiate a board by name.

    `name=None` takes `$FPGA_BOARD`, then the default. An unknown name raises
    with the valid list rather than falling back to a default -- silently
    programming the wrong board is far worse than a failed lookup.
    """
    _load_all()
    key = (name or os.environ.get("FPGA_BOARD") or DEFAULT_BOARD).strip().lower()
    key = _ALIASES.get(key, key)
    if key not in _REGISTRY:
        raise KeyError(
            f"unknown board {key!r}; known boards: {', '.join(sorted(_REGISTRY))}")
    return _REGISTRY[key]()


def _load_all() -> None:
    """Import every board module in this package so the registry is complete.

    Import-driven, so a new board file is picked up merely by existing -- there
    is no central list to forget to update.
    """
    import importlib
    import pkgutil
    for mod in pkgutil.iter_modules(__path__):
        if not mod.name.startswith("_"):
            importlib.import_module(f"{__name__}.{mod.name}")


__all__ = ["Board", "BoardSpec", "register", "get_board", "list_boards"]
