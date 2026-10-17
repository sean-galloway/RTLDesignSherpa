import math
from dataclasses import dataclass


@dataclass
class DeltaMeshConfig:
    """Configuration for a delta AXI-Stream mesh topology."""

    cells_x: int
    cells_y: int = 1
    cells_z: int = 1
    torus_x: bool = False
    torus_y: bool = False
    torus_z: bool = False
    source_route: bool = False
    speculation: bool = False
    fifo_impl: str = "reg"
    data_width: int = 64
    user_width: int = 1
    amba5: bool = False
    add_counters: bool = True
    ifc: str = "axis"


def header_width(cfg: DeltaMeshConfig) -> int:
    """Return the header width required by the mesh routing header.

    COORD_W = max(1, ceil(log2(max(cells_x, cells_y, cells_z))))
    header width = 6 * COORD_W + 32
    """
    coord_w = max(1, math.ceil(math.log2(max(cfg.cells_x, cfg.cells_y, cfg.cells_z))))
    return 6 * coord_w + 32


def validate_mesh(cfg: DeltaMeshConfig) -> None:
    """Validate a mesh configuration, raising ValueError on any violation."""
    for dim_name, dim_val, torus in (
        ("cells_x", cfg.cells_x, cfg.torus_x),
        ("cells_y", cfg.cells_y, cfg.torus_y),
        ("cells_z", cfg.cells_z, cfg.torus_z),
    ):
        if dim_val < 1:
            raise ValueError(f"{dim_name} must be >= 1")
        if torus and dim_val < 2:
            raise ValueError(f"torus on {dim_name} requires {dim_name} >= 2")

    if cfg.fifo_impl not in {"reg", "sram"}:
        raise ValueError(f"fifo-impl must be 'reg' or 'sram', got {cfg.fifo_impl!r}")

    if cfg.ifc not in {"axis", "cxs"}:
        raise ValueError(f"ifc must be 'axis' or 'cxs', got {cfg.ifc!r}")

    if cfg.fifo_impl == "sram":
        raise ValueError(
            "fifo-impl 'sram' is not supported in mesh mode: the mesh input "
            "buffers are shallow by design (FIFO_DEPTH=4) and always flop-"
            "implemented -- a 4-deep BRAM's registered-read skew buys nothing "
            "and hangs the drop FSM (issue #118, closed: rejected + flop-only "
            "by design). Use 'reg'.")

    if cfg.amba5:
        raise ValueError(
            "amba5 is not supported in mesh mode (flat mode only in v1; "
            "mesh ports carry no TWAKEUP/check sidebands)")

    if cfg.ifc == "cxs":
        # AMBA CXS multi-packet flits (CXSMAXPKTPERFLIT >= 2, required by the
        # house framers for TLAST framing) restrict CXSDATAWIDTH to 256/512/
        # 1024 (2048 also legal at Issue D) -- cxs_pkg::config_error rule 6.
        if cfg.data_width not in {256, 512, 1024, 2048}:
            raise ValueError(
                f"ifc 'cxs' requires --data-width 256/512/1024/2048 "
                f"(CXS multi-packet flits; cxs_pkg::config_error rule 6), "
                f"got {cfg.data_width}")

    min_user_width = header_width(cfg)
    if cfg.user_width < min_user_width:
        raise ValueError(f"user-width {cfg.user_width} is below header width {min_user_width}")
