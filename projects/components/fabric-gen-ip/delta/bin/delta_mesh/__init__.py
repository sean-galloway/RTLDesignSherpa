import os

from .config import DeltaMeshConfig, header_width, validate_mesh


def generate_mesh(config: DeltaMeshConfig, output_dir: str) -> None:
    """Emit delta_mesh_cell*.sv, fabric top, planes, and filelist into output_dir."""
    from .cell import DeltaMeshCell, write_cell_cxs, write_filelist
    from .fabric import validate_fabric, write_fabric, write_fabric_cxs
    from .plane import write_planes

    validate_fabric(config)

    # The AXIS core cell is always emitted; the CXS wrapper instantiates it.
    axis_generator = DeltaMeshCell(config)
    axis_generator.verilog(output_dir)
    cell_path = os.path.join(output_dir, 'delta_mesh_cell.sv')
    print(f"Generated mesh cell: {cell_path}")

    if config.ifc == "cxs":
        plane_paths = write_planes(output_dir, config.data_width,
                                   config.user_width)
        for p in plane_paths:
            print(f"Generated mesh plane: {p}")
        cxs_cell_path = write_cell_cxs(config, output_dir)
        print(f"Generated mesh CXS cell: {cxs_cell_path}")

    if config.ifc == "cxs":
        fabric_path = write_fabric_cxs(config, output_dir)
    else:
        fabric_path = write_fabric(config, output_dir)
    filelist_path = write_filelist(config, output_dir)
    print(f"Generated mesh fabric: {fabric_path}")
    print(f"Generated mesh filelist: {filelist_path}")


__all__ = ["DeltaMeshConfig", "generate_mesh", "header_width", "validate_mesh"]
