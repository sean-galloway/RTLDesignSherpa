import os

from .config import DeltaMeshConfig, header_width, validate_mesh


def generate_mesh(config: DeltaMeshConfig, output_dir: str) -> None:
    """Emit delta_mesh_cell.sv, the fabric top, and the filelist into output_dir."""
    from .cell import DeltaMeshCell, write_filelist
    from .fabric import validate_fabric, write_fabric

    validate_fabric(config)
    generator = DeltaMeshCell(config)
    generator.verilog(output_dir)
    cell_path = os.path.join(output_dir, 'delta_mesh_cell.sv')
    fabric_path = write_fabric(config, output_dir)
    filelist_path = write_filelist(config, output_dir)
    print(f"Generated mesh cell: {cell_path}")
    print(f"Generated mesh fabric: {fabric_path}")
    print(f"Generated mesh filelist: {filelist_path}")


__all__ = ["DeltaMeshConfig", "generate_mesh", "header_width", "validate_mesh"]
